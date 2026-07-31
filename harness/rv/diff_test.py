#!/usr/bin/env python3
"""RV32IMC+M-mode differential harness: LeanModels.Rv.isaStep vs sail-riscv.

Oracle
------
The pinned **sail-riscv C emulator** (prebuilt release binary, version
0.13.1, github.com/riscv/sail-riscv, BSD-2-Clause) at::

    tools/rv-oracle/sail-riscv-Linux-x86_64/bin/sail_riscv_sim

run with ``--rv32 --config-override harness/rv/sail_rv32imc_override.json``,
which scopes it to exactly the model's fragment: ``rv32imc_zicsr_zifencei``,
machine mode only, priv v1.11, PMP absent, misaligned data access allowed.
Spike and QEMU were not needed: no riscv toolchain or emulator exists on
this host, but sail publishes Linux-x86_64 release binaries and this is the
preferred oracle anyway (SYNTHESIS: "Sail as validation oracle only").
``tools/ci.sh`` gates the harness on the binary's presence (absent on stock
runners; re-fetch with the URL in tools/rv-oracle/README).

Method
------
Every case is a self-contained flat program (built by the in-file RV32IMC
encoder, no external toolchain): a trap-handler block at the 256-aligned
``mtvec`` base, a prologue that normalizes mtvec/mie/mstatus, a register
preamble, the instruction(s) under test between compressed-nop landing pads
(so branch/jump targets — including 2-mod-4 misaligned ones — always reach
the postamble), a CSR-observation postamble (``csrr`` into x18..x24, so CSR
state is compared through the architecture itself), and an HTIF terminator.

The same bytes go to both sides: to sail as a handcrafted ELF (with the
``tohost`` symbol HTIF needs) and to ``harness/rv/isa_run.lean`` (one
``lake env lean --run`` batch) as JSON segments. Compared per case:

* the pc of every retired instruction (exceptions retire at the faulting
  pc; interrupt dispatch retires nothing — both sides agree on this),
* every value-changing GPR write, in order,
* every data-memory write ``(addr, width, value)``,
* the final 32-entry register file (plus the x0 = 0 kernel invariant),
* termination via the HTIF store pair.

Known WARL scope divergences (CV32E40P RTL choice vs sail's choice, both
legal; vectors below stay inside the agreeing subset, the CV32E40P-specific
behavior is pinned by ``#guard``s in LeanModels/Rv/Csr.lean and documented
in docs/rv-model.md):

* ``mie``: CV32E40P masks writes with IRQ_MASK = 0xFFFF0888 (fast irqs
  31:16); sail M-only keeps 0x888. Vectors use values ⊆ 0x888.
* ``mtvec``: CV32E40P keeps base[31:8] + mode bit 0 (reserved modes 10/11
  legalize to 00/01); sail keeps base[31:2] and *ignores* reserved-mode
  writes (keeps the old mode). Vectors use 256-aligned bases with mode
  ∈ {00, 01}, plus one mode-10 write from direct mode (both land 00).
* ``mcause``: CV32E40P narrows the WLRL code field to bits {31,4:0}; sail
  keeps all written bits. Vectors use values ⊆ 0x8000001F.
* Fast interrupts 16..31 and the CV32E40P priority cascade above MEI are
  not injectable in sail's platform (its mip has MEI/MTI/MSI only);
  MSI/MEI dispatch, vectoring and priority (MEI > MSI) are compared via
  sail's simple-interrupt-generator MMIO device.
* Bus/access faults do not exist in the model (CV32E40P's fault inputs are
  asserted away), so all data accesses stay inside sail RAM, and stores
  that wrap the 2^32 address-space edge are #guard-covered instead.

Usage:  python3 harness/rv/diff_test.py [--no-build] [--only PREFIX]
                                        [--sail BIN] [--keep DIR] [-v]
Exits non-zero on any divergence. Python 3.9 compatible.
"""

import argparse
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SAIL_DEFAULT = os.path.join(
    REPO_ROOT, "tools", "rv-oracle", "sail-riscv-Linux-x86_64", "bin", "sail_riscv_sim")
OVERRIDE = os.path.join(REPO_ROOT, "harness", "rv", "sail_rv32imc_override.json")
RUNNER = os.path.join(REPO_ROOT, "harness", "rv", "isa_run.lean")

# Memory map (sail --rv32 platform: RAM at 0x8000_0000, irqgen at 0xC00_0000).
HANDLER = 0x80000100          # 256-aligned mtvec base; 16 vector slots + body
BODY = HANDLER + 0x40
ENTRY = 0x80000200
TOHOST = 0x80001000
DATA = 0x80010000
IRQGEN = 0x0C000004           # the irq set/clear register (base + 4)

# ---------------------------------------------------------------------------
# RV32IMC encoders
# ---------------------------------------------------------------------------

def _r(op, f3, f7, rd, rs1, rs2):
    return (f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op

def _i(op, f3, rd, rs1, imm):
    return ((imm & 0xFFF) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op

def _s(op, f3, rs1, rs2, imm):
    imm &= 0xFFF
    return ((imm >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) \
        | ((imm & 0x1F) << 7) | op

def branch(f3, rs1, rs2, imm):
    imm &= 0x1FFF
    return (((imm >> 12) & 1) << 31) | (((imm >> 5) & 0x3F) << 25) | (rs2 << 20) \
        | (rs1 << 15) | (f3 << 12) | (((imm >> 1) & 0xF) << 8) \
        | (((imm >> 11) & 1) << 7) | 0x63

def lui(rd, imm20):
    return ((imm20 & 0xFFFFF) << 12) | (rd << 7) | 0x37

def auipc(rd, imm20):
    return ((imm20 & 0xFFFFF) << 12) | (rd << 7) | 0x17

def jal(rd, imm):
    imm &= 0x1FFFFF
    return (((imm >> 20) & 1) << 31) | (((imm >> 1) & 0x3FF) << 21) \
        | (((imm >> 11) & 1) << 20) | (((imm >> 12) & 0xFF) << 12) | (rd << 7) | 0x6F

def jalr(rd, rs1, imm, f3=0):
    return _i(0x67, f3, rd, rs1, imm)

def op_r(f3, f7, rd, rs1, rs2):
    return _r(0x33, f3, f7, rd, rs1, rs2)

def op_i(f3, rd, rs1, imm):
    return _i(0x13, f3, rd, rs1, imm)

def addi(rd, rs1, v):
    return op_i(0, rd, rs1, v)

def load(f3, rd, rs1, imm):
    return _i(0x03, f3, rd, rs1, imm)

def store(f3, rs1, rs2, imm):
    return _s(0x23, f3, rs1, rs2, imm)

def csr_op(f3, rd, csr, rs1_or_z):
    return _i(0x73, f3, rd, rs1_or_z, csr)

def csrrw(rd, csr, rs1):
    return csr_op(1, rd, csr, rs1)

def csrrs(rd, csr, rs1):
    return csr_op(2, rd, csr, rs1)

def csrrc(rd, csr, rs1):
    return csr_op(3, rd, csr, rs1)

def csrrwi(rd, csr, z):
    return csr_op(5, rd, csr, z)

def csrrsi(rd, csr, z):
    return csr_op(6, rd, csr, z)

def csrrci(rd, csr, z):
    return csr_op(7, rd, csr, z)

def csrr(rd, csr):
    return csrrs(rd, csr, 0)

def li32(rd, v):
    """Load a 32-bit constant: always exactly lui + addi (fixed layout)."""
    v &= 0xFFFFFFFF
    lo = v & 0xFFF
    if lo >= 0x800:
        lo -= 0x1000
    hi = ((v - lo) >> 12) & 0xFFFFF
    return [lui(rd, hi), addi(rd, rd, lo)]

ECALL = 0x00000073
EBREAK = 0x00100073
MRET = 0x30200073
WFI = 0x10500073
FENCE = 0x0FF0000F
FENCE_I = 0x0000100F
NOP = addi(0, 0, 0)
C_NOP = 0x0001
C_EBREAK = 0x9002

def _c3(r):
    assert 8 <= r <= 15
    return r - 8

def c_addi(rd, imm):
    imm &= 0x3F
    return (0 << 13) | ((imm >> 5) << 12) | (rd << 7) | ((imm & 0x1F) << 2) | 0b01

def c_li(rd, imm):
    imm &= 0x3F
    return (0b010 << 13) | ((imm >> 5) << 12) | (rd << 7) | ((imm & 0x1F) << 2) | 0b01

def c_lui(rd, imm6):
    imm6 &= 0x3F
    return (0b011 << 13) | ((imm6 >> 5) << 12) | (rd << 7) | ((imm6 & 0x1F) << 2) | 0b01

def c_addi16sp(imm):
    v = imm & 0x3FF
    return (0b011 << 13) | (((v >> 9) & 1) << 12) | (2 << 7) | (((v >> 4) & 1) << 6) \
        | (((v >> 6) & 1) << 5) | (((v >> 7) & 3) << 3) | (((v >> 5) & 1) << 2) | 0b01

def c_addi4spn(rd, imm):
    v = imm & 0x3FF
    return (0b000 << 13) | (((v >> 4) & 3) << 11) | (((v >> 6) & 0xF) << 7) \
        | (((v >> 2) & 1) << 6) | (((v >> 3) & 1) << 5) | (_c3(rd) << 2) | 0b00

def c_lw(rd, rs1, imm):
    v = imm & 0x7F
    return (0b010 << 13) | (((v >> 3) & 7) << 10) | (_c3(rs1) << 7) \
        | (((v >> 2) & 1) << 6) | (((v >> 6) & 1) << 5) | (_c3(rd) << 2) | 0b00

def c_sw(rs2, rs1, imm):
    v = imm & 0x7F
    return (0b110 << 13) | (((v >> 3) & 7) << 10) | (_c3(rs1) << 7) \
        | (((v >> 2) & 1) << 6) | (((v >> 6) & 1) << 5) | (_c3(rs2) << 2) | 0b00

def c_srli(rd, sh):
    return (0b100 << 13) | (((sh >> 5) & 1) << 12) | (0b00 << 10) | (_c3(rd) << 7) \
        | ((sh & 0x1F) << 2) | 0b01

def c_srai(rd, sh):
    return (0b100 << 13) | (((sh >> 5) & 1) << 12) | (0b01 << 10) | (_c3(rd) << 7) \
        | ((sh & 0x1F) << 2) | 0b01

def c_andi(rd, imm):
    imm &= 0x3F
    return (0b100 << 13) | ((imm >> 5) << 12) | (0b10 << 10) | (_c3(rd) << 7) \
        | ((imm & 0x1F) << 2) | 0b01

def _c_arith(funct2, rd, rs2):
    return (0b100 << 13) | (0 << 12) | (0b11 << 10) | (_c3(rd) << 7) \
        | (funct2 << 5) | (_c3(rs2) << 2) | 0b01

def c_sub(rd, rs2):
    return _c_arith(0b00, rd, rs2)

def c_xor(rd, rs2):
    return _c_arith(0b01, rd, rs2)

def c_or(rd, rs2):
    return _c_arith(0b10, rd, rs2)

def c_and(rd, rs2):
    return _c_arith(0b11, rd, rs2)

def _c_j_imm(imm):
    v = imm & 0xFFF
    return (((v >> 11) & 1) << 12) | (((v >> 4) & 1) << 11) | (((v >> 8) & 3) << 9) \
        | (((v >> 10) & 1) << 8) | (((v >> 6) & 1) << 7) | (((v >> 7) & 1) << 6) \
        | (((v >> 1) & 7) << 3) | (((v >> 5) & 1) << 2)

def c_j(imm):
    return (0b101 << 13) | _c_j_imm(imm) | 0b01

def c_jal(imm):
    return (0b001 << 13) | _c_j_imm(imm) | 0b01

def _c_b(f3, rs1, imm):
    v = imm & 0x1FF
    return (f3 << 13) | (((v >> 8) & 1) << 12) | (((v >> 3) & 3) << 10) \
        | (_c3(rs1) << 7) | (((v >> 6) & 3) << 5) | (((v >> 1) & 3) << 3) \
        | (((v >> 5) & 1) << 2) | 0b01

def c_beqz(rs1, imm):
    return _c_b(0b110, rs1, imm)

def c_bnez(rs1, imm):
    return _c_b(0b111, rs1, imm)

def c_slli(rd, sh):
    return (0b000 << 13) | (((sh >> 5) & 1) << 12) | (rd << 7) | ((sh & 0x1F) << 2) | 0b10

def c_lwsp(rd, imm):
    v = imm & 0xFF
    return (0b010 << 13) | (((v >> 5) & 1) << 12) | (rd << 7) | (((v >> 2) & 7) << 4) \
        | (((v >> 6) & 3) << 2) | 0b10

def c_swsp(rs2, imm):
    v = imm & 0xFF
    return (0b110 << 13) | (((v >> 2) & 0xF) << 9) | (((v >> 6) & 3) << 7) \
        | (rs2 << 2) | 0b10

def c_jr(rs1):
    return (0b100 << 13) | (0 << 12) | (rs1 << 7) | 0b10

def c_jalr(rs1):
    return (0b100 << 13) | (1 << 12) | (rs1 << 7) | 0b10

def c_mv(rd, rs2):
    return (0b100 << 13) | (0 << 12) | (rd << 7) | (rs2 << 2) | 0b10

def c_add(rd, rs2):
    return (0b100 << 13) | (1 << 12) | (rd << 7) | (rs2 << 2) | 0b10

# ---------------------------------------------------------------------------
# Two-pass assembler: items are ('w', v), ('h', v), ('label', name);
# v may be a callable (addr, labels) -> int for label-relative encodings.
# ---------------------------------------------------------------------------

def W(v):
    return ('w', v)

def H(v):
    return ('h', v)

def L(name):
    return ('label', name)

def jal_to(rd, label):
    return W(lambda a, ls: jal(rd, ls[label] - a))

def branch_to(f3, rs1, rs2, label):
    return W(lambda a, ls: branch(f3, rs1, rs2, ls[label] - a))

def li32_label(rd, label, add=0):
    hi = W(lambda a, ls: li32(rd, ls[label] + add)[0])
    lo = W(lambda a, ls: li32(rd, ls[label] + add)[1])
    return [hi, lo]

def assemble(items, base):
    labels = {}
    addr = base
    for it in items:
        if it[0] == 'label':
            labels[it[1]] = addr
        else:
            addr += 2 if it[0] == 'h' else 4
    out = b""
    addr = base
    for it in items:
        if it[0] == 'label':
            continue
        v = it[1](addr, labels) if callable(it[1]) else it[1]
        if it[0] == 'h':
            out += struct.pack("<H", v & 0xFFFF)
            addr += 2
        else:
            out += struct.pack("<I", v & 0xFFFFFFFF)
            addr += 4
    return out, labels

# ---------------------------------------------------------------------------
# ELF writer (minimal ELF32 EXEC with a symtab carrying the tohost symbol)
# ---------------------------------------------------------------------------

def make_elf(segments, entry, symbols):
    ehsize, phentsize, shentsize = 52, 32, 40
    nph = len(segments)
    off = ehsize + nph * phentsize
    seg_offs = []
    blob = b""
    for _va, data in segments:
        blob += b"\0" * ((-(off + len(blob))) % 4)
        seg_offs.append(off + len(blob))
        blob += data
    strtab = b"\0"
    name_off = {}
    for name in symbols:
        name_off[name] = len(strtab)
        strtab += name.encode() + b"\0"
    blob += b"\0" * ((-(off + len(blob))) % 4)
    strtab_off = off + len(blob)
    blob += strtab
    blob += b"\0" * ((-(off + len(blob))) % 4)
    symtab_off = off + len(blob)
    symtab = struct.pack("<IIIBBH", 0, 0, 0, 0, 0, 0)
    for name, addr in symbols.items():
        symtab += struct.pack("<IIIBBH", name_off[name], addr, 4, (1 << 4) | 1, 0, 0xFFF1)
    blob += symtab
    shstrtab = b"\0.symtab\0.strtab\0.shstrtab\0"
    shstrtab_off = off + len(blob)
    blob += shstrtab
    blob += b"\0" * ((-(off + len(blob))) % 4)
    shoff = off + len(blob)
    shdrs = struct.pack("<10I", *([0] * 10))
    shdrs += struct.pack("<10I", 1, 2, 0, 0, symtab_off, len(symtab), 2, 1, 4, 16)
    shdrs += struct.pack("<10I", 9, 3, 0, 0, strtab_off, len(strtab), 0, 0, 1, 0)
    shdrs += struct.pack("<10I", 17, 3, 0, 0, shstrtab_off, len(shstrtab), 0, 0, 1, 0)
    ident = b"\x7fELF" + bytes([1, 1, 1, 0]) + b"\0" * 8
    ehdr = ident + struct.pack("<HHIIIIIHHHHHH",
                               2, 243, 1, entry, ehsize, shoff, 0,
                               ehsize, phentsize, nph, shentsize, 4, 3)
    phdrs = b""
    for (va, data), foff in zip(segments, seg_offs):
        phdrs += struct.pack("<8I", 1, foff, va, va, len(data), len(data), 7, 4)
    return ehdr + phdrs + b"\0" * (off - ehsize - len(phdrs)) + blob + shdrs

# ---------------------------------------------------------------------------
# Program builder
# ---------------------------------------------------------------------------

def build_case(name, test, pre=(), pads=0, flavor='exc', mode=1, mie=None,
               set_mie=False, inject=None, clear=0x808, maxsteps=300):
    """Build one case's two memory segments (handler + entry program).

    test:    list of assembler items — the instruction(s) under test.
    pre:     [(reg, value)] register preamble (regs 0..17 only).
    pads:    bytes of c.nop landing pad before/after the test (0 = none).
    flavor:  'exc' — trap handler captures mepc/mcause/mstatus into x28..x30
             and mrets to the postamble; 'irq' — captures, clears the irqgen
             lines in `clear`, and mrets to mepc.
    mode:    mtvec mode written by the prologue (0 direct / 1 vectored).
    mie:     value written to mie (None = leave at reset 0).
    set_mie: set mstatus.MIE (via csrrsi) after the preamble.
    inject:  irqgen line mask to set right before the test (MSI=0x8, MEI=0x800).
    """
    # handler: 16 vectored slots, all jumping to the body
    h = []
    for i in range(16):
        h.append(jal_to(0, 'body'))
    h.append(L('body'))
    h += [W(csrr(28, 0x341)), W(csrr(29, 0x342)), W(csrr(30, 0x300))]
    if flavor == 'irq':
        h += li32(27, clear)
        h += [W(store(2, 26, 27, 0))]        # sw x27, 0(x26): clear irq lines
        h += [W(MRET)]
    else:
        h += li32_label(27, 'after')
        h += [W(csrrw(0, 0x341, 27)), W(MRET)]
    handler_items = [W(x) if isinstance(x, int) else x for x in h]

    e = []
    e += [W(x) for x in li32(25, TOHOST)]
    e += [W(x) for x in li32(26, IRQGEN)]
    e += [W(x) for x in li32(5, HANDLER | mode)]
    e += [W(csrrw(0, 0x305, 5))]
    # Normalize mstatus: sail resets it to 0x0 (MPP = 00) where the model —
    # like the CV32E40P RTL — resets to 0x1800 (MPP reads M). v1.11 leaves
    # the reset MPP unspecified; a write forces MPP = M on both sides.
    e += [W(csrrwi(0, 0x300, 0))]
    if mie is not None:
        e += [W(x) for x in li32(5, mie)]
        e += [W(csrrw(0, 0x304, 5))]
    for reg, val in pre:
        assert 0 <= reg <= 17, "preamble regs must stay below the reserved set"
        e += [W(x) for x in li32(reg, val)]
    if set_mie:
        e += [W(csrrsi(0, 0x300, 8))]
    if inject is not None:
        e += [W(x) for x in li32(5, 0x80000000 | inject)]
        e += [W(store(2, 26, 5, 0))]         # sw x5, 0(x26): set irq lines
    if pads:
        e += [jal_to(0, 'test')]
        e += [H(C_NOP)] * (pads // 2)
        e += [jal_to(0, 'after')]
    e += [L('test')]
    e += list(test)
    if pads:
        e += [H(C_NOP)] * (pads // 2)
    e += [L('after')]
    e += [W(csrr(18, 0x305)), W(csrr(19, 0x304)), W(csrr(21, 0x300)),
          W(csrr(22, 0x341)), W(csrr(23, 0x342)), W(csrr(24, 0x340))]
    e += [W(addi(27, 0, 1)), W(store(2, 25, 27, 0)), W(store(2, 25, 0, 4)),
          W(jal(0, 0))]

    # entry labels may be referenced by the handler ('after'): assemble the
    # entry first, then feed its labels into the handler's assembly pass.
    ebytes, elabels = assemble(e, ENTRY)
    hbytes, _ = assemble(
        [(k, (lambda f: (lambda a, ls: f(a, dict(ls, **elabels))))(v) if callable(v) else v)
         if k != 'label' else (k, v) for (k, v) in handler_items], HANDLER)
    return {
        "name": name,
        "segments": [(HANDLER, hbytes), (ENTRY, ebytes)],
        "maxsteps": maxsteps,
    }

# ---------------------------------------------------------------------------
# Case generators
# ---------------------------------------------------------------------------

import random

def gen_cases(seed):
    rng = random.Random(seed)
    cases = []

    def add(name, test, **kw):
        cases.append(build_case(name, test, **kw))

    def rnd32():
        return rng.getrandbits(32)

    # --- alu R-type -------------------------------------------------------
    r_ops = [("add", 0, 0x00), ("sub", 0, 0x20), ("sll", 1, 0x00),
             ("slt", 2, 0x00), ("sltu", 3, 0x00), ("xor", 4, 0x00),
             ("srl", 5, 0x00), ("sra", 5, 0x20), ("or", 6, 0x00), ("and", 7, 0x00)]
    corners = [(0xFFFFFFFF, 1), (0x80000000, 31), (0x80000000, 0xFFFFFFFF),
               (0, 0xFFFFFFFF), (1, 32), (0x7FFFFFFF, 1)]
    for nm, f3, f7 in r_ops:
        for k in range(2):
            a, b = rnd32(), rnd32()
            add("alu_r_%s_rand%d" % (nm, k), [W(op_r(f3, f7, 6, 7, 8))],
                pre=[(7, a), (8, b)])
        a, b = corners[hash(nm) % len(corners)]
        add("alu_r_%s_corner" % nm, [W(op_r(f3, f7, 6, 7, 8))], pre=[(7, a), (8, b)])
    # rd == rs1 and operands aliased
    add("alu_r_add_rd_eq_rs1", [W(op_r(0, 0, 7, 7, 8))], pre=[(7, 5), (8, 9)])
    add("alu_r_sub_aliased", [W(op_r(0, 0x20, 6, 7, 7))], pre=[(7, 12345)])

    # --- alu I-type -------------------------------------------------------
    i_ops = [("addi", 0), ("slti", 2), ("sltiu", 3), ("xori", 4), ("ori", 6), ("andi", 7)]
    for nm, f3 in i_ops:
        for k, imm in enumerate([rng.randint(-2048, 2047), -2048, 2047]):
            add("alu_i_%s_%d" % (nm, k), [W(op_i(f3, 6, 7, imm))], pre=[(7, rnd32())])
    for nm, f7 in [("slli", 0x00), ("srli", 0x00), ("srai", 0x20)]:
        f3 = 1 if nm == "slli" else 5
        for sh in [0, 1, 31]:
            add("alu_i_%s_sh%d" % (nm, sh), [W(op_i(f3, 6, 7, (f7 << 5) | sh))],
                pre=[(7, 0x80000001)])
    add("alu_i_lui", [W(lui(6, 0xDEADB))])
    add("alu_i_lui_allones", [W(lui(6, 0xFFFFF))])
    add("alu_i_auipc", [W(auipc(6, 0x12345))])
    add("alu_i_auipc_neg", [W(auipc(6, 0xFFFFF))])

    # --- mulDiv -----------------------------------------------------------
    m_ops = [("mul", 0), ("mulh", 1), ("mulhsu", 2), ("mulhu", 3),
             ("div", 4), ("divu", 5), ("rem", 6), ("remu", 7)]
    for nm, f3 in m_ops:
        for k in range(2):
            add("muldiv_%s_rand%d" % (nm, k), [W(op_r(f3, 1, 6, 7, 8))],
                pre=[(7, rnd32()), (8, rnd32())])
    quirks = [
        ("div_by0", 4, 10, 0), ("divu_by0", 5, 10, 0),
        ("rem_by0", 6, 10, 0), ("remu_by0", 7, 10, 0),
        ("div_ovf", 4, 0x80000000, 0xFFFFFFFF), ("rem_ovf", 6, 0x80000000, 0xFFFFFFFF),
        ("divu_minneg", 5, 0x80000000, 0xFFFFFFFF), ("remu_minneg", 7, 0x80000000, 0xFFFFFFFF),
        ("div_n7_2", 4, 0xFFFFFFF9, 2), ("rem_n7_2", 6, 0xFFFFFFF9, 2),
        ("div_7_n2", 4, 7, 0xFFFFFFFE), ("rem_7_n2", 6, 7, 0xFFFFFFFE),
        ("mulh_allones", 1, 0xFFFFFFFF, 0xFFFFFFFF),
        ("mulhsu_allones", 2, 0xFFFFFFFF, 0xFFFFFFFF),
        ("mulhu_allones", 3, 0xFFFFFFFF, 0xFFFFFFFF),
        ("mulh_minmin", 1, 0x80000000, 0x80000000),
    ]
    for nm, f3, a, b in quirks:
        add("muldiv_%s" % nm, [W(op_r(f3, 1, 6, 7, 8))], pre=[(7, a), (8, b)])

    # --- branches ---------------------------------------------------------
    b_ops = [("beq", 0, 5, 5, 5, 7), ("bne", 1, 5, 7, 5, 5),
             ("blt", 4, 0xFFFFFFFF, 0, 0, 0xFFFFFFFF),
             ("bge", 5, 0, 0xFFFFFFFF, 0xFFFFFFFF, 0),
             ("bltu", 6, 0, 0xFFFFFFFF, 0xFFFFFFFF, 0),
             ("bgeu", 7, 0xFFFFFFFF, 0, 0, 0xFFFFFFFF)]
    for nm, f3, ta, tb, na, nb in b_ops:
        for off in [-48, 20]:
            add("branch_%s_taken_%s" % (nm, "neg" if off < 0 else "pos"),
                [W(branch(f3, 7, 8, off))], pre=[(7, ta), (8, tb)], pads=52)
        add("branch_%s_nottaken" % nm, [W(branch(f3, 7, 8, -20))],
            pre=[(7, na), (8, nb)], pads=52)
    # misaligned (2 mod 4) targets land on c.nops in the pad
    add("branch_beq_misaligned_pos", [W(branch(0, 7, 8, 22))], pre=[(7, 3), (8, 3)], pads=52)
    add("branch_bne_misaligned_neg", [W(branch(1, 7, 8, -46))], pre=[(7, 3), (8, 4)], pads=52)
    # target inside the branch's own second halfword: both sides fetch the
    # same garbage parcel (here it decodes as a load, so every register is
    # pointed into RAM first — bus faults don't exist in the model)
    add("branch_beq_into_self", [W(branch(0, 7, 8, 2))],
        pre=[(r, DATA + 0x200 + 8 * r) for r in range(1, 7)] + [(7, 1), (8, 1)]
            + [(r, DATA + 0x200 + 8 * r) for r in range(9, 18)],
        pads=52)

    # --- jumps ------------------------------------------------------------
    add("jump_jal_pos", [W(jal(1, 24))], pads=52)
    add("jump_jal_neg", [W(jal(1, -40))], pads=52)
    add("jump_jal_x0", [W(jal(0, 16))], pads=52)
    add("jump_jal_misaligned", [W(jal(1, 18))], pads=52)
    add("jump_jalr", [li32_label(9, 'after')[0], li32_label(9, 'after')[1],
                      W(jalr(1, 9, 0))])
    add("jump_jalr_negimm", [li32_label(9, 'after', add=16)[0],
                             li32_label(9, 'after', add=16)[1], W(jalr(1, 9, -16))])
    add("jump_jalr_oddtarget", [li32_label(9, 'after', add=1)[0],
                                li32_label(9, 'after', add=1)[1], W(jalr(1, 9, 0))])
    add("jump_jalr_rd_eq_rs1", [li32_label(9, 'after')[0], li32_label(9, 'after')[1],
                                W(jalr(9, 9, 0))])

    # --- memory -----------------------------------------------------------
    def mempre(v=0x8899AABB):
        return [(10, DATA), (11, v)]
    add("mem_sw_aligned", [W(store(2, 10, 11, 0x40))], pre=mempre())
    add("mem_sw_mis1", [W(store(2, 10, 11, 0x41))], pre=mempre())
    add("mem_sw_mis2", [W(store(2, 10, 11, 0x42))], pre=mempre())
    add("mem_sw_mis3", [W(store(2, 10, 11, 0x43))], pre=mempre())
    add("mem_sh_aligned", [W(store(1, 10, 11, 0x40))], pre=mempre())
    add("mem_sh_mis", [W(store(1, 10, 11, 0x45))], pre=mempre())
    add("mem_sb", [W(store(0, 10, 11, 0x47))], pre=mempre())
    add("mem_sw_negimm", [W(store(2, 10, 11, -4))], pre=[(10, DATA + 0x80), (11, 0x11223344)])
    # store-then-load round trips (sign/zero extension corners)
    add("mem_lw_aligned", [W(store(2, 10, 11, 0x40)), W(load(2, 6, 10, 0x40))], pre=mempre())
    add("mem_lw_mis", [W(store(2, 10, 11, 0x40)), W(store(2, 10, 11, 0x44)),
                       W(load(2, 6, 10, 0x41))], pre=mempre(0xDEADBEEF))
    add("mem_lb_signed", [W(store(0, 10, 11, 0x40)), W(load(0, 6, 10, 0x40))],
        pre=mempre(0x80))
    add("mem_lbu", [W(store(0, 10, 11, 0x40)), W(load(4, 6, 10, 0x40))], pre=mempre(0x80))
    add("mem_lh_signed", [W(store(1, 10, 11, 0x40)), W(load(1, 6, 10, 0x40))],
        pre=mempre(0x8000))
    add("mem_lhu", [W(store(1, 10, 11, 0x40)), W(load(5, 6, 10, 0x40))], pre=mempre(0x8000))
    add("mem_lh_mis", [W(store(2, 10, 11, 0x40)), W(load(1, 6, 10, 0x41))],
        pre=mempre(0x00AB7F80))
    add("mem_lw_x0", [W(store(2, 10, 11, 0x40)), W(load(2, 0, 10, 0x40))], pre=mempre())

    # --- RVC --------------------------------------------------------------
    add("rvc_c_addi", [H(c_addi(9, -1))], pre=[(9, 5)])
    add("rvc_c_li", [H(c_li(9, 0x15))])
    add("rvc_c_li_neg", [H(c_li(9, -32 & 0x3F))])
    add("rvc_c_lui", [H(c_lui(9, 0x21))], pre=[(9, 1)])
    add("rvc_c_addi16sp", [H(c_addi16sp(-512 & 0x3FF))], pre=[(2, 0x800)])
    add("rvc_c_addi4spn", [H(c_addi4spn(8, 4))], pre=[(2, 0x100)])
    add("rvc_c_lw", [W(store(2, 8, 11, 0x44)), H(c_lw(9, 8, 0x44))],
        pre=[(8, DATA), (11, 0xCAFEBABE)])
    add("rvc_c_sw", [H(c_sw(11, 8, 0x48))], pre=[(8, DATA), (11, 0x13579BDF)])
    add("rvc_c_srli", [H(c_srli(8, 5))], pre=[(8, 0x80000000)])
    add("rvc_c_srai", [H(c_srai(8, 5))], pre=[(8, 0x80000000)])
    add("rvc_c_andi", [H(c_andi(8, 0x11))], pre=[(8, 0xFF)])
    add("rvc_c_sub", [H(c_sub(8, 9))], pre=[(8, 5), (9, 7)])
    add("rvc_c_xor", [H(c_xor(8, 9))], pre=[(8, 0xF0F0), (9, 0xFFFF)])
    add("rvc_c_or", [H(c_or(8, 9))], pre=[(8, 0xF0F0), (9, 0x0F0F)])
    add("rvc_c_and", [H(c_and(8, 9))], pre=[(8, 0xFF00), (9, 0x0FF0)])
    add("rvc_c_slli", [H(c_slli(9, 4))], pre=[(9, 0x1234)])
    add("rvc_c_lwsp", [W(store(2, 2, 11, 0x14)), H(c_lwsp(9, 0x14))],
        pre=[(2, DATA + 0x40), (11, 0x0BADF00D)])
    add("rvc_c_swsp", [H(c_swsp(11, 0x18))], pre=[(2, DATA + 0x40), (11, 0x600DF00D)])
    add("rvc_c_mv", [H(c_mv(9, 8))], pre=[(8, 0x77)])
    add("rvc_c_add", [H(c_add(9, 8))], pre=[(8, 3), (9, 4)])
    add("rvc_c_nop", [H(C_NOP)])
    add("rvc_c_addi_x0_hint", [H(c_addi(0, 5))])
    add("rvc_c_j", [H(c_j(20))], pads=52)
    add("rvc_c_j_neg", [H(c_j(-30))], pads=52)
    add("rvc_c_jal", [H(c_jal(24))], pads=52)      # links pc+2: the ilen fix
    add("rvc_c_jal_neg", [H(c_jal(-26))], pads=52)
    add("rvc_c_beqz_taken", [H(c_beqz(8, -22))], pre=[(8, 0)], pads=52)
    add("rvc_c_beqz_nottaken", [H(c_beqz(8, 30))], pre=[(8, 1)], pads=52)
    add("rvc_c_bnez_taken", [H(c_bnez(8, 26))], pre=[(8, 0xFFFFFFFF)], pads=52)
    add("rvc_c_bnez_nottaken", [H(c_bnez(8, -18))], pre=[(8, 0)], pads=52)
    add("rvc_c_jr", [li32_label(9, 'after')[0], li32_label(9, 'after')[1], H(c_jr(9))])
    add("rvc_c_jalr", [li32_label(9, 'after')[0], li32_label(9, 'after')[1], H(c_jalr(9))])
    # known-illegal / reserved halfwords
    add("rvc_illegal_zero", [H(0x0000)])
    add("rvc_illegal_c_fld", [H(0x2000)])
    add("rvc_reserved_addi4spn0", [H(0x0008)])
    # random halfwords: every register points into RAM so any load/store/jump
    # stays comparable (no bus faults exist in the model). Quadrant-01
    # jumps/branches are excluded — an arbitrary backward c.j/c.bnez can
    # re-enter the prologue and loop forever; those forms have enumerated
    # cases above instead.
    ram_pre = [(r, DATA + 0x100 + 8 * r) for r in range(1, 18)]
    picked = 0
    while picked < 12:
        h = rng.getrandbits(16)
        if (h & 3) == 1 and ((h >> 13) & 7) in (1, 5, 6, 7):
            continue
        add("rvc_random_%04x" % h, [H(h)], pre=ram_pre, pads=52)
        picked += 1

    # --- system -----------------------------------------------------------
    add("sys_ecall", [W(ECALL)])
    add("sys_ebreak", [W(EBREAK)])
    add("sys_c_ebreak", [H(C_EBREAK)])
    add("sys_fence", [W(FENCE)])
    add("sys_fence_fields", [W(_i(0x0F, 0, 3, 4, 0x123))])
    add("sys_fence_i", [W(FENCE_I)])
    add("sys_fence_i_fields", [W(_i(0x0F, 1, 2, 3, 0x456))])
    add("sys_wfi_wake", [W(WFI)], mie=0x8, inject=0x8, flavor='irq')
    add("sys_mret_direct", [li32_label(9, 'after')[0], li32_label(9, 'after')[1],
                            W(csrrw(0, 0x341, 9)), W(MRET)])
    add("sys_sret_illegal", [W(0x10200073)])
    add("sys_uret_illegal", [W(0x00200073)])
    add("sys_dret_illegal", [W(0x7B200073)])
    add("sys_sfence_vma_illegal", [W(0x12000073)])

    # --- illegal 32-bit words --------------------------------------------
    illegal = [
        ("zero", 0x00000000),
        ("allones", 0xFFFFFFFF),
        ("branch_f3_010", branch(2, 1, 2, 8)),
        ("branch_f3_011", branch(3, 1, 2, 8)),
        ("store_f3_011", store(3, 10, 11, 0)),
        ("load_f3_011", load(3, 6, 10, 0)),
        ("load_f3_110", load(6, 6, 10, 0)),
        ("op_bad_f7", _r(0x33, 0, 0x40, 6, 7, 8)),
        ("op_bad_f7_2", _r(0x33, 0, 0x01 | 0x20, 6, 7, 8)),
        ("shift_bad_f7", op_i(1, 6, 7, (0x7F << 5) | 3)),
        ("jalr_f3_1", jalr(1, 9, 0, f3=1)),
        ("amoadd", 0x0000202F),
        ("flw", 0x00002007),
        ("fsw", 0x00002027),
        ("fadd", 0x00007053),
        ("csr_f3_100", csr_op(4, 6, 0x340, 7)),
        ("system_bits", 0x00000FF3),
    ]
    for nm, wv in illegal:
        add("illegal_%s" % nm, [W(wv)], pre=[(10, DATA), (11, 1)])

    # --- CSRs -------------------------------------------------------------
    add("csr_mscratch_rw", [W(csrrw(6, 0x340, 7))], pre=[(7, 0xCAFEBABE)])
    add("csr_mscratch_rw_rd_x0", [W(csrrw(0, 0x340, 7))], pre=[(7, 0x12341234)])
    add("csr_mscratch_rs", [W(csrrw(0, 0x340, 7)), W(csrrs(6, 0x340, 8))],
        pre=[(7, 0xF0F00000), (8, 0x0000FFFF)])
    add("csr_mscratch_rc", [W(csrrw(0, 0x340, 7)), W(csrrc(6, 0x340, 8))],
        pre=[(7, 0xFFFFFFFF), (8, 0x0F0F0F0F)])
    add("csr_mscratch_rs_x0_nowrite", [W(csrrw(0, 0x340, 7)), W(csrrs(6, 0x340, 0))],
        pre=[(7, 0x5A5A5A5A)])
    add("csr_mscratch_rwi", [W(csrrwi(6, 0x340, 31))])
    add("csr_mscratch_rsi", [W(csrrwi(0, 0x340, 16)), W(csrrsi(6, 0x340, 5))])
    add("csr_mscratch_rci", [W(csrrwi(0, 0x340, 31)), W(csrrci(6, 0x340, 21))])
    add("csr_mscratch_rsi_zero_nowrite", [W(csrrwi(0, 0x340, 9)), W(csrrsi(6, 0x340, 0))])
    add("csr_mscratch_rd_eq_rs", [W(csrrw(0, 0x340, 7)), W(csrrw(7, 0x340, 7))],
        pre=[(7, 0x77770001)])
    add("csr_mepc_write_odd", [W(csrrw(0, 0x341, 7)), W(csrr(6, 0x341))],
        pre=[(7, 0x80000235)])
    add("csr_mepc_write_allones", [W(csrrw(0, 0x341, 7)), W(csrr(6, 0x341))],
        pre=[(7, 0xFFFFFFFF)])
    add("csr_mstatus_write_allones", [W(csrrw(6, 0x300, 7)), W(csrr(8, 0x300))],
        pre=[(7, 0xFFFFFFFF)])
    add("csr_mstatus_write_zero", [W(csrrw(0, 0x300, 0)), W(csrr(6, 0x300))])
    add("csr_mstatus_set_mie_mpie", [W(csrrwi(0, 0x300, 8)), W(csrrsi(6, 0x300, 0)),
                                     W(csrrs(0, 0x300, 7)), W(csrr(8, 0x300))],
        pre=[(7, 0x80)])
    add("csr_mstatus_clear_mie", [W(csrrwi(0, 0x300, 8)), W(csrrci(6, 0x300, 8)),
                                  W(csrr(8, 0x300))])
    add("csr_mie_write_888", [W(csrrw(0, 0x304, 7)), W(csrr(6, 0x304))], pre=[(7, 0x888)])
    add("csr_mie_write_8", [W(csrrwi(0, 0x304, 8)), W(csrr(6, 0x304))])
    add("csr_mie_set_800", [W(csrrwi(0, 0x304, 8)), W(csrrs(6, 0x304, 7)), W(csrr(8, 0x304))],
        pre=[(7, 0x800)])
    add("csr_mie_clear", [W(csrrw(0, 0x304, 7)), W(csrrc(6, 0x304, 8)), W(csrr(9, 0x304))],
        pre=[(7, 0x888), (8, 0x88)])
    add("csr_mtvec_direct", [W(csrrw(6, 0x305, 7)), W(csrr(8, 0x305))],
        pre=[(7, HANDLER)], mode=1)
    add("csr_mtvec_vectored", [W(csrrw(6, 0x305, 7)), W(csrr(8, 0x305))],
        pre=[(7, 0x80004500 | 1)], mode=0)
    add("csr_mtvec_mode10_from_direct", [W(csrrw(0, 0x305, 7)), W(csrr(6, 0x305))],
        pre=[(7, HANDLER | 2)], mode=0)
    add("csr_mcause_write", [W(csrrw(0, 0x342, 7)), W(csrr(6, 0x342))],
        pre=[(7, 0x8000000B)])
    add("csr_mcause_write_code", [W(csrrwi(0, 0x342, 0x1F)), W(csrr(6, 0x342))])
    add("csr_mcause_write_zero", [W(csrrw(0, 0x342, 0)), W(csrr(6, 0x342))])
    add("csr_reset_reads", [W(csrr(6, 0x300)), W(csrr(7, 0x304)), W(csrr(8, 0x341)),
                            W(csrr(9, 0x342)), W(csrr(10, 0x340))])
    add("csr_unimpl_7c0", [W(csrr(6, 0x7C0))])
    add("csr_unimpl_sscratch", [W(csrrw(6, 0x140, 7))], pre=[(7, 1)])

    # --- x0 discipline ----------------------------------------------------
    add("x0_addi", [W(addi(0, 0, 5))])
    add("x0_lui", [W(lui(0, 0x12345))])
    add("x0_c_li", [H(c_li(0, 7))])
    add("x0_c_mv", [H(c_mv(0, 8))], pre=[(8, 0xABCD)])

    # --- interrupts (via the simple interrupt generator) ------------------
    add("irq_msi_vectored", [W(NOP), W(NOP), W(NOP)],
        mie=0x8, set_mie=True, inject=0x8, flavor='irq', mode=1)
    add("irq_msi_direct", [W(NOP), W(NOP), W(NOP)],
        mie=0x8, set_mie=True, inject=0x8, flavor='irq', mode=0)
    add("irq_mei_vectored", [W(NOP), W(NOP), W(NOP)],
        mie=0x808, set_mie=True, inject=0x800, flavor='irq', mode=1)
    add("irq_mei_beats_msi", [W(NOP), W(NOP), W(NOP)],
        mie=0x808, set_mie=True, inject=0x808, flavor='irq', mode=1)
    add("irq_masked_by_mie", [W(NOP), W(NOP), W(NOP)],
        mie=0x800, set_mie=True, inject=0x8, flavor='irq', mode=1)
    add("irq_masked_by_mstatus", [W(NOP), W(NOP), W(NOP)],
        mie=0x8, set_mie=False, inject=0x8, flavor='irq', mode=1)
    add("irq_msi_mid_rvc", [H(c_addi(9, 1)), H(c_addi(9, 1)), H(c_addi(9, 1)),
                            W(NOP)],
        pre=[(9, 0)], mie=0x8, set_mie=True, inject=0x8, flavor='irq', mode=1)

    return [c for c in cases if c is not None]

# ---------------------------------------------------------------------------
# Sail runner + trace parser
# ---------------------------------------------------------------------------

HDR_RE = re.compile(r'^\[\d+\] \[M\]: 0x([0-9A-Fa-f]+) \(0x([0-9A-Fa-f]+)\)')
GPR_RE = re.compile(r'^x(\d+) <- 0x([0-9A-Fa-f]+)$')
MEMW_RE = re.compile(r'^mem\[W,0x([0-9A-Fa-f]+)\] <- 0x([0-9A-Fa-f]+)$')

def run_sail(sail, case, workdir, verbose):
    elf = make_elf(case["segments"], ENTRY,
                   {"tohost": TOHOST, "fromhost": TOHOST + 0x40})
    path = os.path.join(workdir, case["name"] + ".elf")
    with open(path, "wb") as f:
        f.write(elf)
    cmd = [sail, "--rv32", "--config-override", OVERRIDE,
           "--trace-instr", "--trace-gpr", "--trace-mem",
           "--inst-limit", str(case["maxsteps"]), path]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    pcs, gprs, mems = [], [], []
    regs = [0] * 32
    term = False
    for line in proc.stdout.splitlines():
        m = HDR_RE.match(line)
        if m:
            pcs.append(int(m.group(1), 16))
            continue
        m = GPR_RE.match(line)
        if m:
            r, v = int(m.group(1)), int(m.group(2), 16)
            if regs[r] != v:
                gprs.append([r, v])
                regs[r] = v
            continue
        m = MEMW_RE.match(line)
        if m:
            val_digits = len(m.group(2))
            mems.append([int(m.group(1), 16), val_digits // 2, int(m.group(2), 16)])
            continue
        if line.strip() == "SUCCESS":
            term = True
    return {"pcs": pcs, "gprs": gprs, "mems": mems, "regs": regs, "term": term,
            "exit": proc.returncode,
            "raw": proc.stdout if verbose else None,
            "stderr": proc.stderr}

# ---------------------------------------------------------------------------
# Lean runner driver
# ---------------------------------------------------------------------------

def run_lean(cases, workdir):
    payload = []
    for c in cases:
        payload.append({
            "name": c["name"],
            "entry": ENTRY,
            "tohost": TOHOST,
            "irqgen": IRQGEN,
            "maxSteps": c["maxsteps"],
            "segments": [{"base": base, "hex": data.hex()}
                         for base, data in c["segments"]],
        })
    path = os.path.join(workdir, "lean_cases.json")
    with open(path, "w") as f:
        json.dump(payload, f)
    proc = subprocess.run(["lake", "env", "lean", "--run", RUNNER, path],
                          capture_output=True, text=True, cwd=REPO_ROOT, timeout=3600)
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout + proc.stderr)
        raise RuntimeError("lean runner failed")
    out = {}
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        rec = json.loads(line)
        rec["gprs"] = [list(x) for x in rec["gprs"]]
        rec["mems"] = [list(x) for x in rec["mems"]]
        out[rec["name"]] = rec
    return out

# ---------------------------------------------------------------------------
# Comparison
# ---------------------------------------------------------------------------

def compare(case, sail_r, lean_r):
    problems = []
    if not sail_r["term"]:
        problems.append("sail did not reach HTIF termination (exit %d)" % sail_r["exit"])
    if not lean_r["term"]:
        problems.append("lean model did not reach termination (%d steps)" % lean_r["steps"])
    if sail_r["pcs"] != lean_r["pcs"]:
        for i, (a, b) in enumerate(zip(sail_r["pcs"], lean_r["pcs"])):
            if a != b:
                problems.append("pc[%d]: sail 0x%x vs lean 0x%x" % (i, a, b))
                break
        else:
            problems.append("pc trace length: sail %d vs lean %d"
                            % (len(sail_r["pcs"]), len(lean_r["pcs"])))
    if sail_r["gprs"] != lean_r["gprs"]:
        for i, (a, b) in enumerate(zip(sail_r["gprs"], lean_r["gprs"])):
            if a != b:
                problems.append("gpr write[%d]: sail x%d<-0x%x vs lean x%d<-0x%x"
                                % (i, a[0], a[1], b[0], b[1]))
                break
        else:
            problems.append("gpr write count: sail %d vs lean %d"
                            % (len(sail_r["gprs"]), len(lean_r["gprs"])))
    if sail_r["mems"] != lean_r["mems"]:
        problems.append("mem writes: sail %s vs lean %s" % (sail_r["mems"], lean_r["mems"]))
    if sail_r["regs"] != lean_r["regs"]:
        for r in range(32):
            if sail_r["regs"][r] != lean_r["regs"][r]:
                problems.append("final x%d: sail 0x%x vs lean 0x%x"
                                % (r, sail_r["regs"][r], lean_r["regs"][r]))
    if lean_r["regs"][0] != 0:
        problems.append("x0 kernel violated on the lean side: 0x%x" % lean_r["regs"][0])
    if sail_r["regs"][0] != 0:
        problems.append("x0 kernel violated on the sail side: 0x%x" % sail_r["regs"][0])
    return problems

# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true",
                    help="skip the up-front lake build (CI already ran it)")
    ap.add_argument("--only", default=None, help="run only cases with this name prefix")
    ap.add_argument("--sail", default=os.environ.get("RV_SAIL_SIM", SAIL_DEFAULT))
    ap.add_argument("--seed", type=int, default=0xC0FFEE)
    ap.add_argument("--keep", default=None, help="keep work artifacts in this directory")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    if not os.path.isfile(args.sail) or not os.access(args.sail, os.X_OK):
        print("rv-harness: sail oracle not present at %s" % args.sail)
        print("fetch: https://github.com/riscv/sail-riscv/releases/tag/0.13.1 "
              "(sail-riscv-Linux-x86_64.tar.gz, unpack under tools/rv-oracle/)")
        return 2

    if not args.no_build:
        r = subprocess.run(["lake", "build", "LeanModels"], cwd=REPO_ROOT)
        if r.returncode != 0:
            print("lake build failed")
            return 1

    cases = gen_cases(args.seed)
    if args.only:
        cases = [c for c in cases if c["name"].startswith(args.only)]
    if not cases:
        print("no cases selected")
        return 1

    workdir = args.keep or tempfile.mkdtemp(prefix="rv_diff_")
    if args.keep:
        os.makedirs(workdir, exist_ok=True)
    try:
        print("rv-harness: %d cases; oracle: sail-riscv (%s)" % (len(cases), args.sail))
        lean_out = run_lean(cases, workdir)
        n_pass = n_fail = 0
        failures = []
        for case in cases:
            sail_r = run_sail(args.sail, case, workdir, args.verbose)
            lean_r = lean_out.get(case["name"])
            if lean_r is None:
                failures.append((case["name"], ["missing lean output"]))
                n_fail += 1
                continue
            problems = compare(case, sail_r, lean_r)
            if problems:
                n_fail += 1
                failures.append((case["name"], problems))
                if args.verbose and sail_r["raw"]:
                    print("---- sail trace for %s ----" % case["name"])
                    print(sail_r["raw"])
            else:
                n_pass += 1
                if args.verbose:
                    print("PASS %-32s (%d retired)" % (case["name"], len(sail_r["pcs"])))
        print("rv-harness: %d PASS, %d FAIL" % (n_pass, n_fail))
        for name, problems in failures:
            print("FAIL %s" % name)
            for p in problems:
                print("     %s" % p)
        return 0 if n_fail == 0 else 1
    finally:
        if not args.keep:
            shutil.rmtree(workdir, ignore_errors=True)

if __name__ == "__main__":
    sys.exit(main())
