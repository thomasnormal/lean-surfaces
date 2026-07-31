import LeanModels.Rv.Priv

/-!
# The full architectural step: fetch parcel → decode → dispatch → execute

`isaStep` is the top of the model: one architectural step of the RV32IMC +
machine-mode hart, composing interrupt dispatch (`Priv.lean`), decode
(`Decode.lean`), CSR read-modify-write (`Csr.lean`), trap entry/return
(`Priv.lean`) and the non-privileged execution core (`Exec.lean`). The
instruction arrives as a `Fetched` parcel (the platform owns instruction
memory and the fetch path, exactly as it owns data memory), and the step
returns the next state plus `StepEffects` — the retirement-observable tuple
(pc target, data-memory access, system op, trap cause) that the RVFI-style
core-level refinement will consume.

Step order (each step handles at most one of these, top priority first):

1. **Interrupt dispatch** — before the fetched instruction executes
   (`mepc` = its pc), *except* when that instruction is a WFI: a WFI with a
   pending locally-enabled interrupt retires first and the interrupt is
   taken at the next step with `mepc` past the WFI — v1.11 §3.3's "resumes
   at the instruction following the WFI". Both behaviors are v1.11-legal
   for a *freshly reached* WFI; the rule makes the *stalled*-WFI case (the
   one v1.11 constrains) right.
2. **Illegal instruction** — decode failure (or, later, an unimplemented
   CSR address) traps with cause 2.
3. **System transfers** — ECALL (cause 11), EBREAK (cause 3), MRET, WFI,
   CSR ops.
4. **Everything else** — `execInstr` at the parcel's encoding length (so a
   compressed instruction retires at `pc + 2` and `c.jal` links `pc + 2`).

WFI is wait-until-interrupt: with no locally-enabled pending interrupt
(`pendingSet = 0`, the RTL's `irq_wu_ctrl_o` — **independent of
`mstatus.MIE`**, per v1.11 and per `cv32e40p_int_controller.sv` line 76) the
step is an architectural no-op at the same pc; once one pends, the WFI
retires to `pc + ilen`. CV32E40P's sleep unit is a timing refinement of
exactly this.

## Projection index (the spec-surface artifacts, all named defs)

The four tables + transfer fragments consumed by `docs/cv32e40p-spec-surface.md`:

| Projection | Def | Consumer spec |
|---|---|---|
| decode table | `decodeTable` (`Decode.lean`) | entry 7 `decoder_conforms`/`decoder_illegal` (`cv32e40p_decoder`); `expandC` for `cv32e40p_compressed_decoder` |
| ALU op table | `aluSem` (`Exec.lean`) | entry 5 `alu_conf_base` (`cv32e40p_alu`) |
| div/rem conventions | `divRem` (`Exec.lean`) | entry 6 `alu_div_tx` (`cv32e40p_alu_div`); `mulDivSem` for `cv32e40p_mult` |
| CSR behavior table | `csrTable` (`Csr.lean`) | entry 8 `csr_write_conforms` (`cv32e40p_cs_registers`) |
| trap-entry tuple | `trapEnter`/`mstatusOnTrap`/`mret` (`Priv.lean`) | entry 8 `csr_trap_entry_atomic`; entry 10 `controller_irq_boundary` |
| irq priority | `irqPriority`/`selectIrq` (`Priv.lean`) | entry 10 (`cv32e40p_int_controller` encoder) |

`isaStep` itself is the golden model for the eventual core-level `⊑`
refinement (spec-surface section B's closing argument).
-/

namespace LeanModels.Rv

/-! ## Fetch parcels -/

/-- One fetched instruction parcel, as the fetch interface delivers it: a
32-bit word (bits `[1:0] = 11`) or a compressed halfword. Whether the parcel
matches instruction memory at `s.pc` is the platform's obligation, not the
step's — the same boundary `Exec.lean` draws for data memory. -/
inductive Fetched where
  | word (w : BitVec 32)
  | half (h : BitVec 16)
  deriving DecidableEq, Repr

/-- Encoding length in bytes: what sequential retirement adds to the pc and
what `jump` links. -/
def Fetched.size : Fetched → BitVec 32
  | .word _ => 4
  | .half _ => 2

/-- Decode a parcel into the six semantic families (`decode` for words,
`expandC ∘ decode` for halfwords). `none` = illegal instruction. -/
def Fetched.decode : Fetched → Option Instr
  | .word w => Rv.decode w
  | .half h => decode16 h

/-! ## Step effects -/

/-- The per-step observable tuple: `Effects` (pc target, data-memory access,
system op) plus the trap cause if this step entered a trap. `pcTarget`
always equals the returned state's `pc` — including for traps (the handler
address) and a waiting WFI (the same pc). -/
structure StepEffects extends Effects where
  trap : Option Cause := none
  deriving DecidableEq, Repr

/-! ## CSR read-modify-write -/

/-- The CSR write-operand value: rs1 for the register forms, the 5-bit
zero-extended immediate for the `i` forms. -/
def csrOperand (s : ArchState) : CsrSrc → BitVec 32
  | .reg r => s.readReg r
  | .imm z => z.setWidth 32

/-- Is the write-operand *argument* the zero one (`rs1 = x0` / `uimm = 0`)?
The architectural no-write condition for CSRRS/CSRRC is about the argument,
not its value (unpriv spec §9.1) — for `x0` the two coincide only because
`x0` reads 0. -/
def CsrSrc.isZeroArg : CsrSrc → Bool
  | .reg r => r == 0
  | .imm z => z == 0

/-- Fold a CSR op against the old value (the RTL's `csr_wdata_int` mux). -/
def csrRmw (op : CsrOp) (old operand : BitVec 32) : BitVec 32 :=
  match op with
  | .rw => operand
  | .rs => old ||| operand
  | .rc => old &&& ~~~operand

/-- Does this CSR instruction perform a write? CSRRW always; CSRRS/CSRRC
unless the operand argument is `x0`/`0`. (Reads always happen — no CSR in
scope has read side effects.) -/
def csrWrites (op : CsrOp) (src : CsrSrc) : Bool :=
  op == .rw || !src.isZeroArg

/-! ## WFI wake -/

/-- WFI wake condition: some implemented interrupt pending *and* locally
enabled — `mstatus.MIE` does not participate (v1.11 §3.3; the RTL's
`irq_wu_ctrl_o = |(irq_i & mie_bypass_i)`). -/
def wfiWake (f : CsrFile) (irq : BitVec 32) : Bool :=
  pendingSet f irq != 0

/-! ## The step -/

/-- One architectural step: dispatch a pending interrupt or execute the
fetched parcel (see the module docstring for the priority order and the
WFI-first rule). `mem` is the data-memory view (loads read it; the produced
store is reported in `StepEffects.mem`, not applied — `isaStepMem` applies
it). `irq` is the level of the 32 interrupt lines during this step. -/
def isaStep (s : ArchState) (mem : Mem) (f : Fetched) (irq : BitVec 32 := 0) :
    ArchState × StepEffects :=
  let decoded := f.decode
  match takeInterrupt? s.csrs irq with
  | some id =>
    if decoded = some (.system .wfi) then
      -- WFI-first: retire the WFI now; the interrupt is taken at the next
      -- step, so the handler resumes *after* the WFI (v1.11 §3.3).
      let next := s.pc + f.size
      ({ s with pc := next }, { pcTarget := next, sys := some .wfi })
    else
      let s' := trapEnter s (.interrupt id)
      (s', { pcTarget := s'.pc, trap := some (.interrupt id) })
  | none =>
    match decoded with
    | none =>
      let s' := trapEnter s .illegalInstr
      (s', { pcTarget := s'.pc, trap := some .illegalInstr })
    | some (.system .ecall) =>
      let s' := trapEnter s .ecallM
      (s', { pcTarget := s'.pc, sys := some .ecall, trap := some .ecallM })
    | some (.system .ebreak) =>
      let s' := trapEnter s .breakpoint
      (s', { pcTarget := s'.pc, sys := some .ebreak, trap := some .breakpoint })
    | some (.system .mret) =>
      let s' := mret s
      (s', { pcTarget := s'.pc, sys := some .mret })
    | some (.system .wfi) =>
      if wfiWake s.csrs irq then
        let next := s.pc + f.size
        ({ s with pc := next }, { pcTarget := next, sys := some .wfi })
      else
        (s, { pcTarget := s.pc, sys := some .wfi })
    | some (.system (.csr op rd src addr)) =>
      match findCsr? addr with
      | none =>  -- unimplemented CSR address: illegal instruction
        let s' := trapEnter s .illegalInstr
        (s', { pcTarget := s'.pc, trap := some .illegalInstr })
      | some row =>
        let old := row.readView s.csrs
        let wv := csrRmw op old (csrOperand s src)
        let csrs' :=
          if csrWrites op src then row.write s.csrs (row.legalize old wv)
          else s.csrs
        let next := s.pc + f.size
        ({ s.writeReg rd old with pc := next, csrs := csrs' },
         { pcTarget := next, sys := some (.csr op rd src addr) })
    | some i =>  -- .alu/.mulDiv/.branch/.jump/.mem and the fences
      let (s', e) := execInstr i s mem f.size
      (s', { toEffects := e })

/-- Convenience driver: step state *and* memory together (stores land,
reads don't disturb) — the `execStep` of the full model. -/
def isaStepMem (s : ArchState) (m : Mem) (f : Fetched) (irq : BitVec 32 := 0) :
    ArchState × Mem :=
  let (s', e) := isaStep s m f irq
  (s', applyMemEffect m e.mem)

/-! ## `#guard` battery -/

private def mZ : Mem := fun _ => 0
/-- Vectored mtvec at 0x8000, global MIE on, all interrupts locally enabled. -/
private def csrsG : CsrFile :=
  { mtvec := 0x00008001, mstatus := mkMstatus true false, mie := irqMask }
private def sG : ArchState := { regs := fun _ => 0, pc := 0x1000, csrs := csrsG }
/-- Same but interrupts globally disabled. -/
private def sQ : ArchState :=
  { sG with csrs := { csrsG with mstatus := mkMstatus false false } }

/-! ### Exception entry through the step (ecall/ebreak/illegal/bad CSR) -/

#guard (isaStep sG mZ (.word 0x00000073)).1.pc = 0x00008000        -- ecall → base
#guard (isaStep sG mZ (.word 0x00000073)).1.csrs.mepc = 0x1000
#guard (isaStep sG mZ (.word 0x00000073)).1.csrs.mcause = 0x0000000B
#guard (isaStep sG mZ (.word 0x00000073)).2
        = { pcTarget := 0x00008000, sys := some .ecall, trap := some .ecallM }
#guard (isaStep sG mZ (.word 0x00100073)).1.csrs.mcause = 0x00000003 -- ebreak
#guard (isaStep sG mZ (.half 0x9002)).1.csrs.mcause = 0x00000003     -- c.ebreak
#guard (isaStep sG mZ (.word 0x00000000)).2.trap = some .illegalInstr
#guard (isaStep sG mZ (.word 0x00000000)).1.csrs.mcause = 0x00000002
#guard (isaStep sG mZ (.word 0x301312F3)).2.trap = some .illegalInstr -- csrrw to misa: out of scope ⇒ illegal
-- trap entry disables interrupts and stacks the old enable
#guard (isaStep sG mZ (.word 0x00000073)).1.csrs.mstatus = mkMstatus false true

/-! ### MRET through the step, and a full trap→mret round trip -/

private def sM : ArchState :=
  { regs := fun _ => 0, pc := 0x0100
    csrs := { mepc := 0x2000, mstatus := mkMstatus false true } }
#guard (isaStep sM mZ (.word 0x30200073)).1.pc = 0x2000
#guard (isaStep sM mZ (.word 0x30200073)).1.csrs.mstatus = mkMstatus true true
#guard (isaStep sM mZ (.word 0x30200073)).2
        = { pcTarget := 0x2000, sys := some .mret }
-- ecall at 0x1000, handler immediately mrets: back at the ecall's pc with
-- MIE restored (the ecall handler would advance mepc in software; the
-- architectural round trip is pc-exact)
#guard (let s1 := (isaStep sG mZ (.word 0x00000073)).1
        let s2 := (isaStep s1 mZ (.word 0x30200073)).1
        (s2.pc, s2.csrs.mstatusMie)) = (0x1000#32, true)

/-! ### CSR instructions (rd ← old, WARL write, no-write forms) -/

private def sC : ArchState :=
  { (ArchState.init 0x1000).writeReg 6 0xABCD1234 with
    csrs := { mscratch := 0x00005555 } }
-- csrrw x5, mscratch, x6: rd gets old, file gets rs1
#guard (isaStep sC mZ (.word 0x340312F3)).1.readReg 5 = 0x00005555
#guard (isaStep sC mZ (.word 0x340312F3)).1.csrs.mscratch = 0xABCD1234
#guard (isaStep sC mZ (.word 0x340312F3)).1.pc = 0x1004
#guard (isaStep sC mZ (.word 0x340312F3)).2.sys
        = some (.csr .rw 5 (.reg 6) 0x340)
-- csrrs x7, mscratch, x0: pure read, no write
#guard (isaStep sC mZ (.word 0x340023F3)).1.readReg 7 = 0x00005555
#guard (isaStep sC mZ (.word 0x340023F3)).1.csrs.mscratch = 0x00005555
-- csrrsi x6, mie, 31: set-bits write lands legalized (31 & IRQ_MASK = 8)
#guard (isaStep (ArchState.init 0x1000) mZ (.word 0x304FE373)).1.csrs.mie = 0x00000008
-- csrrw x0, mepc, x6 (0x34131073): WARL clears bit 0 (0xABCD1234 is even; use odd rs1)
private def sC1 : ArchState :=
  { (ArchState.init 0x1000).writeReg 6 0x00001235 with csrs := {} }
#guard (isaStep sC1 mZ (.word 0x34131073)).1.csrs.mepc = 0x00001234
-- …then mret lands exactly there: write-mepc → mret round trip
#guard (let s1 := (isaStep sC1 mZ (.word 0x34131073)).1
        (isaStep s1 mZ (.word 0x30200073)).1.pc) = 0x1234#32
-- csrrc x0, mstatus, x6 with x6 = 8: clears MIE only (0x1808 → 0x1800)
private def sC2 : ArchState :=
  { (ArchState.init 0x1000).writeReg 6 0x00000008 with
    csrs := { mstatus := mkMstatus true false } }
#guard (isaStep sC2 mZ (.word 0x30033073)).1.csrs.mstatus = 0x00001800

/-! ### Interrupt dispatch through the step -/

-- MSI+MTI pending: MSI (3) wins, vectored to base + 12; the fetched addi
-- does NOT execute (x1 stays 0) and mepc is its pc
#guard (isaStep sG mZ (.word 0x00500093) (irq := 0x00000088)).1.pc = 0x0000800C
#guard (isaStep sG mZ (.word 0x00500093) (irq := 0x00000088)).1.csrs.mepc = 0x1000
#guard (isaStep sG mZ (.word 0x00500093) (irq := 0x00000088)).1.csrs.mcause = 0x80000003
#guard (isaStep sG mZ (.word 0x00500093) (irq := 0x00000088)).1.readReg 1 = 0
#guard (isaStep sG mZ (.word 0x00500093) (irq := 0x00000088)).2.trap
        = some (.interrupt 3)
-- fast irq 31 outranks everything
#guard (isaStep sG mZ (.word 0x00500093) (irq := 0xFFFF0888)).1.pc = 0x0000807C
-- globally disabled: the addi retires instead
#guard (isaStep sQ mZ (.word 0x00500093) (irq := 0x00000088)).1.readReg 1 = 5
#guard (isaStep sQ mZ (.word 0x00500093) (irq := 0x00000088)).1.pc = 0x1004
-- direct-mode mtvec: interrupt to base
#guard (isaStep { sG with csrs := { csrsG with mtvec := 0x00008000 } } mZ
          (.word 0x00500093) (irq := 0x00000088)).1.pc = 0x00008000

/-! ### WFI: wait, wake, and resume-past-WFI -/

-- no pending interrupt: architecturally stalled (same state, same pc)
#guard (isaStep sQ mZ (.word 0x10500073)).1.pc = 0x1000
#guard (isaStep sQ mZ (.word 0x10500073)).2
        = { pcTarget := 0x1000, sys := some .wfi }
-- locally-enabled pending irq wakes even with MIE off: retires, no trap
#guard (isaStep sQ mZ (.word 0x10500073) (irq := 0x00010000)).1.pc = 0x1004
#guard (isaStep sQ mZ (.word 0x10500073) (irq := 0x00010000)).2.trap = none
-- irq pending but not locally enabled: still stalled
#guard (isaStep { sQ with csrs := { sQ.csrs with mie := 0 } } mZ
          (.word 0x10500073) (irq := 0x00010000)).1.pc = 0x1000
-- MIE on: the WFI-first rule — WFI retires this step, the interrupt is
-- taken next step with mepc PAST the wfi (v1.11 "resume after WFI")
#guard (isaStep sG mZ (.word 0x10500073) (irq := 0x00010000)).1.pc = 0x1004
#guard (isaStep sG mZ (.word 0x10500073) (irq := 0x00010000)).2.trap = none
#guard (let s1 := (isaStep sG mZ (.word 0x10500073) (irq := 0x00010000)).1
        let (s2, e2) := isaStep s1 mZ (.word 0x00500093) (irq := 0x00010000)
        (s2.pc, s2.csrs.mepc, e2.trap))
        = (0x00008040#32, 0x1004#32, some (Cause.interrupt 16))

/-! ### Compressed parcels: pc + 2 retirement and pc + 2 links -/

-- c.jal 100: links pc + 2 (the ilen fix), targets pc + 100
#guard (isaStep sQ mZ (.half 0x2095)).1.readReg 1 = 0x1002
#guard (isaStep sQ mZ (.half 0x2095)).1.pc = 0x1064
-- c.addi16sp -512 retires at pc + 2
private def sSp : ArchState := (ArchState.init 0x1000).writeReg 2 0x800
#guard (isaStep sSp mZ (.half 0x7101)).1.pc = 0x1002
#guard (isaStep sSp mZ (.half 0x7101)).1.readReg 2 = 0x600
-- an illegal halfword (c.fld at FPU = 0) traps like any illegal instruction
#guard (isaStep sG mZ (.half 0x2000)).2.trap = some .illegalInstr
-- c.swsp through isaStepMem: the store lands in memory
private def sSw : ArchState := ((ArchState.init 0x1000).writeReg 2 0x200).writeReg 12 0x12345678
#guard ((isaStepMem sSw mZ (.half 0xD032)).2 0x220) = 0x78#8
#guard ((isaStepMem sSw mZ (.half 0xD032)).2 0x223) = 0x12#8

/-! ### Fences retire as no-ops through the full step -/

#guard (isaStep sQ mZ (.word 0x0FF0000F)).1.pc = 0x1004
#guard (isaStep sQ mZ (.word 0x0FF0000F)).2
        = { pcTarget := 0x1004, sys := some .fence }

end LeanModels.Rv
