import LeanModels.Rv.Exec

/-!
# The CSR behavior table: WARL legalization as data (priv v1.11, CV32E40P scope)

`csrTable : List CsrBehavior` is the spec-side artifact of spec-surface
entry 8 (`cv32e40p_cs_registers`): one row per CSR of the scoped subset
{`mstatus`, `mtvec`, `mepc`, `mcause`, `mie`, `mscratch`} at `PULP_SECURE = 0`,
each row carrying the address, the reset value, and the WARL legalization
function *as data* (design law L3). The per-row `legalize` functions follow
sail-riscv's `legalize_<csr>` idiom (`sys_regs.sail`, BSD-2-Clause, RISC-V
International; SYNTHESIS adoption #4) — small named `old → wdata → value`
functions — with every field value **re-derived** for priv spec v1.11 against
`cv32e40p_cs_registers.sv` (read directly), not imported, because mainline
sail-riscv tracks a later privileged spec.

## The RTL ground truth (and one loud divergence)

All masks below were read out of `cv32e40p_cs_registers.sv` at
`PULP_SECURE = 0`, `FPU = 0`:

* **`mstatus` — DIVERGENCE from spec-surface entry 8's sketch, flagged.**
  Entry 8 sketched `mstatusLegalize` as picking `{uie, mie, upie, mpie, mpp,
  mprv}` — that is what the *write logic* computes (lines 954–961). But at
  `PULP_SECURE = 0` the register update (lines 1222–1231) hardwires
  `uie/upie/mprv` to 0 and `mpp` to `PRIV_LVL_M` on **every** cycle, so the
  effective WARL is: only bits 3 (MIE) and 7 (MPIE) are writable, MPP reads
  as `11` always, everything else reads 0. The sketch read the dead half of
  the write logic. Against priv v1.11 the *RTL* is conformant (`misa.U = 0`
  ⇒ `uie/upie/mprv` hardwired 0 is required; MPP as read-only `11` is legal
  WARL); the divergence is spec-surface-vs-RTL, and this table sides with
  the RTL: `legalizeMstatus old w = mkMstatus w[3] w[7]`.
* **`mtvec`**: stores base`[31:8]` (256-byte alignment — stricter than the
  ≥4-byte alignment v1.11 requires, legal WARL) and mode bit 0 only (mode
  bit 1 hardwired 0, so the reserved modes `10`/`11` legalize to `00`/`01` —
  a WARL choice; sail-riscv instead keeps the *old* mode on a reserved
  write, which is why `legalize` keeps its `old` argument even though no row
  in this scoped table consults it). Resets to *vectored* (`MTVEC_MODE =
  2'b01`) with base 0; the RTL also loads the boot base from the
  `mtvec_addr_i` port (`csr_mtvec_init_i`), which the model expresses by
  starting from a non-default `CsrFile`.
* **`mepc`**: `w &&& ~1` — bit 0 forced clear, bit 1 writable (16-bit
  alignment; correct for a C-extension hart per v1.11).
* **`mcause`**: the register is physically 6 bits; writes keep
  `{w[31], w[4:0]}` and reads produce `w[31] ++ 0#26 ++ w[4:0]`. v1.11 calls
  the exception-code field WLRL; collapsing bits 30:5 to zero is the RTL's
  (legal) narrowing, and reads can never produce them set.
* **`mie`**: `w &&& IRQ_MASK` with `IRQ_MASK = 0xFFFF0888` (fast irqs 31:16,
  MEI 11, MTI 7, MSI 3) — `cv32e40p_pkg.sv` line 725.
* **`mscratch`**: unrestricted.

Timing notes the ISA level absorbs: the RTL's `mie_bypass_o` makes a CSR
write to `mie` visible to the immediately following instruction — in a
sequential model every write is; and trap entry beating a same-cycle SW CSR
write (the `unique case (1'b1)` priority) is invisible here because a trap
and a CSR retirement never coincide in one `isaStep`.

Scope note (not a divergence): the RTL implements further CSRs (`misa`,
`mhartid`, `mip`, counters, debug/trigger, hwloop, …). Addresses outside
this table get `none` from `readCsr?`/`writeCsr?`, which `Step.lean` turns
into an illegal-instruction trap — the correct behavior for genuinely
unimplemented addresses; extending the subset means adding rows, not
machinery.
-/

namespace LeanModels.Rv

/-! ## Field constants -/

/-- The implemented-interrupt mask (`IRQ_MASK`, `cv32e40p_pkg.sv`): fast
interrupts 31:16, MEI (11), MTI (7), MSI (3). Both `mie` and the pending set
are always subsets of it. -/
def irqMask : BitVec 32 := 0xFFFF0888

/-- Assemble an `mstatus` read value from the two writable bits. MPP (bits
12:11) reads as `11` (M) always; every other bit reads 0 (`PULP_SECURE = 0`
hardwiring, see module docstring). The whole `mstatus` state space of this
model is the four values `{0x1800, 0x1808, 0x1880, 0x1888}`. -/
def mkMstatus (mie mpie : Bool) : BitVec 32 :=
  0x00001800 ||| (if mie then 0x00000008 else 0) ||| (if mpie then 0x00000080 else 0)

/-- `mstatus.MIE` (bit 3): the M-mode global interrupt enable. -/
def CsrFile.mstatusMie (f : CsrFile) : Bool := f.mstatus[3]

/-- `mstatus.MPIE` (bit 7): the pre-trap interrupt enable. -/
def CsrFile.mstatusMpie (f : CsrFile) : Bool := f.mstatus[7]

/-! ## Per-CSR legalization (sail-riscv `legalize_<csr>` shape, v1.11 values)

Each is `(old wdata : BitVec 32) → BitVec 32`, returning the architectural
value that a write of `wdata` actually lands. In this scoped subset no
legalizer consults `old` (CV32E40P's WARL choices are all pure masks); the
argument stays for the shape — sail's `legalize_tvec` does consult it. -/

/-- `mstatus`: keep MIE (bit 3) and MPIE (bit 7); MPP reads as M; all other
fields hardwired (see module docstring for the entry-8 divergence). -/
def legalizeMstatus (_old w : BitVec 32) : BitVec 32 :=
  mkMstatus w[3] w[7]

/-- `mtvec`: keep base`[31:8]` (256-byte aligned) and mode bit 0; bits 7:1
read as zero (mode bit 1 hardwired — reserved modes legalize away). -/
def legalizeMtvec (_old w : BitVec 32) : BitVec 32 :=
  (w &&& 0xFFFFFF00) ||| (w &&& 1)

/-- `mepc`: force bit 0 clear (16-bit alignment; C extension present). -/
def legalizeMepc (_old w : BitVec 32) : BitVec 32 :=
  w &&& ~~~1#32

/-- `mcause`: keep the interrupt bit (31) and the 5-bit code; the RTL's
6-bit register narrows v1.11's WLRL code field to bits 4:0. -/
def legalizeMcause (_old w : BitVec 32) : BitVec 32 :=
  w &&& 0x8000001F

/-- `mie`: implemented interrupts only (`w &&& IRQ_MASK`). -/
def legalizeMie (_old w : BitVec 32) : BitVec 32 :=
  w &&& irqMask

/-- `mscratch`: unrestricted. -/
def legalizeMscratch (_old w : BitVec 32) : BitVec 32 :=
  w

/-! ## The table -/

/-- One CSR's behavior, as data — the projection row spec-surface entry 8's
`csr_write_conforms`/`csr_trap_entry_atomic` theorems consume
(`cv32e40p_cs_registers` conformance). `readView`/`write` are the file
accessors (entry 8's `hwView` analog: `mtvec_o`, `mepc_o`, `mie_bypass_o`, …
observe exactly these values); `legalize` is the WARL semantics. The stored
value is legalized by invariant: `resetVal` is a `legalize` fixed point
(guarded below) and `writeCsr?` routes every software write through
`legalize`. -/
structure CsrBehavior where
  name     : String
  addr     : BitVec 12
  resetVal : BitVec 32
  /-- WARL legalization: the value a write of `wdata` lands, given the
  current value `old` (unused by every row in this subset — kept for the
  sail `legalize_<csr>` shape). -/
  legalize : (old wdata : BitVec 32) → BitVec 32
  /-- Read the CSR's architectural value out of the file. -/
  readView : CsrFile → BitVec 32
  /-- Store an (already legalized) value into the file. -/
  write    : CsrFile → BitVec 32 → CsrFile

/-- The CSR behavior table for the scoped v1.11 subset (`PULP_SECURE = 0`):
the projection source for spec-surface entry 8 (`cv32e40p_cs_registers`).
Every mask transliterated from `cv32e40p_cs_registers.sv`; shape from
sail-riscv (BSD-2-Clause). Addresses are the standard machine-mode ones
(`cv32e40p_pkg.sv` `csr_num_e`). -/
def csrTable : List CsrBehavior := [
  { name := "mstatus",  addr := 0x300, resetVal := 0x00001800
    legalize := legalizeMstatus
    readView := (·.mstatus),  write := fun f v => { f with mstatus := v } },
  { name := "mie",      addr := 0x304, resetVal := 0
    legalize := legalizeMie
    readView := (·.mie),      write := fun f v => { f with mie := v } },
  { name := "mtvec",    addr := 0x305, resetVal := 0x00000001
    legalize := legalizeMtvec
    readView := (·.mtvec),    write := fun f v => { f with mtvec := v } },
  { name := "mscratch", addr := 0x340, resetVal := 0
    legalize := legalizeMscratch
    readView := (·.mscratch), write := fun f v => { f with mscratch := v } },
  { name := "mepc",     addr := 0x341, resetVal := 0
    legalize := legalizeMepc
    readView := (·.mepc),     write := fun f v => { f with mepc := v } },
  { name := "mcause",   addr := 0x342, resetVal := 0
    legalize := legalizeMcause
    readView := (·.mcause),   write := fun f v => { f with mcause := v } }]

/-- Look up a CSR row by address; `none` = unimplemented in this scope. -/
def findCsr? (addr : BitVec 12) : Option CsrBehavior :=
  csrTable.find? (·.addr == addr)

/-- Read a CSR by address (`none` = unimplemented ⇒ illegal instruction in
`Step.lean`). -/
def readCsr? (f : CsrFile) (addr : BitVec 12) : Option (BitVec 32) :=
  (findCsr? addr).map (·.readView f)

/-- Write a CSR by address, through the row's WARL legalization. `none` =
unimplemented address (no partial writes: the caller traps instead). -/
def writeCsr? (f : CsrFile) (addr : BitVec 12) (wdata : BitVec 32) :
    Option CsrFile :=
  (findCsr? addr).map fun row => row.write f (row.legalize (row.readView f) wdata)

/-! ## `#guard` battery: table sanity + WARL legalization vectors -/

-- distinct addresses, and reset values are what a reset `CsrFile` reads
#guard (csrTable.map (·.addr)).Nodup
#guard csrTable.all fun row => row.readView {} == row.resetVal
-- reset values are legalize fixed points, so the file starts legalized
#guard csrTable.all fun row => row.legalize row.resetVal row.resetVal == row.resetVal
-- legalization is idempotent on every row (stored values stay legal)
#guard csrTable.all fun row =>
  [0xFFFFFFFF#32, 0xDEADBEEF, 0x00000001, 0x80000000].all fun w =>
    row.legalize 0 (row.legalize 0 w) == row.legalize 0 w

-- mstatus: only MIE/MPIE writable; MPP reads as M; all-ones lands 0x1888
#guard legalizeMstatus 0 0xFFFFFFFF = 0x00001888
#guard legalizeMstatus 0 0x00000000 = 0x00001800   -- MPP stuck at 11
#guard legalizeMstatus 0 0x00000008 = 0x00001808   -- MIE alone
#guard legalizeMstatus 0 0x00000080 = 0x00001880   -- MPIE alone
#guard legalizeMstatus 0 0x00000011 = 0x00001800   -- uie/upie writes dropped
#guard mkMstatus true false = 0x00001808
#guard (CsrFile.mstatusMie { mstatus := 0x00001808 }) = true
#guard (CsrFile.mstatusMpie { mstatus := 0x00001808 }) = false

-- mtvec: 256-byte base + mode bit 0; reserved mode bit 1 dropped
#guard legalizeMtvec 0 0xDEADBEEF = 0xDEADBE01
#guard legalizeMtvec 0 0xFFFFFFFF = 0xFFFFFF01
#guard legalizeMtvec 0 0x00008003 = 0x00008001    -- mode 11 → 01 (vectored)
#guard legalizeMtvec 0 0x00008002 = 0x00008000    -- mode 10 → 00 (direct)

-- mepc: bit 0 cleared, bit 1 kept (C-extension alignment)
#guard legalizeMepc 0 0xFFFFFFFF = 0xFFFFFFFE
#guard legalizeMepc 0 0x00001003 = 0x00001002

-- mcause: interrupt bit + 5-bit code only
#guard legalizeMcause 0 0xFFFFFFFF = 0x8000001F
#guard legalizeMcause 0 0x0000002B = 0x0000000B   -- code 43 narrows to 11
#guard legalizeMcause 0 0x8000000B = 0x8000000B

-- mie: IRQ_MASK
#guard legalizeMie 0 0xFFFFFFFF = 0xFFFF0888
#guard legalizeMie 0 0x00000FFF = 0x00000888      -- only MEI/MTI/MSI below 16
#guard legalizeMie 0 0x00030000 = 0x00030000      -- fast irqs 16,17 kept

-- table-driven read/write round trips
#guard writeCsr? {} 0x300 0xFFFFFFFF = some { mstatus := 0x00001888 }
#guard writeCsr? {} 0x304 0xFFFFFFFF = some { mie := 0xFFFF0888 }
#guard writeCsr? {} 0x305 0xDEADBEEF = some { mtvec := 0xDEADBE01 }
#guard writeCsr? {} 0x340 0xCAFEBABE = some { mscratch := 0xCAFEBABE }
#guard writeCsr? {} 0x341 0x00000101 = some { mepc := 0x00000100 }
#guard writeCsr? {} 0x342 0x800000FF = some { mcause := 0x8000001F }
#guard readCsr? { mscratch := 0x12345678 } 0x340 = some 0x12345678
#guard readCsr? {} 0x300 = some 0x00001800
-- unimplemented addresses are refused, not zero-filled
#guard readCsr? {} 0x344 = none     -- mip: implemented in RTL, out of scope
#guard readCsr? {} 0x7C0 = none     -- custom space
#guard writeCsr? {} 0x301 0 = none  -- misa: out of scope

end LeanModels.Rv
