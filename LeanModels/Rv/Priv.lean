import LeanModels.Rv.Csr

/-!
# Privileged transfer semantics: traps, MRET, interrupt dispatch (v1.11, M-only)

The machine-mode transfer semantics of the scoped model (`PULP_SECURE = 0`:
M is the only privilege level, so there is no privilege-level state to track
— `misa.U = 0` and the RTL hardwires `priv_lvl_q = PRIV_LVL_M`). Three
artifacts:

* `trapEnter` — the mstatus stack dance, defined **once** for every trap
  (exception or interrupt): it is the projection source for spec-surface
  entry 8's `csr_trap_entry_atomic` (the one-edge trap tuple of
  `cv32e40p_cs_registers`) and for entry 10's `controller_irq_boundary`
  (which cause/save-PC tuple the controller commands).
* `mret` — the inverse dance (`csr_restore_mret_i` in the RTL).
* `pendingSet`/`irqPriority`/`selectIrq`/`takeInterrupt?` — non-CLIC
  interrupt dispatch in sail-riscv's `getPendingSet`/`dispatchInterrupt`
  split (SYNTHESIS adoption #4), with the priority order transliterated from
  `cv32e40p_int_controller.sv`'s encoder cascade.

## The priority order, reconciled honestly

Priv v1.11 §3.1.9 fixes the *standard* order MEI > MSI > MTI (external,
software, timer — note software above timer) and leaves platform-custom
interrupts to the platform. sail-riscv dispatches MEI > MSI > MTI likewise.
`cv32e40p_int_controller.sv` (lines 95–148) implements: fast interrupts 31
down to 16 **first**, then MEI (11) > MSI (3) > MTI (7). So within the
standard trio the RTL matches v1.11 and sail exactly (the cascade's
`MEI, MSI, MTI` line order is the priority — MSI's lower bit index still
outranks MTI); the only nonstandard fact is that the sixteen custom fast
interrupts outrank MEI, which v1.11 permits for platform interrupts. The RTL
cascade continues below MTI through reserved ids (15:12, then 10/2/6, 9/1/5,
8/0/4) — those lines are dead under `IRQ_MASK` (both `irq_q` and `mie` are
masked), so `irqPriority` omits them; the omission is exact, not an
approximation (`pendingSet ⊆ irqMask`, guarded below).

## Trap entry facts (RTL `cv32e40p_cs_registers.sv` lines 1043–1064, v1.11 §3.1.6.1)

On any trap: `MPIE := MIE; MIE := 0; MPP := M` (the last is invisible at
`PULP_SECURE = 0` — MPP already reads M), `mepc := pc` of the interrupted
instruction, `mcause := interrupt ++ 0 ++ code`. Exceptions vector to the
`mtvec` **base regardless of mode** (the RTL's `EXC_PC_EXCEPTION` arm; also
v1.11: vectoring applies to interrupts only); interrupts go to
`base + 4·id` when mode = vectored (`mtvec[0] = 1`, the reset state), else
to base. MRET: `MIE := MPIE; MPIE := 1; MPP := M`, `pc := mepc`.

`mepc` stores the trap pc unmasked (the RTL stores `exception_pc`
directly, without the `& ~1` of the software-write path): pc parity is a
step invariant (every architectural pc is even), not something trap entry
re-enforces.
-/

namespace LeanModels.Rv

/-! ## Causes -/

/-- A trap cause of the scoped model. The exception causes are the ones a
`PULP_SECURE = 0`, no-PMP, no-debug CV32E40P can raise architecturally
(bus-fault inputs are asserted away in the RTL, so access faults cannot
occur; ecall-from-U needs a U mode). Encodings: v1.11 Table 3.6 =
`cv32e40p_pkg.sv` `EXC_CAUSE_*`. -/
inductive Cause where
  /-- Illegal instruction (code 2) — also the fate of unimplemented-CSR
  accesses. -/
  | illegalInstr
  /-- Breakpoint from EBREAK (code 3). -/
  | breakpoint
  /-- Environment call from M-mode (code 11). -/
  | ecallM
  /-- Machine interrupt `id` (one of the `irqMask` bits; `mcause` bit 31
  set). -/
  | interrupt (id : Fin 32)
  deriving DecidableEq, Repr

/-- The 5-bit exception/interrupt code. -/
def Cause.code : Cause → BitVec 5
  | .illegalInstr => 2
  | .breakpoint   => 3
  | .ecallM       => 11
  | .interrupt id => BitVec.ofNat 5 id.val

/-- Interrupt bit (`mcause[31]`). -/
def Cause.isInterrupt : Cause → Bool
  | .interrupt _ => true
  | _            => false

/-- The `mcause` value this cause lands: `interrupt ++ 0#26 ++ code`
(already `legalizeMcause`-legal by construction). -/
def Cause.mcauseVal (c : Cause) : BitVec 32 :=
  ((if c.isInterrupt then 1#1 else 0#1) ++ (0 : BitVec 26) ++ c.code : BitVec 32)

/-! ## The mstatus stack dance (defined once) -/

/-- Trap entry on `mstatus`: `MPIE := MIE; MIE := 0; MPP := M` (v1.11
§3.1.6.1; RTL lines 1058–1061). Used by `trapEnter` for exceptions and
interrupts alike. -/
def mstatusOnTrap (m : BitVec 32) : BitVec 32 :=
  mkMstatus (mie := false) (mpie := m[3])

/-- MRET on `mstatus`: `MIE := MPIE; MPIE := 1; MPP := M` (M because U mode
is not supported — v1.11: "set to U, or M if user-mode is not supported";
RTL lines 1067–1072). -/
def mstatusOnMret (m : BitVec 32) : BitVec 32 :=
  mkMstatus (mie := m[7]) (mpie := true)

/-! ## Trap entry and return -/

/-- The trap handler address: `mtvec` base for every exception; for
interrupts, `base + 4·id` in vectored mode (`mtvec[0]`, the reset state) and
base in direct mode. Matches the RTL's `EXC_PC_EXCEPTION`/`EXC_PC_IRQ` mux
(`cv32e40p_if_stage.sv`; the `+` never carries into the base because the
base's low 8 bits are zero, so it equals the RTL's concatenation
`{base[31:8], 1'b0, id, 2'b0}`). -/
def trapVector (f : CsrFile) (c : Cause) : BitVec 32 :=
  let base := f.mtvec &&& 0xFFFFFF00
  match c with
  | .interrupt id => if f.mtvec[0] then base + 4 * BitVec.ofNat 32 id.val else base
  | _ => base

/-- Enter a trap: the whole architectural trap tuple in one definition —
`pc := trapVector`, `mepc := pc` of the interrupted instruction,
`mcause := c`, and the `mstatusOnTrap` dance. Registers are untouched.

Projection: spec-surface entry 8's `csr_trap_entry_atomic` states exactly
this tuple landing in one clock edge (with the save-pc selected by
`csr_save_{if,id,ex}_i`), and entry 10's `controller_irq_boundary` states
the controller commanding it with `cause = 1 ++ irq_id` on the `irq_ack_o`
edge. For interrupts `s.pc` is the pc of the *next unexecuted* instruction
(dispatch happens before execution in `Step.lean`), which is v1.11's "pc of
the instruction that was interrupted" — and the WFI-first rule in
`Step.lean` makes that pc the one *after* a waiting WFI. -/
def trapEnter (s : ArchState) (c : Cause) : ArchState :=
  { s with
    pc := trapVector s.csrs c
    csrs := { s.csrs with
      mepc    := s.pc
      mcause  := c.mcauseVal
      mstatus := mstatusOnTrap s.csrs.mstatus } }

/-- Return from a machine trap: `pc := mepc`, `mstatusOnMret` dance.
(`mepc` is bit-0-clear by invariant, so no target masking is needed —
unlike JALR there is no `& ~1` in the RTL's mret path either: the target
comes straight from `mepc_q`.) -/
def mret (s : ArchState) : ArchState :=
  { s with
    pc := s.csrs.mepc
    csrs := { s.csrs with mstatus := mstatusOnMret s.csrs.mstatus } }

/-! ## Interrupt dispatch (non-CLIC, sail `getPendingSet`/`dispatchInterrupt` split) -/

/-- The pending-and-locally-enabled set: `irq & IRQ_MASK & mie` (the RTL's
`irq_local_qual`; `mip = irq & IRQ_MASK` and the qualification with `mie`).
Always a subset of `irqMask`. -/
def pendingSet (f : CsrFile) (irq : BitVec 32) : BitVec 32 :=
  irq &&& irqMask &&& f.mie

/-- The CV32E40P interrupt priority order, highest first: fast interrupts 31
down to 16, then MEI (11) > MSI (3) > MTI (7). Transliterated from the
`cv32e40p_int_controller.sv` encoder cascade; see the module docstring for
the honest reconciliation with v1.11 §3.1.9 (standard trio identical; fast
irqs above MEI is a platform choice; the cascade's dead reserved lines are
omitted exactly). This list is the projection source for entry 10's
interrupt-boundary spec (`irq_id_o` selection). -/
def irqPriority : List (Fin 32) :=
  [31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 11, 3, 7]

/-- Select the highest-priority set bit of a pending set (`none` iff the
masked set is empty — `irqPriority` covers every bit of `irqMask`). -/
def selectIrq (pending : BitVec 32) : Option (Fin 32) :=
  irqPriority.find? fun i => pending.getLsbD i.val

/-- Interrupt dispatch decision: `some id` iff some implemented interrupt is
pending, locally enabled (`mie`), and interrupts are globally enabled
(`mstatus.MIE` — the RTL's `m_irq_enable_o`, sans the debug-single-step
gating that is out of scope). -/
def takeInterrupt? (f : CsrFile) (irq : BitVec 32) : Option (Fin 32) :=
  if f.mstatusMie then selectIrq (pendingSet f irq) else none

/-! ## `#guard` battery -/

/-! ### Cause encodings -/

#guard Cause.illegalInstr.mcauseVal = 0x00000002
#guard Cause.breakpoint.mcauseVal   = 0x00000003
#guard Cause.ecallM.mcauseVal       = 0x0000000B
#guard (Cause.interrupt 31).mcauseVal = 0x8000001F
#guard (Cause.interrupt 3).mcauseVal  = 0x80000003
-- every cause value is mcause-legal as stored
#guard [Cause.illegalInstr, .breakpoint, .ecallM, .interrupt 31, .interrupt 7].all
  fun c => legalizeMcause 0 c.mcauseVal == c.mcauseVal

/-! ### Trap entry / MRET round trips -/

private def csrsV : CsrFile :=      -- vectored mtvec at 0x8000, MIE set
  { mtvec := 0x00008001, mstatus := mkMstatus true false }
private def sT : ArchState :=
  { regs := fun _ => 0, pc := 0x1234, csrs := csrsV }

-- exceptions vector to base even in vectored mode; interrupts vector by id
#guard (trapEnter sT .ecallM).pc = 0x00008000
#guard (trapEnter sT .illegalInstr).pc = 0x00008000
#guard (trapEnter sT (.interrupt 31)).pc = 0x0000807C
#guard (trapEnter sT (.interrupt 3)).pc  = 0x0000800C
-- direct mode: everything to base
#guard (trapEnter { sT with csrs := { csrsV with mtvec := 0x00008000 } }
        (.interrupt 31)).pc = 0x00008000
-- the trap tuple: mepc, mcause, and the mstatus dance (MPIE := MIE, MIE := 0)
#guard (trapEnter sT .ecallM).csrs.mepc = 0x1234
#guard (trapEnter sT .ecallM).csrs.mcause = 0x0000000B
#guard (trapEnter sT .ecallM).csrs.mstatus = mkMstatus false true
#guard (trapEnter sT (.interrupt 16)).csrs.mcause = 0x80000010
-- registers untouched
#guard (trapEnter sT .ecallM).regs 5 = 0

-- trap → mret round trip: pc restored, MIE restored through MPIE, MPIE := 1
#guard (mret (trapEnter sT .ecallM)).pc = 0x1234
#guard (mret (trapEnter sT .ecallM)).csrs.mstatus = mkMstatus true true
-- with interrupts initially disabled, mret leaves them disabled
private def sT0 : ArchState := { sT with csrs := { csrsV with mstatus := mkMstatus false false } }
#guard (mret (trapEnter sT0 .breakpoint)).csrs.mstatus = mkMstatus false true
-- nested-trap loss (architectural, v1.11): a second trap before mret
-- overwrites MPIE with the (cleared) MIE, so the pre-trap enable is lost
#guard (mret (trapEnter (trapEnter sT .ecallM) .breakpoint)).csrs.mstatus
        = mkMstatus false true

/-! ### Interrupt dispatch: pending set and priority -/

private def allOn : CsrFile := { mstatus := mkMstatus true false, mie := irqMask }

-- pendingSet masks by IRQ_MASK and mie
#guard pendingSet allOn 0xFFFFFFFF = 0xFFFF0888
#guard pendingSet { allOn with mie := 0x00000888 } 0xFFFFFFFF = 0x00000888
#guard pendingSet allOn 0x00007654 = 0x00000000    -- reserved ids never pend
-- irqPriority covers irqMask exactly (the dead cascade lines are omitted exactly)
#guard (irqPriority.foldl (fun acc i => acc ||| (1#32 <<< (BitVec.ofNat 32 i.val)))
        0#32) = irqMask
#guard irqPriority.Nodup

-- fast irqs first, highest id wins
#guard selectIrq 0xFFFF0888 = some 31
#guard selectIrq 0x00030888 = some 17
#guard selectIrq 0x00010888 = some 16
-- the standard trio: MEI > MSI > MTI (MSI's lower bit outranks MTI!)
#guard selectIrq 0x00000888 = some 11
#guard selectIrq 0x00000088 = some 3
#guard selectIrq 0x00000080 = some 7
#guard selectIrq 0 = none

-- global gate: mstatus.MIE off ⇒ never taken; local gate: mie bit off ⇒ not taken
#guard takeInterrupt? allOn 0x00010000 = some 16
#guard takeInterrupt? { allOn with mstatus := mkMstatus false false } 0x00010000 = none
#guard takeInterrupt? { allOn with mie := 0x00000888 } 0x00010000 = none
#guard takeInterrupt? allOn 0 = none

end LeanModels.Rv
