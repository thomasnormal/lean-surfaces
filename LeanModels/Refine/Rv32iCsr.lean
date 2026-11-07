import LeanModels.Refine.Rv32iSystem

/-!
# RV32I Zicsr retirement boundary

The machine-mode Zicsr instructions share one architectural shape: read the
implemented CSR row, write the old value to `rd`, and optionally apply the
operation's read-modify-write result through that row's WARL legalizer.  The
row lookup remains an explicit premise, so an unimplemented address cannot be
silently treated as a no-op; `isaStepWith` reports those parcels as illegal
instruction traps instead.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## CSR operation shape -/

/-- The decoded Zicsr operation, retaining the CSR row address and operands. -/
structure CsrOpKind where
  op : CsrOp
  rd : Reg
  src : CsrSrc
  addr : BitVec 12
  deriving DecidableEq, Repr

/-- The architectural instruction represented by a Zicsr operation. -/
def CsrOpKind.toInstr (kind : CsrOpKind) : Instr :=
  .system (.csr kind.op kind.rd kind.src kind.addr)

/-! ## Architectural CSR equations -/

/-- The old CSR value selected by an implemented row. -/
def csrOld (s : ArchState) (row : CsrBehavior) : Word :=
  row.readView s.csrs

/-- The legalized CSR value produced by a Zicsr read-modify-write. -/
def csrWriteValue (s : ArchState) (row : CsrBehavior)
    (op : CsrOp) (src : CsrSrc) : Word :=
  row.legalize (csrOld s row) (csrRmw op (csrOld s row) (csrOperand s src))

/-- The architectural state after one implemented Zicsr operation. -/
def csrNext (s : ArchState) (row : CsrBehavior) (kind : CsrOpKind) : ArchState :=
  let old := csrOld s row
  let csrs' :=
    if csrWrites kind.op kind.src then
      row.write s.csrs (csrWriteValue s row kind.op kind.src)
    else s.csrs
  { s.writeReg kind.rd old with pc := s.pc + 4, csrs := csrs' }

/-- The architectural effects after one implemented Zicsr operation. -/
def csrEffects (s : ArchState) (kind : CsrOpKind) : StepEffects :=
  { pcTarget := s.pc + 4
    sys := some (.csr kind.op kind.rd kind.src kind.addr) }

/-- The exact ISA-side retirement for an implemented Zicsr parcel. -/
def csrRetirement (s : ArchState) (input : Input)
    (row : CsrBehavior) (kind : CsrOpKind) : Retirement :=
  Retirement.ofRvStep s input (csrNext s row kind) (csrEffects s kind)

/-! ## ISA and stateful-machine bridges -/

/-- Every profile takes the exact implemented-row Zicsr step when interrupts
are absent.  The row lookup premise is what separates this boundary from the
illegal-instruction path for an unimplemented CSR address. -/
theorem isaStepWith_csr (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (row : CsrBehavior) (kind : CsrOpKind)
    (hdecode : Fetched.decode (.word w) = some kind.toInstr)
    (hrow : findCsr? kind.addr = some row) :
    isaStepWith profile s mem (.word w) 0 =
      (csrNext s row kind, csrEffects s kind) := by
  cases kind with
  | mk op rd src addr =>
    change Fetched.decode (.word w) =
      some (.system (.csr op rd src addr)) at hdecode
    change findCsr? addr = some row at hrow
    have hirq : takeInterrupt? s.csrs 0 = none := by
      simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
    simp only [isaStepWith, hirq, hdecode]
    rw [hrow]
    simp [CsrOpKind.toInstr, csrNext, csrEffects, csrOld, csrWriteValue,
      Fetched.size]

/-- The implemented-row Zicsr step preserves the threaded data memory. -/
theorem isaStepMemWith_csr (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (row : CsrBehavior) (kind : CsrOpKind)
    (hdecode : Fetched.decode (.word w) = some kind.toInstr)
    (hrow : findCsr? kind.addr = some row) :
    isaStepMemWith profile s mem (.word w) 0 =
      (csrNext s row kind, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_csr profile s mem w row kind hdecode hrow]
  rfl

/-- The generic machine adapter exposes the same implemented-row CSR boundary. -/
theorem rvMachineWith_csr (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (row : CsrBehavior) (kind : CsrOpKind)
    (hdecode : Fetched.decode (.word w) = some kind.toInstr)
    (hrow : findCsr? kind.addr = some row) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (csrNext s row kind,
        csrRetirement s { fetched := .word w, memory := mem, irq := 0 }
          row kind) := by
  simp only [rvMachineWith]
  rw [isaStepWith_csr profile s mem w row kind hdecode hrow]
  rfl

#print axioms LeanModels.Refine.isaStepWith_csr
#print axioms LeanModels.Refine.isaStepMemWith_csr
#print axioms LeanModels.Refine.rvMachineWith_csr

end LeanModels.Refine
