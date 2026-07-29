import LeanModels.Circuit.MixedSignal
import LeanModels.Spice.DramBitcell

/-!
# Transaction-level DRAM bank contract

This module is the implementation-independent boundary consumed by a digital
controller.  Physical array, decoder, precharge, sense, restore, and write
driver proofs refine this contract; the contract itself does not assume a
particular circuit topology.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

/-- Logical contents of a rows-by-columns DRAM array. -/
structure DramMatrixState (rows columns : Nat) where
  bits : Fin rows → Fin columns → Bool

def DramMatrixState.write
    (state : DramMatrixState rows columns)
    (row : Fin rows) (column : Fin columns) (value : Bool) :
    DramMatrixState rows columns :=
  { bits :=
      Function.update state.bits row
        (Function.update (state.bits row) column value) }

@[simp] theorem DramMatrixState.write_selected
    (state : DramMatrixState rows columns)
    (row : Fin rows) (column : Fin columns) (value : Bool) :
    (state.write row column value).bits row column = value := by
  simp [DramMatrixState.write]

theorem DramMatrixState.write_other
    (state : DramMatrixState rows columns)
    (row selectedRow : Fin rows) (column selectedColumn : Fin columns)
    (value : Bool)
    (hother : row ≠ selectedRow ∨ column ≠ selectedColumn) :
    (state.write selectedRow selectedColumn value).bits row column =
      state.bits row column := by
  rcases hother with hrow | hcolumn
  · simp [DramMatrixState.write, hrow]
  · by_cases hrow : row = selectedRow
    · subst row
      simp [DramMatrixState.write, hcolumn]
    · simp [DramMatrixState.write, hrow]

inductive DramBankRequest (rows columns : Nat)
  | read (row : Fin rows) (column : Fin columns)
  | write (row : Fin rows) (column : Fin columns) (value : Bool)
  | refresh (row : Fin rows)
deriving Repr, DecidableEq

inductive DramBankResponse
  | readData (value : Bool)
  | acknowledged
deriving Repr, DecidableEq

/-- Analog timing obligations exposed at the digital transaction boundary. -/
structure DramBankTiming where
  readLatency : ℝ
  writeLatency : ℝ
  refreshLatency : ℝ
  retentionLimit : ℝ

def DramBankTiming.Valid (timing : DramBankTiming) : Prop :=
  0 ≤ timing.readLatency ∧
  0 ≤ timing.writeLatency ∧
  0 ≤ timing.refreshLatency ∧
  0 < timing.retentionLimit

noncomputable def DramBankTiming.latency
    (timing : DramBankTiming) :
    DramBankRequest rows columns → ℝ
  | .read _ _ => timing.readLatency
  | .write _ _ _ => timing.writeLatency
  | .refresh _ => timing.refreshLatency

/-- Functional state transition observed by the digital controller.

Reads are nondestructive at this boundary because the physical refinement
includes restoration.  A physical activation may temporarily disturb every
cell in the selected row. -/
def DramBankStep
    (before : DramMatrixState rows columns)
    (request : DramBankRequest rows columns)
    (response : DramBankResponse)
    (after : DramMatrixState rows columns) : Prop :=
  match request with
  | .read row column =>
      response = .readData (before.bits row column) ∧ after = before
  | .write row column value =>
      response = .acknowledged ∧ after = before.write row column value
  | .refresh _row =>
      response = .acknowledged ∧ after = before

structure DramBankTransaction (rows columns : Nat) where
  before : DramMatrixState rows columns
  request : DramBankRequest rows columns
  acceptedAt : HybridTime
  response : DramBankResponse
  completedAt : HybridTime
  after : DramMatrixState rows columns

/-- A completed operation satisfies both the functional bank transition and
the minimum analog latency promised by the implementation. -/
noncomputable def DramBankTransactionContract
    (timing : DramBankTiming)
    (transaction : DramBankTransaction rows columns) : Prop :=
  DramBankStep transaction.before transaction.request
      transaction.response transaction.after ∧
    transaction.acceptedAt.physical ≤ transaction.completedAt.physical ∧
    timing.latency transaction.request ≤
      transaction.completedAt.physical - transaction.acceptedAt.physical

noncomputable def canonicalDramResponse
    (before : DramMatrixState rows columns) :
    DramBankRequest rows columns → DramBankResponse
  | .read row column => .readData (before.bits row column)
  | .write _ _ _ => .acknowledged
  | .refresh _ => .acknowledged

def canonicalDramAfter
    (before : DramMatrixState rows columns) :
    DramBankRequest rows columns → DramMatrixState rows columns
  | .read _ _ => before
  | .write row column value => before.write row column value
  | .refresh _ => before

noncomputable def canonicalDramTransaction
    (timing : DramBankTiming)
    (before : DramMatrixState rows columns)
    (request : DramBankRequest rows columns)
    (acceptedAt : HybridTime) : DramBankTransaction rows columns :=
  { before
    request
    acceptedAt
    response := canonicalDramResponse before request
    completedAt :=
      ⟨acceptedAt.physical + timing.latency request, acceptedAt.microstep⟩
    after := canonicalDramAfter before request }

theorem dram_bank_step_realizable
    (before : DramMatrixState rows columns)
    (request : DramBankRequest rows columns) :
    ∃ response after, DramBankStep before request response after := by
  cases request <;>
    simp [DramBankStep, canonicalDramResponse, canonicalDramAfter]

theorem dram_bank_step_determinate
    {before : DramMatrixState rows columns}
    {request : DramBankRequest rows columns}
    {leftResponse rightResponse : DramBankResponse}
    {leftAfter rightAfter : DramMatrixState rows columns}
    (hleft : DramBankStep before request leftResponse leftAfter)
    (hright : DramBankStep before request rightResponse rightAfter) :
    leftResponse = rightResponse ∧ leftAfter = rightAfter := by
  cases request <;>
    simp [DramBankStep] at hleft hright
  all_goals
    exact ⟨hleft.1.trans hright.1.symm, hleft.2.trans hright.2.symm⟩

theorem canonical_dram_transaction_realizable
    {timing : DramBankTiming} (hvalid : timing.Valid)
    (before : DramMatrixState rows columns)
    (request : DramBankRequest rows columns)
    (acceptedAt : HybridTime) :
    DramBankTransactionContract timing
      (canonicalDramTransaction timing before request acceptedAt) := by
  constructor
  · cases request <;>
      simp [canonicalDramTransaction, DramBankStep,
        canonicalDramResponse, canonicalDramAfter]
  constructor
  · simp [canonicalDramTransaction]
    cases request <;>
      simp [DramBankTiming.latency, DramBankTiming.Valid] at hvalid ⊢ <;>
      linarith
  · simp [canonicalDramTransaction]

theorem dram_bank_read_correct
    {before after : DramMatrixState rows columns}
    {row : Fin rows} {column : Fin columns}
    {response : DramBankResponse}
    (hstep : DramBankStep before (.read row column) response after) :
    response = .readData (before.bits row column) ∧ after = before :=
  hstep

theorem dram_bank_write_correct
    {before after : DramMatrixState rows columns}
    {row : Fin rows} {column : Fin columns} {value : Bool}
    {response : DramBankResponse}
    (hstep : DramBankStep before (.write row column value) response after) :
    response = .acknowledged ∧
      after.bits row column = value ∧
      ∀ otherRow otherColumn,
        otherRow ≠ row ∨ otherColumn ≠ column →
        after.bits otherRow otherColumn =
          before.bits otherRow otherColumn := by
  rcases hstep with ⟨rfl, rfl⟩
  exact ⟨rfl, DramMatrixState.write_selected _ _ _ _,
    fun otherRow otherColumn hother =>
      DramMatrixState.write_other _ _ _ _ _ _ hother⟩

end LeanModels.Spice
