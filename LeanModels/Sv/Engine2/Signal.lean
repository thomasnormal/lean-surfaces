import LeanModels.Sv.Engine2.Event

/-!
# Engine 2 ordinary signal publication state

`SignalState` is the semantic read-side authority for one ordinary signal:
its identity, current four-state value and publication token. The token is
zero before the first ordinary value publication and is represented as a
nonzero natural after publication. Named-event occurrence state is separate.
This module defines state and structural observations only; it does not define
value-change detection, token allocation, fanout, queue admission or wakeups.
-/

namespace LeanModels.Sv.Engine2

inductive PublicationGeneration where
  | initial
  | issued (ordinal : Nat)
  deriving DecidableEq, Repr

namespace PublicationGeneration

def token : PublicationGeneration → Nat
  | .initial => 0
  | .issued ordinal => ordinal + 1

def isPublished (generation : PublicationGeneration) : Bool :=
  generation.token != 0

theorem token_initial : PublicationGeneration.initial.token = 0 := rfl

theorem token_issued_positive (ordinal : Nat) :
    0 < (PublicationGeneration.issued ordinal).token := by
  simp [token]

theorem token_eq_zero_iff (generation : PublicationGeneration) :
    generation.token = 0 ↔ generation = .initial := by
  cases generation with
  | initial => simp [token]
  | issued ordinal => simp [token]

theorem isPublished_initial :
    PublicationGeneration.initial.isPublished = false := by
  simp [isPublished, token]

theorem isPublished_issued (ordinal : Nat) :
    (PublicationGeneration.issued ordinal).isPublished = true := by
  simp [isPublished, token]

theorem cases (generation : PublicationGeneration) :
    generation = .initial ∨ ∃ ordinal, generation = .issued ordinal := by
  cases generation with
  | initial => exact Or.inl rfl
  | issued ordinal => exact Or.inr ⟨ordinal, rfl⟩

end PublicationGeneration

structure SignalState where
  key : SignalKey
  value : LVec
  publication : PublicationGeneration
  deriving DecidableEq, Repr

namespace SignalState

def initial (key : SignalKey) (value : LVec) : SignalState :=
  ⟨key, value, .initial⟩

def token (state : SignalState) : Nat := state.publication.token

def isPublished (state : SignalState) : Bool := state.publication.isPublished

theorem initial_key (key : SignalKey) (value : LVec) :
    (initial key value).key = key := rfl

theorem initial_value (key : SignalKey) (value : LVec) :
    (initial key value).value = value := rfl

theorem initial_token (key : SignalKey) (value : LVec) :
    (initial key value).token = 0 := rfl

theorem initial_unpublished (key : SignalKey) (value : LVec) :
    (initial key value).isPublished = false := by
  rfl

theorem token_zero_iff_initial (state : SignalState) :
    state.token = 0 ↔ state.publication = .initial := by
  exact PublicationGeneration.token_eq_zero_iff state.publication

theorem issued_token_positive (key : SignalKey) (value : LVec) (ordinal : Nat) :
    0 < (⟨key, value, .issued ordinal⟩ : SignalState).token := by
  simpa [token] using PublicationGeneration.token_issued_positive ordinal

theorem key_preserved (state : SignalState) : state.key = state.key := rfl

theorem value_preserved (state : SignalState) : state.value = state.value := rfl

theorem publication_preserved (state : SignalState) :
    state.publication = state.publication := rfl

end SignalState

#guard PublicationGeneration.initial.token == 0
#guard (PublicationGeneration.issued 0).token == 1
#guard (PublicationGeneration.issued 7).token == 8
#guard !PublicationGeneration.initial.isPublished
#guard (PublicationGeneration.issued 0).isPublished
#guard (SignalState.initial ⟨0⟩ ⟨#[.lx]⟩).token == 0
#guard !(SignalState.initial ⟨0⟩ ⟨#[.lx]⟩).isPublished
#guard (⟨⟨0⟩, ⟨#[.l1]⟩, .issued 3⟩ : SignalState).token == 4

#print axioms PublicationGeneration.token_eq_zero_iff
#print axioms PublicationGeneration.cases
#print axioms SignalState.token_zero_iff_initial
#print axioms SignalState.issued_token_positive

end LeanModels.Sv.Engine2
