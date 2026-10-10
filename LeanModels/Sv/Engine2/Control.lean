import LeanModels.Sv.Engine2.Wait

/-!
# Engine 2 process-control registrations

Control registrations are separate from dependency waits and from the process
state's explicit suspension flag. An awaiter records the process continuation
that will resume after a target process completes. A named-block activation
records typed declaration identity, activation identity and the saved
post-block continuation used by disable. Registration keys do not depend on
continuation data, so replacing a continuation does not replace the control
registration. This module defines identity and derived views only; control
transitions, cancellation, wakeups and declaration lookup remain future rules.
-/

namespace LeanModels.Sv.Engine2

structure AwaitKey where
  registration : Nat
  deriving DecidableEq, Repr

structure AwaitRegistration where
  key : AwaitKey
  continuation : ContinuationKey
  target : ProcessKey
  resumeRegion : Region
  deriving DecidableEq, Repr

namespace AwaitRegistration

def owner (registration : AwaitRegistration) : ProcessKey :=
  registration.continuation.owner

def hasKey (registration : AwaitRegistration) (key : AwaitKey) : Bool :=
  decide (registration.key = key)

def withContinuation (registration : AwaitRegistration)
    (continuation : ContinuationKey) : AwaitRegistration :=
  { registration with continuation := continuation }

theorem owner_eq (registration : AwaitRegistration) :
    registration.owner = registration.continuation.owner := rfl

theorem key_preserved (registration : AwaitRegistration) :
    registration.key = registration.key := rfl

theorem target_preserved (registration : AwaitRegistration) :
    registration.target = registration.target := rfl

theorem withContinuation_key (registration : AwaitRegistration)
    (continuation : ContinuationKey) :
    (registration.withContinuation continuation).key = registration.key := rfl

theorem hasKey_iff (registration : AwaitRegistration) (key : AwaitKey) :
    registration.hasKey key = true ↔ registration.key = key := by
  simp [hasKey]

end AwaitRegistration

structure NamedBlockKey where
  declaration : Nat
  deriving DecidableEq, Repr

structure NamedBlockActivationKey where
  declaration : NamedBlockKey
  activation : Nat
  deriving DecidableEq, Repr

structure NamedBlockActivation where
  identity : NamedBlockActivationKey
  entry : ContinuationKey
  postBlock : ContinuationKey
  deriving DecidableEq, Repr

namespace NamedBlockActivation

def owner (activation : NamedBlockActivation) : ProcessKey :=
  activation.entry.owner

def hasIdentity (activation : NamedBlockActivation)
    (identity : NamedBlockActivationKey) : Bool :=
  decide (activation.identity = identity)

theorem owner_eq (activation : NamedBlockActivation) :
    activation.owner = activation.entry.owner := rfl

theorem identity_preserved (activation : NamedBlockActivation) :
    activation.identity = activation.identity := rfl

theorem postBlock_preserved (activation : NamedBlockActivation) :
    activation.postBlock = activation.postBlock := rfl

theorem hasIdentity_iff (activation : NamedBlockActivation)
    (identity : NamedBlockActivationKey) :
    activation.hasIdentity identity = true ↔ activation.identity = identity := by
  simp [hasIdentity]

end NamedBlockActivation

structure ControlState where
  awaiters : List AwaitRegistration
  namedBlocks : List NamedBlockActivation
  deriving DecidableEq, Repr

namespace ControlState

def initial : ControlState :=
  ⟨[], []⟩

def awaiterCount (state : ControlState) : Nat :=
  state.awaiters.length

def namedBlockCount (state : ControlState) : Nat :=
  state.namedBlocks.length

def hasAwaiter (state : ControlState) (process : ProcessKey) : Bool :=
  state.awaiters.any (fun registration => registration.owner == process)

def hasNamedBlock (state : ControlState) (identity : NamedBlockActivationKey) : Bool :=
  state.namedBlocks.any (fun activation => activation.hasIdentity identity)

/-- A derived view of explicit process-control suspension. The process state
remains authoritative; named-block membership alone does not imply suspension. -/
def suspensionView (state : ControlState) (process : ProcessKey) : Bool :=
  state.hasAwaiter process

theorem initial_awaiters : initial.awaiters = [] := rfl

theorem initial_namedBlocks : initial.namedBlocks = [] := rfl

theorem awaiterCount_eq (state : ControlState) :
    state.awaiterCount = state.awaiters.length := rfl

theorem namedBlockCount_eq (state : ControlState) :
    state.namedBlockCount = state.namedBlocks.length := rfl

theorem hasAwaiter_head (state : ControlState) (registration : AwaitRegistration) :
    (ControlState.mk (registration :: state.awaiters) state.namedBlocks).hasAwaiter
      registration.owner = true := by
  simp [hasAwaiter]

theorem hasNamedBlock_head (state : ControlState)
    (activation : NamedBlockActivation) :
    (ControlState.mk state.awaiters (activation :: state.namedBlocks)).hasNamedBlock
      activation.identity = true := by
  simp [hasNamedBlock, NamedBlockActivation.hasIdentity]

theorem suspensionView_eq_hasAwaiter (state : ControlState) (process : ProcessKey) :
    state.suspensionView process = state.hasAwaiter process := rfl

end ControlState

#guard (AwaitRegistration.mk ⟨0⟩ ⟨⟨0⟩, 1⟩ ⟨1⟩ .active).owner == ⟨0⟩
#guard (NamedBlockActivation.mk ⟨⟨0⟩, 1⟩ ⟨⟨0⟩, 2⟩ ⟨⟨0⟩, 3⟩).owner == ⟨0⟩
#guard !ControlState.initial.hasAwaiter ⟨0⟩
#guard !ControlState.initial.hasNamedBlock ⟨⟨0⟩, 0⟩
#guard (ControlState.mk
  [⟨⟨0⟩, ⟨⟨0⟩, 0⟩, ⟨1⟩, .active⟩] []).hasAwaiter ⟨0⟩
#guard ((ControlState.mk []
  [NamedBlockActivation.mk ⟨⟨0⟩, 0⟩ ⟨⟨0⟩, 1⟩ ⟨⟨0⟩, 2⟩]).hasNamedBlock
  ⟨⟨0⟩, 0⟩)

#print axioms AwaitRegistration.hasKey_iff
#print axioms NamedBlockActivation.hasIdentity_iff
#print axioms ControlState.hasAwaiter_head
#print axioms ControlState.hasNamedBlock_head

end LeanModels.Sv.Engine2
