import LeanModels.Sv.Engine2.Wait

/-!
# Engine 2 fork-group state

A fork group records semantic identity, the parent activation, immediate-child
membership, its join mode and whether children have been released. Child lists
are membership data only: their order is not a scheduler order. This module
does not define spawning, release, join wakeups, cancellation, descendant
traversal or process-slot storage.
-/

namespace LeanModels.Sv.Engine2

structure ForkKey where
  registration : Nat
  deriving DecidableEq, Repr

inductive ForkJoinKind where
  | join
  | joinAny
  | joinNone
  deriving DecidableEq, Repr

inductive ForkRelease where
  | deferred
  | released
  deriving DecidableEq, Repr

namespace ForkJoinKind

theorem cases (kind : ForkJoinKind) :
    kind = .join ∨ kind = .joinAny ∨ kind = .joinNone := by
  cases kind <;> simp

end ForkJoinKind

namespace ForkRelease

theorem cases (release : ForkRelease) :
    release = .deferred ∨ release = .released := by
  cases release <;> simp

end ForkRelease

structure ForkState where
  key : ForkKey
  parent : ContinuationKey
  children : List ProcessKey
  joinKind : ForkJoinKind
  release : ForkRelease
  deriving DecidableEq, Repr

namespace ForkState

def initialJoin (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) : ForkState :=
  ⟨key, parent, children, .join, .released⟩

def initialJoinAny (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) : ForkState :=
  ⟨key, parent, children, .joinAny, .released⟩

def initialJoinNone (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) : ForkState :=
  ⟨key, parent, children, .joinNone, .deferred⟩

def parentProcess (state : ForkState) : ProcessKey := state.parent.owner

def childCount (state : ForkState) : Nat := state.children.length

def hasChild (state : ForkState) (child : ProcessKey) : Bool :=
  state.children.any (fun candidate => candidate == child)

def isDeferred (state : ForkState) : Bool := state.release == .deferred

def isReleased (state : ForkState) : Bool := state.release == .released

theorem initialJoin_key (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) :
    (initialJoin key parent children).key = key := rfl

theorem initialJoin_parent (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) :
    (initialJoin key parent children).parent = parent := rfl

theorem initialJoin_children (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) :
    (initialJoin key parent children).children = children := rfl

theorem initialJoin_kind (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) :
    (initialJoin key parent children).joinKind = .join := rfl

theorem initialJoinAny_kind (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) :
    (initialJoinAny key parent children).joinKind = .joinAny := rfl

theorem initialJoinNone_kind (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) :
    (initialJoinNone key parent children).joinKind = .joinNone := rfl

theorem initialJoin_released (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) :
    (initialJoin key parent children).release = .released := rfl

theorem initialJoinAny_released (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) :
    (initialJoinAny key parent children).release = .released := rfl

theorem initialJoinNone_deferred (key : ForkKey) (parent : ContinuationKey)
    (children : List ProcessKey) :
    (initialJoinNone key parent children).release = .deferred := rfl

theorem parentProcess_eq (state : ForkState) :
    state.parentProcess = state.parent.owner := rfl

theorem childCount_eq (state : ForkState) :
    state.childCount = state.children.length := rfl

theorem hasChild_head (state : ForkState) (child : ProcessKey) :
    (ForkState.mk state.key state.parent (child :: state.children)
      state.joinKind state.release).hasChild child = true := by
  simp [hasChild]

theorem kind_cases (state : ForkState) :
    state.joinKind = .join ∨ state.joinKind = .joinAny ∨
      state.joinKind = .joinNone := by
  exact state.joinKind.cases

theorem release_cases (state : ForkState) :
    state.release = .deferred ∨ state.release = .released := by
  exact state.release.cases

end ForkState

#guard ((ForkState.initialJoin ⟨0⟩ ⟨⟨0⟩, 0⟩ [⟨1⟩]).joinKind == .join)
#guard ((ForkState.initialJoinAny ⟨1⟩ ⟨⟨1⟩, 0⟩ []).joinKind == .joinAny)
#guard ((ForkState.initialJoinNone ⟨2⟩ ⟨⟨2⟩, 0⟩ [⟨3⟩]).release == .deferred)
#guard ((ForkState.initialJoin ⟨0⟩ ⟨⟨0⟩, 0⟩ [⟨1⟩, ⟨2⟩]).childCount == 2)
#guard ((ForkState.initialJoin ⟨0⟩ ⟨⟨0⟩, 0⟩ [⟨1⟩]).hasChild ⟨1⟩)
#guard !(ForkState.initialJoin ⟨0⟩ ⟨⟨0⟩, 0⟩ [⟨1⟩]).hasChild ⟨2⟩

#print axioms ForkJoinKind.cases
#print axioms ForkRelease.cases
#print axioms ForkState.kind_cases
#print axioms ForkState.release_cases
#print axioms ForkState.hasChild_head

end LeanModels.Sv.Engine2
