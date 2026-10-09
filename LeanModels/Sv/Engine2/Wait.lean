import LeanModels.Sv.Engine2.Process
import LeanModels.Sv.Engine2.Regions
import LeanModels.Sv.Engine2.Time

/-!
# Engine 2 normalized wait registrations

A partial dependency vocabulary for IEEE 1800-2023 clauses 9.4 and 15.5.
Ordinary dependencies denote directly monitored values, not an unchecked
decomposition of arbitrary event expressions into their operands. Named-event
keys denote non-null synchronization objects, not names or persistent trigger
state. No ABI edge-mask conversion or source normalization is asserted here.

Registration identity and continuation incarnation are independent. Neither is
a native slot, wrapping generation word or automatic-storage activation token.
Identity recognition alone does not implement cancellation, effective
sensitization, single-wake consumption or legal region selection.
-/

namespace LeanModels.Sv.Engine2

structure SignalKey where
  registration : Nat
  deriving DecidableEq, Repr

structure NamedEventKey where
  registration : Nat
  deriving DecidableEq, Repr

/-- Directional edges inspect the result's LSB. `eitherEdge` is posedge or
negedge; `anyChange` observes the whole result, including X/Z exchanges. -/
inductive OrdinaryEdge where
  | posedge
  | negedge
  | eitherEdge
  | anyChange
  deriving DecidableEq, Repr

inductive WaitDependency where
  | ordinary (signal : SignalKey) (edge : OrdinaryEdge)
  | occurrence (event : NamedEventKey)
  deriving DecidableEq, Repr

/-- OR alternatives in the admitted nonempty event-wait subset. Order and
duplicates are retained, without assigning wake priority or multiplicity. -/
structure EventDependencies where
  head : WaitDependency
  tail : List WaitDependency
  deriving DecidableEq, Repr

namespace EventDependencies

def toList (dependencies : EventDependencies) : List WaitDependency :=
  dependencies.head :: dependencies.tail

end EventDependencies

/-- Semantic execution/continuation-cancellation incarnation. -/
structure ContinuationKey where
  owner : ProcessKey
  incarnation : Nat
  deriving DecidableEq, Repr

structure WaitKey where
  registration : Nat
  deriving DecidableEq, Repr

structure WaitIdentity where
  key : WaitKey
  continuation : ContinuationKey
  deriving DecidableEq, Repr

inductive WaitReason where
  | delay (due : SimTime)
  | events (dependencies : EventDependencies)
  | forever
  deriving DecidableEq, Repr

/-- A captured descriptor, not a second suspension or active-wait authority.
`forever` requires independent justification, never a failed dependency census.
Region legality and absolute deadline construction are future obligations. -/
structure WaitRegistration where
  identity : WaitIdentity
  reason : WaitReason
  resumeRegion : Region
  deriving DecidableEq, Repr

namespace WaitRegistration

def owner (registration : WaitRegistration) : ProcessKey :=
  registration.identity.continuation.owner

/-- Exact identity recognition, not permission to wake a historical record. -/
def hasIdentity (registration : WaitRegistration) (identity : WaitIdentity) : Bool :=
  decide (registration.identity = identity)

end WaitRegistration

#guard OrdinaryEdge.eitherEdge != OrdinaryEdge.anyChange
#guard (EventDependencies.mk (.ordinary ⟨0⟩ .posedge) []).toList.length == 1
#guard (EventDependencies.mk (.ordinary ⟨0⟩ .posedge)
  [.ordinary ⟨0⟩ .posedge]).toList.length == 2
#guard (EventDependencies.mk (.ordinary ⟨0⟩ .anyChange) [.occurrence ⟨0⟩]).toList.length == 2
#guard (WaitRegistration.mk ⟨⟨0⟩, ⟨⟨0⟩, 0⟩⟩ (.delay (SimTime.zero.after 5)) .active).hasIdentity
  ⟨⟨0⟩, ⟨⟨0⟩, 0⟩⟩
#guard !(WaitRegistration.mk ⟨⟨0⟩, ⟨⟨0⟩, 0⟩⟩ .forever .active).hasIdentity
  ⟨⟨1⟩, ⟨⟨0⟩, 0⟩⟩
#guard !(WaitRegistration.mk ⟨⟨0⟩, ⟨⟨0⟩, 0⟩⟩ .forever .active).hasIdentity
  ⟨⟨0⟩, ⟨⟨1⟩, 0⟩⟩
#guard !(WaitRegistration.mk ⟨⟨0⟩, ⟨⟨0⟩, 0⟩⟩ .forever .reactive).hasIdentity
  ⟨⟨0⟩, ⟨⟨0⟩, 1⟩⟩

namespace EventDependencies

theorem toList_ne_nil (dependencies : EventDependencies) : dependencies.toList ≠ [] := by
  simp [toList]

theorem length_positive (dependencies : EventDependencies) : 0 < dependencies.toList.length := by
  simp [toList]

theorem head_mem (dependencies : EventDependencies) : dependencies.head ∈ dependencies.toList := by
  simp [toList]

theorem toList_injective : Function.Injective toList := by
  intro first second sameList
  cases first
  cases second
  simp only [toList, List.cons.injEq] at sameList
  rcases sameList with ⟨rfl, rfl⟩
  rfl

end EventDependencies

namespace WaitRegistration

theorem hasIdentity_iff (registration : WaitRegistration) (identity : WaitIdentity) :
    registration.hasIdentity identity = true ↔ registration.identity = identity := by
  simp [hasIdentity]

theorem hasIdentity_false_iff (registration : WaitRegistration) (identity : WaitIdentity) :
    registration.hasIdentity identity = false ↔ registration.identity ≠ identity := by
  simp [hasIdentity]

theorem different_wait_key (registration : WaitRegistration) (identity : WaitIdentity)
    (different : registration.identity.key ≠ identity.key) :
    registration.hasIdentity identity = false := by
  rw [hasIdentity_false_iff]
  intro same
  exact different (congrArg WaitIdentity.key same)

theorem different_owner (registration : WaitRegistration) (identity : WaitIdentity)
    (different : registration.owner ≠ identity.continuation.owner) :
    registration.hasIdentity identity = false := by
  rw [hasIdentity_false_iff]
  intro same
  exact different (congrArg (fun observed => observed.continuation.owner) same)

theorem different_incarnation (registration : WaitRegistration) (identity : WaitIdentity)
    (different : registration.identity.continuation.incarnation ≠ identity.continuation.incarnation) :
    registration.hasIdentity identity = false := by
  rw [hasIdentity_false_iff]
  intro same
  exact different (congrArg (fun observed => observed.continuation.incarnation) same)

end WaitRegistration

theorem continuationKey_eq_iff (first second : ContinuationKey) :
    first = second ↔ first.owner = second.owner ∧ first.incarnation = second.incarnation := by
  cases first
  cases second
  simp only [ContinuationKey.mk.injEq]

theorem waitIdentity_eq_iff (first second : WaitIdentity) :
    first = second ↔ first.key = second.key ∧
      first.continuation.owner = second.continuation.owner ∧
      first.continuation.incarnation = second.continuation.incarnation := by
  cases first
  cases second
  simp only [WaitIdentity.mk.injEq, continuationKey_eq_iff]

#print axioms EventDependencies.toList_injective
#print axioms WaitRegistration.hasIdentity_iff
#print axioms WaitRegistration.different_wait_key
#print axioms WaitRegistration.different_owner
#print axioms WaitRegistration.different_incarnation
#print axioms waitIdentity_eq_iff

end LeanModels.Sv.Engine2
