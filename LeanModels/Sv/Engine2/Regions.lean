import LeanModels.Sv.Regions

/-!
# Engine 2 event-region vocabulary

The complete IEEE 1800-2023 clause 4.4 inventory, its simulation/PLI-only
partition, and the region sets of clause 4.4.1. This is a state-schema piece,
not a scheduler. Presentation positions do not define execution priority:
clause 4.5 revisits iterative regions within a time slot.

The existing R1 vocabulary embeds without changing its interpreter or theorem
statements. That embedding preserves names and classification, not execution
semantics. No ABI ordinal or implementation queue policy is an authority here.
-/

namespace LeanModels.Sv.Engine2

inductive Region where
  | preponed
  | preActive
  | active
  | inactive
  | preNBA
  | nba
  | postNBA
  | preObserved
  | observed
  | postObserved
  | reactive
  | reInactive
  | preReNBA
  | reNBA
  | postReNBA
  | prePostponed
  | postponed
deriving Repr, BEq, DecidableEq, Inhabited

namespace Region

/-- Clause 4.4's presentation order, not a legal execution trace. -/
def all : List Region :=
  [preponed, preActive, active, inactive, preNBA, nba, postNBA, preObserved,
   observed, postObserved, reactive, reInactive, preReNBA, reNBA, postReNBA,
   prePostponed, postponed]

/-- The simulation regions of clause 4.4.2. -/
def simulation : List Region :=
  [preponed, active, inactive, nba, observed, reactive, reInactive, reNBA,
   postponed]

/-- The additional PLI-only regions of clause 4.4.3. Preponed and Postponed
also permit PLI callbacks but belong to the simulation-region partition. -/
def pliOnly : List Region :=
  [preActive, preNBA, postNBA, preObserved, postObserved, preReNBA, postReNBA,
   prePostponed]

def isPLIOnly : Region → Bool
  | preActive | preNBA | postNBA | preObserved | postObserved
  | preReNBA | postReNBA | prePostponed => true
  | _ => false

/-- The five-region active set of clause 4.4.1, not the broader scheduling
phase that continues through Post-Observed in clause 4.5. -/
def activeSet : List Region :=
  [active, inactive, preNBA, nba, postNBA]

def isActiveSet : Region → Bool
  | active | inactive | preNBA | nba | postNBA => true
  | _ => false

def reactiveSet : List Region :=
  [reactive, reInactive, preReNBA, reNBA, postReNBA]

def isReactiveSet : Region → Bool
  | reactive | reInactive | preReNBA | reNBA | postReNBA => true
  | _ => false

/-- The fourteen iterative regions of clause 4.4.1. Membership supplies no
permission to traverse a scheduling edge without its queue/phase guards. -/
def iterative : List Region :=
  [active, inactive, preNBA, nba, postNBA, preObserved, observed, postObserved,
   reactive, reInactive, preReNBA, reNBA, postReNBA, prePostponed]

def isIterative : Region → Bool
  | preponed | preActive | postponed => false
  | _ => true

/-- A position in the clause 4.4 inventory. This is not a scheduler rank or
a claim that region positions increase along execution. -/
def position : Region → Fin 17
  | preponed => 0
  | preActive => 1
  | active => 2
  | inactive => 3
  | preNBA => 4
  | nba => 5
  | postNBA => 6
  | preObserved => 7
  | observed => 8
  | postObserved => 9
  | reactive => 10
  | reInactive => 11
  | preReNBA => 12
  | reNBA => 13
  | postReNBA => 14
  | prePostponed => 15
  | postponed => 16

#guard all.length == 17
#guard simulation.length == 9
#guard pliOnly.length == 8
#guard activeSet.length == 5
#guard reactiveSet.length == 5
#guard iterative.length == 14
#guard position preObserved == 7
#guard position prePostponed == 15
#guard isPLIOnly preObserved && isPLIOnly prePostponed
#guard !isPLIOnly preponed && !isPLIOnly postponed
#guard !isActiveSet preObserved && !isReactiveSet prePostponed
#guard isIterative preObserved && isIterative prePostponed

theorem mem_all (region : Region) : region ∈ all := by
  cases region <;> simp [all]

theorem all_nodup : all.Nodup := by decide

theorem all_length : all.length = 17 := rfl

theorem simulation_length : simulation.length = 9 := rfl

theorem pliOnly_length : pliOnly.length = 8 := rfl

theorem simulation_partition : all.filter (fun region => !isPLIOnly region) = simulation := by
  decide

theorem pliOnly_partition : all.filter isPLIOnly = pliOnly := by decide

theorem activeSet_partition : all.filter isActiveSet = activeSet := by decide

theorem reactiveSet_partition : all.filter isReactiveSet = reactiveSet := by decide

theorem iterative_partition : all.filter isIterative = iterative := by decide

theorem activeSet_reactiveSet_disjoint (region : Region) :
    ¬ (region ∈ activeSet ∧ region ∈ reactiveSet) := by
  cases region <;> simp [activeSet, reactiveSet]

theorem position_injective : Function.Injective position := by
  intro firstRegion secondRegion equalPosition
  cases firstRegion <;> cases secondRegion <;> simp_all [position]

theorem positions_all : all.map (fun region => (position region).val) = List.range 17 := by
  decide

/-- The legacy fifteen-region R1 vocabulary, embedded by name only. -/
def ofR1 : LeanModels.Sv.Region → Region
  | .preponed => preponed
  | .preActive => preActive
  | .active => active
  | .inactive => inactive
  | .preNBA => preNBA
  | .nba => nba
  | .postNBA => postNBA
  | .observed => observed
  | .postObserved => postObserved
  | .reactive => reactive
  | .reInactive => reInactive
  | .preReNBA => preReNBA
  | .reNBA => reNBA
  | .postReNBA => postReNBA
  | .postponed => postponed

theorem ofR1_injective : Function.Injective ofR1 := by
  intro firstRegion secondRegion equalRegion
  cases firstRegion <;> cases secondRegion <;> simp_all [ofR1]

theorem ofR1_isPLIOnly (region : LeanModels.Sv.Region) :
    isPLIOnly (ofR1 region) = region.isPLI := by
  cases region <;> rfl

theorem missing_from_R1 :
    all.filter (fun region => !(LeanModels.Sv.Region.all.map ofR1).contains region) =
      [preObserved, prePostponed] := by
  decide

#print axioms mem_all
#print axioms all_nodup
#print axioms simulation_partition
#print axioms pliOnly_partition
#print axioms position_injective
#print axioms positions_all
#print axioms ofR1_injective
#print axioms ofR1_isPLIOnly
#print axioms missing_from_R1

end Region
end LeanModels.Sv.Engine2
