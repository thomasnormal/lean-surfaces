import LeanModels.Sv.Basic

/-!
# Correlated 0/1 concretizations of unknown values

**Status: derived relation; executor integration pending.**

IEEE 1800 §6.3.1 treats `x` and `z` as bits whose 0/1 value is not known.
This file is the first E-facing piece of `docs/sv-x-resolution.md`: it
enumerates all concretizations of one source value, keeping the choice
correlated for every later read of that value. It contains no execution and no
fuel.
-/

namespace LeanModels.Sv
namespace Kernel

/-- The concrete values represented by one four-state bit. -/
def Logic.resolutions : Logic → List Logic
  | .l0 => [.l0]
  | .l1 => [.l1]
  | .lx | .lz => [.l0, .l1]

/-- One concrete bit is a resolution of an abstract bit. -/
def Logic.Resolves : Logic → Logic → Prop
  | .l0, .l0 | .l1, .l1 | .lx, .l0 | .lx, .l1 | .lz, .l0 | .lz, .l1 => True
  | _, _ => False

/-- All concrete bit lists represented by an abstract bit list. -/
def resolveBits : List Logic → List (List Logic)
  | [] => [[]]
  | b :: bs => (Logic.resolutions b).flatMap fun c =>
      (resolveBits bs).map fun cs => c :: cs

/-- All 0/1 concretizations of a four-state vector, preserving bit order. -/
def LVec.concretizations (v : LVec) : List LVec :=
  (resolveBits v.bits.toList).map fun bs => ⟨bs.toArray⟩

/-- Pointwise resolution of two bit lists, preserving their length. -/
def bitListResolves : List Logic → List Logic → Prop
  | [], [] => True
  | a :: as, b :: bs => Logic.Resolves a b ∧ bitListResolves as bs
  | _, _ => False

private theorem resolves_of_mem : ∀ (b c : Logic),
    c ∈ Logic.resolutions b → Logic.Resolves b c := by
  intro b c
  cases b <;> cases c <;> simp [Logic.resolutions, Logic.Resolves]

/-- A vector is a concretization of another when every bit resolves and the
width is preserved. -/
def LVec.Resolves (abstract concrete : LVec) : Prop :=
  abstract.bits.toList.length = concrete.bits.toList.length ∧
    bitListResolves abstract.bits.toList concrete.bits.toList

/-- IEEE 1800 §6.11's explicit 4-state to 2-state conversion boundary.
This is a separate relation from `LVec.Resolves`: conversion maps x/z to 0
by definition, rather than quantifying those source bits as environment
choices. -/
def TwoStateBoundary (source result : LVec) : Prop :=
  result = source.toTwoState

/-- The typed value-set boundary used by E. Four-state destinations retain a
source concretization; two-state destinations use the deterministic §6.11
conversion. The destination's `fourState` bit is passed explicitly here so
this relation stays independent of the AST and declaration records. -/
theorem twoStateBoundary_total (source : LVec) :
    TwoStateBoundary source source.toTwoState := rfl

theorem twoStateBoundary_unique {source result result' : LVec}
    (h : TwoStateBoundary source result)
    (h' : TwoStateBoundary source result') : result = result' := by
  exact h.trans h'.symm

theorem twoStateBoundary_width {source result : LVec}
    (h : TwoStateBoundary source result) : result.width = source.width := by
  cases h
  simp [LVec.toTwoState, LVec.width]

def TypedResolution (fourState : Bool) (source result : LVec) : Prop :=
  if fourState then result ∈ LVec.concretizations source else TwoStateBoundary source result

theorem typedResolution_twoState_unique {source result result' : LVec}
    (h : TypedResolution false source result)
    (h' : TypedResolution false source result') : result = result' := by
  exact twoStateBoundary_unique h h'

theorem typedResolution_twoState_total (source : LVec) :
    TypedResolution false source source.toTwoState := by
  exact twoStateBoundary_total source

/-- A decision is known when every correlated concretization gives the same
boolean result. This is deliberately weaker than requiring every source bit
to be known: `1'bx` is definitely true for a nonzero test, while `1'b0x` is
not. The predicate is proof-facing; it does not change the four-state
evaluator or silently choose a branch. -/
def DecisionKnown (v : LVec) : Prop :=
  ∀ w z, w ∈ LVec.concretizations v → z ∈ LVec.concretizations v →
    LVec.condTrue v = LVec.condTrue w ∧ LVec.condTrue w = LVec.condTrue z

/-- A resolved branch decision: the concrete value is tied to the source
through the correlated relation, and the source condition is known to agree
across all such values. This is the proof object a future E branch step can
consume without consulting x-optimistic `condTrue` directly. -/
structure ResolvedDecision (source result : LVec) : Prop where
  resolves : result ∈ LVec.concretizations source
  known : DecisionKnown source

private theorem mem_resolveBits : ∀ (bs : List Logic) (cs : List Logic),
    cs ∈ resolveBits bs → bitListResolves bs cs
  | [], cs, h => by
      simp only [resolveBits] at h
      have : cs = [] := by simpa using h
      subst cs
      exact True.intro
  | b :: bs, cs, h => by
      rw [resolveBits, List.mem_flatMap] at h
      rcases h with ⟨c, hc, hcs⟩
      rw [List.mem_map] at hcs
      obtain ⟨rest, hr, rfl⟩ := hcs
      have hb : Logic.Resolves b c := resolves_of_mem b c hc
      have hrest : bitListResolves bs rest := by
        simpa using mem_resolveBits bs rest hr
      exact ⟨hb, hrest⟩

private theorem bitListResolves_length : ∀ (as bs : List Logic),
    bitListResolves as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | _ :: as, _ :: bs, h =>
      congrArg Nat.succ (bitListResolves_length as bs h.2)

private theorem resolveBits_known : ∀ (bs : List Logic),
    bs.all Logic.isKnown = true → resolveBits bs = [bs]
  | [], _ => by simp [resolveBits]
  | b :: bs, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      have hb : b = .l0 ∨ b = .l1 := by
        cases b <;> simp [Logic.isKnown] at h ⊢
      rcases hb with rfl | rfl <;>
        simp [resolveBits, Logic.resolutions, List.flatMap, resolveBits_known bs h.2]

/-- Every listed concretization resolves its source vector. -/
theorem mem_concretizations_resolves {v w : LVec} (h : w ∈ LVec.concretizations v) :
    LVec.Resolves v w := by
  unfold LVec.concretizations at h
  simp only [List.mem_map] at h
  obtain ⟨bits, hbits, rfl⟩ := h
  have hf := mem_resolveBits v.bits.toList bits hbits
  refine ⟨?_, ?_⟩
  · exact bitListResolves_length _ _ hf
  · exact hf

/-- A known vector has exactly one concretization. -/
theorem concretizations_of_known {v : LVec}
    (h : v.bits.toList.all Logic.isKnown = true) :
    LVec.concretizations v = [v] := by
  unfold LVec.concretizations
  rw [resolveBits_known _ h]
  simp [Array.toArray_toList]

theorem decisionKnown_of_allKnown {v : LVec}
    (h : v.bits.toList.all Logic.isKnown = true) : DecisionKnown v := by
  intro w z hw hz
  rw [concretizations_of_known h] at hw hz
  simp_all [DecisionKnown]

theorem DecisionKnown.same {v : LVec} (h : DecisionKnown v)
    {w z : LVec} (hw : w ∈ LVec.concretizations v)
    (hz : z ∈ LVec.concretizations v) :
    LVec.condTrue w = LVec.condTrue z :=
  (h w z hw hz).2

theorem DecisionKnown.abstract {v : LVec} (h : DecisionKnown v)
    {w : LVec} (hw : w ∈ LVec.concretizations v) :
    LVec.condTrue v = LVec.condTrue w :=
  (h w w hw hw).1

theorem typedResolution_decision_agrees {source result : LVec}
    (hknown : DecisionKnown source)
    (hres : TypedResolution true source result) :
    LVec.condTrue source = LVec.condTrue result := by
  exact hknown.abstract hres

theorem ResolvedDecision.agrees {source result : LVec}
    (h : ResolvedDecision source result) :
    LVec.condTrue source = LVec.condTrue result :=
  h.known.abstract h.resolves

theorem ResolvedDecision.branch_eq {source result : LVec} {α : Type}
    (h : ResolvedDecision source result) (thenBranch elseBranch : α) :
    (if LVec.condTrue source then thenBranch else elseBranch) =
      (if LVec.condTrue result then thenBranch else elseBranch) := by
  rw [h.agrees]

#guard (LVec.concretizations (LVec.ofNat 3 5)).length == 1
#guard (LVec.concretizations (LVec.xVec 2)).length == 4
#guard (LVec.concretizations (LVec.toTwoState (LVec.xVec 2))).length == 1

example : TwoStateBoundary (LVec.lit "xz") ((LVec.lit "xz").toTwoState) :=
  twoStateBoundary_total _

example {v r : LVec} (h : TwoStateBoundary v r) : r.width = v.width := by
  exact twoStateBoundary_width h

example : DecisionKnown (LVec.ofNat 3 5) := by
  apply decisionKnown_of_allKnown
  decide

example : ∀ w ∈ LVec.concretizations (LVec.ofNat 3 5),
    LVec.condTrue (LVec.ofNat 3 5) = LVec.condTrue w := by
  intro w hw
  exact DecisionKnown.abstract (decisionKnown_of_allKnown (v := LVec.ofNat 3 5) (by decide)) hw

#print axioms mem_concretizations_resolves
#print axioms concretizations_of_known

end Kernel
end LeanModels.Sv
