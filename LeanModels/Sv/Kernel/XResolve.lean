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

#guard (LVec.concretizations (LVec.ofNat 3 5)).length == 1
#guard (LVec.concretizations (LVec.xVec 2)).length == 4
#guard (LVec.concretizations (LVec.toTwoState (LVec.xVec 2))).length == 1

#print axioms mem_concretizations_resolves
#print axioms concretizations_of_known

end Kernel
end LeanModels.Sv
