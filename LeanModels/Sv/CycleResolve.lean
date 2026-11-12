import LeanModels.Sv.ObserveE
import LeanModels.Sv.Kernel.XResolve

/-!
# X-E bridge for cycle observations

This is the observation-level bridge used by cycle contracts.  It relates the
pre and post port reads independently and projects back to equal reads when a
consumer proves those reads known.  It does not define a cycle machine or
touch the provisional run2 route.
-/

namespace LeanModels.Sv.Observe

open LeanModels.Sv.Kernel

def OptionXRead (source concrete : Option LVec) : Prop :=
  match source, concrete with
  | none, none => True
  | some source, some concrete => XRead source concrete
  | _, _ => False

def CycleXRead (source concrete : CycleObs PortSample) : Prop :=
  ∀ name,
    OptionXRead (source.pre.read name) (concrete.pre.read name) ∧
      OptionXRead (source.post.read name) (concrete.post.read name)

theorem optionXRead_eq_of_known {source concrete : Option LVec}
    (hread : OptionXRead source concrete)
    (hknown : ∀ value, source = some value → value.bits.toList.all Logic.isKnown = true) :
    source = concrete := by
  cases source with
  | none => cases concrete <;> simp [OptionXRead] at hread ⊢
  | some source =>
      cases concrete with
      | none => simp [OptionXRead] at hread
      | some concrete =>
          have heq := xRead_eq_of_known (hknown source rfl) hread
          cases heq
          rfl

theorem CycleXRead.pre_read_eq_of_known {source concrete : CycleObs PortSample}
    (hread : CycleXRead source concrete)
    (hknown : ∀ name value, source.pre.read name = some value →
      value.bits.toList.all Logic.isKnown = true) :
    ∀ name, source.pre.read name = concrete.pre.read name := by
  intro name
  exact optionXRead_eq_of_known (hread name).1 (fun value hvalue => hknown name value hvalue)

theorem CycleXRead.post_read_eq_of_known {source concrete : CycleObs PortSample}
    (hread : CycleXRead source concrete)
    (hknown : ∀ name value, source.post.read name = some value →
      value.bits.toList.all Logic.isKnown = true) :
    ∀ name, source.post.read name = concrete.post.read name := by
  intro name
  exact optionXRead_eq_of_known (hread name).2 (fun value hvalue => hknown name value hvalue)

end LeanModels.Sv.Observe

#print axioms LeanModels.Sv.Observe.optionXRead_eq_of_known
#print axioms LeanModels.Sv.Observe.CycleXRead.pre_read_eq_of_known
#print axioms LeanModels.Sv.Observe.CycleXRead.post_read_eq_of_known
