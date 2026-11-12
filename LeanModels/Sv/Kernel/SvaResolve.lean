import LeanModels.Sv.Sva
import LeanModels.Sv.Kernel.XResolve

/-!
# X-E bridge for sampled SVA values

This first SVA bridge lifts the known-read refinement through the assertion
case-equality observer. It does not change SVA evaluation or choose a value for
an unknown; unknown samples remain outside this theorem's known-read premise.
-/
namespace LeanModels.Sv.Kernel
open LeanModels.Sv

 theorem sva_caseEqual_xread_left {a a' b : LVec}
    (hknown : a.bits.toList.all Logic.isKnown = true)
    (hread : XRead a a') :
    caseEqual (some a) (some b) = caseEqual (some a') (some b) := by
  have h := xRead_eq_of_known hknown hread
  cases h
  rfl

theorem sva_caseEqual_xread_right {a b b' : LVec}
    (hknown : b.bits.toList.all Logic.isKnown = true)
    (hread : XRead b b') :
    caseEqual (some a) (some b) = caseEqual (some a) (some b') := by
  have h := xRead_eq_of_known hknown hread
  cases h
  rfl

theorem sva_signalAt_xread {state state' : SvState} {name : String}
    {source concrete : LVec}
    (hsource : SvState.lookup state name = some source)
    (hconcrete : SvState.lookup state' name = some concrete)
    (hknown : source.bits.toList.all Logic.isKnown = true)
    (hread : XRead source concrete) :
    signalAt [state] 0 name = signalAt [state'] 0 name := by
  have heq := xRead_eq_of_known hknown hread
  cases heq
  simp [signalAt, hsource, hconcrete]

theorem sva_valueEq_xread_left {trace trace' : List SvState} {index : Nat}
    {name : String} {source concrete : LVec}
    (hsource : trace[index]? = some ([(name, source)]))
    (hconcrete : trace'[index]? = some ([(name, concrete)]))
    (hknown : source.bits.toList.all Logic.isKnown = true)
    (hread : XRead source concrete) :
    SvaValue.eval trace index (.current (.ident name)) =
      SvaValue.eval trace' index (.current (.ident name)) := by
  have heq := xRead_eq_of_known hknown hread
  cases heq
  simp [SvaValue.eval, exprAt, hsource, hconcrete]

theorem sva_past_zero_xread {trace trace' : List SvState} {index : Nat}
    {name : String} {source concrete : LVec}
    (hsource : trace[index]? = some ([(name, source)]))
    (hconcrete : trace'[index]? = some ([(name, concrete)]))
    (hknown : source.bits.toList.all Logic.isKnown = true)
    (hread : XRead source concrete) :
    SvaValue.eval trace index (.past 0 (.ident name)) =
      SvaValue.eval trace' index (.past 0 (.ident name)) := by
  have heq := xRead_eq_of_known hknown hread
  cases heq
  simp [SvaValue.eval, exprAt, hsource, hconcrete]

theorem sva_past_xread {trace trace' : List SvState} {index cycles : Nat}
    {name : String} {source concrete : LVec}
    (hcycles : cycles ≤ index)
    (hsource : trace[index - cycles]? = some ([(name, source)]))
    (hconcrete : trace'[index - cycles]? = some ([(name, concrete)]))
    (hknown : source.bits.toList.all Logic.isKnown = true)
    (hread : XRead source concrete) :
    SvaValue.eval trace index (.past cycles (.ident name)) =
      SvaValue.eval trace' index (.past cycles (.ident name)) := by
  have heq := xRead_eq_of_known hknown hread
  cases heq
  simp [SvaValue.eval, exprAt, hcycles, hsource, hconcrete]

theorem sva_countOnes_xread {trace trace' : List SvState} {index : Nat}
    {name : String} {source concrete : LVec}
    (hsource : trace[index]? = some ([(name, source)]))
    (hconcrete : trace'[index]? = some ([(name, concrete)]))
    (hknown : source.bits.toList.all Logic.isKnown = true)
    (hread : XRead source concrete) :
    SvaValue.eval trace index (.countOnes (.ident name)) =
      SvaValue.eval trace' index (.countOnes (.ident name)) := by
  have heq := xRead_eq_of_known hknown hread
  cases heq
  simp [SvaValue.eval, exprAt, hsource, hconcrete]

theorem sva_binary_eval_congr {trace trace' : List SvState} {index : Nat}
    {op : BinOp} {left right left' right' : SvaValue}
    (hleft : SvaValue.eval trace index left = SvaValue.eval trace' index left')
    (hright : SvaValue.eval trace index right = SvaValue.eval trace' index right') :
    SvaValue.eval trace index (.binary op left right) =
      SvaValue.eval trace' index (.binary op left' right') := by
  simp only [SvaValue.eval, hleft, hright]

theorem sva_bool_evalLogic_congr {trace trace' : List SvState} {index : Nat}
    {left right : SvaBool}
    (h : SvaBool.evalLogic trace index left =
      SvaBool.evalLogic trace' index right) :
    SvaBool.evalChecked trace index left =
      SvaBool.evalChecked trace' index right := by
  simp [SvaBool.evalChecked, h]

theorem sva_signal_bool_xread {state state' : SvState} {name : String}
    {source concrete : LVec}
    (hsource : SvState.lookup state name = some source)
    (hconcrete : SvState.lookup state' name = some concrete)
    (hknown : source.bits.toList.all Logic.isKnown = true)
    (hread : XRead source concrete) :
    SvaBool.evalLogic [state] 0 (.signal name) =
      SvaBool.evalLogic [state'] 0 (.signal name) := by
  have hs := sva_signalAt_xread hsource hconcrete hknown hread
  simp [SvaBool.evalLogic, hs]

theorem sva_signal_checked_xread {state state' : SvState} {name : String}
    {source concrete : LVec}
    (hsource : SvState.lookup state name = some source)
    (hconcrete : SvState.lookup state' name = some concrete)
    (hknown : source.bits.toList.all Logic.isKnown = true)
    (hread : XRead source concrete) :
    SvaBool.evalChecked [state] 0 (.signal name) =
      SvaBool.evalChecked [state'] 0 (.signal name) := by
  apply sva_bool_evalLogic_congr
  exact sva_signal_bool_xread hsource hconcrete hknown hread

end LeanModels.Sv.Kernel
