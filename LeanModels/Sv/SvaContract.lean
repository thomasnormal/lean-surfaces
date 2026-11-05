import LeanModels.Sv.Ingest2
import LeanModels.Sv.Sva
import LeanModels.Sv.Contract

/-!
# SVA properties as E observation contracts

`PProperty` is the source-shaped envelope record.  This bridge keeps that
record beside the structured `SvaCheck` consumed by the finite F1 evaluator;
it does not parse or discard the retained source text.  A caller supplies the
structured body after the frontend has admitted it, and the constructor checks
that the retained assertion kind and clock agree with the check.  Unsupported
source syntax therefore remains a loud boundary at that elaboration step.
-/

namespace LeanModels.Sv

open LeanModels.Sv.Observe

structure SvaContract where
  source : PProperty
  check : SvaCheck

namespace SvaContract

private def kindName : SvaKind → String
  | .assert => "assert"
  | .assume => "assume"
  | .cover => "cover"

def ofCheck (source : PProperty) (check : SvaCheck) : Except String SvaContract := do
  if source.kind != kindName check.kind then
    .error s!"SVA property '{source.name}': source kind '{source.kind}' disagrees with structured check"
  match source.clock with
  | none => .error s!"SVA property '{source.name}': missing clock"
  | some clock =>
      if clock != check.clock then
        .error s!"SVA property '{source.name}': source clock '{clock}' disagrees with structured check clock '{check.clock}'"
      else
        .ok { source, check }

/-! ## Source parser: the first retained F1 production

This parser deliberately admits one complete source form and refuses the rest:
`<kind> property (@(posedge clk) a |-> b);`, where `a`, `b`, and `clk` are
simple signal names.  Keeping the parser here makes the source-to-contract
boundary explicit while the broader `Sv.Ast` property grammar is still being
specified.
-/

private def simpleAtom (text : String) : Except String SvaBool :=
  let n := text.trimAscii.toString
  if n.isEmpty || n.any (fun c => c == ' ' || c == '\n' || c == '\t' || c == '(' || c == ')') then
    .error "SVA: simple implication operands must be signal names"
  else .ok (.signal n)

private def simpleKind (kind : String) : Except String SvaKind :=
  match kind with
  | "assert" => .ok .assert
  | "assume" => .ok .assume
  | "cover" => .ok .cover
  | _ => .error s!"SVA: unsupported property kind '{kind}'"

def parseSimple (source : PProperty) : Except String SvaContract := do
  let text := source.text.trimAscii.toString
  let kindName ←
    if text.startsWith "assert property" then pure "assert"
    else if text.startsWith "assume property" then pure "assume"
    else if text.startsWith "cover property" then pure "cover"
    else throw "SVA: expected assert/assume/cover property"
  let kind ← simpleKind kindName
  let some clockText := source.clock
    | throw "SVA: simple property is missing its retained clock"
  let clock := clockText.trimAscii.toString
  if !text.contains "@(posedge " ||
      (!text.contains "|->" && !text.contains "|=>") || !text.endsWith ");" then
    throw "SVA: unsupported property syntax (expected posedge implication form)"
  let edgeParts := text.splitOn "@(posedge "
  let edgeTail := edgeParts.getLast!
  let afterEdge := edgeTail.splitOn ")"
  let parsedClock := afterEdge.head!.trimAscii.toString
  if parsedClock != clock then
    throw s!"SVA: retained clock '{clock}' disagrees with source clock '{parsedClock}'"
  let some bodyText := afterEdge[1]?
    | throw "SVA: missing implication body"
  let body := bodyText.trimAscii.toString
  let operator := if body.contains "|=>" then "|=>" else "|->"
  let implication := body.splitOn operator
  match implication with
  | [antecedent, consequent] =>
      let left ← simpleAtom antecedent
      let right ← simpleAtom consequent
      let check : SvaCheck :=
        { kind := kind, clock := clock,
          property := if operator == "|=>"
            then .nonoverlap (.atom left) (.atom right)
            else .implies (.atom left) (.atom right) }
      ofCheck source check
  | _ => throw "SVA: expected exactly one implication"

def portRegionAux : Nat → List (CycleObs PortSample) → RegionTrace
  | _, [] => []
  | n, o :: os =>
      { time := n, sampled := o.pre.vals, final := o.post.vals } :: portRegionAux (n + 1) os

/-- Turn the trusted pre/post cycle observations into the E slot view consumed
by concurrent properties.  The property sees only declared ports. -/
def portRegion (b : List (CycleObs PortSample)) : RegionTrace :=
  portRegionAux 0 b

def eval (C : SvaContract) (b : List (CycleObs PortSample)) : Except String Bool :=
  C.check.evalRegion (portRegion b)

def holds (C : SvaContract) (b : List (CycleObs PortSample)) : Prop :=
  C.eval b = .ok true

theorem holds_iff_evalRegion (C : SvaContract) (b : List (CycleObs PortSample)) :
    C.holds b ↔ C.eval b = .ok true := by rfl

/-! An observation-model safety wrapper.  The generic backend inclusion
theorems can now transport an SVA contract without exposing the backend's
internal `Probe` or scheduler state. -/

def Safe (C : SvaContract) {M : ObservationModel} (k : Clocking) (d : M.Design) : Prop :=
  ObservationModel.Safe M k d (fun _ b => C.holds b)

theorem safe_of_included {M₁ M₂ : ObservationModel} {d₁ : M₁.Design} {d₂ : M₂.Design}
    (C : SvaContract) {k : Clocking}
    (hinc : Included M₁ M₂ k d₁ d₂) (h : C.Safe k d₂) : C.Safe k d₁ :=
  Safe.of_included hinc h

end SvaContract

private def sourceProperty : PProperty :=
  { name := "p_ab", kind := "assert", clock := some "clk",
    text := "assert property (@(posedge clk) a |-> b);" }

private def sourceCheck : SvaCheck :=
  { kind := .assert, clock := "clk",
    property := .implies (.atom (.signal "a")) (.atom (.signal "b")) }

private def portTrace : List (CycleObs PortSample) :=
  [ { pre := { vals := [("clk", LVec.ofNat 1 0), ("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 0)] },
      post := { vals := [("clk", LVec.ofNat 1 0), ("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 0)] } }
  , { pre := { vals := [("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 1 1), ("b", LVec.ofNat 1 1)] },
      post := { vals := [("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 1 1), ("b", LVec.ofNat 1 1)] } } ]

#guard (SvaContract.ofCheck sourceProperty sourceCheck).toOption.isSome
#guard match SvaContract.parseSimple sourceProperty with
  | .ok _ => true
  | .error _ => false
#guard match SvaContract.ofCheck sourceProperty sourceCheck with
  | .ok C => match C.eval portTrace with
    | .ok true => true
    | _ => false
  | .error _ => false
#guard match SvaContract.ofCheck { sourceProperty with kind := "cover" } sourceCheck with
  | .error _ => true
  | .ok _ => false
#guard match SvaContract.ofCheck { sourceProperty with clock := none } sourceCheck with
  | .error _ => true
  | .ok _ => false
#guard match SvaContract.parseSimple { sourceProperty with text := "assert property (@(posedge clk) a ##1 b);" } with
  | .error _ => true
  | .ok _ => false
#guard match SvaContract.parseSimple
    { sourceProperty with text := "assert property (@(posedge clk) a |=> b);" } with
  | .ok C => match C.check.property with
    | .nonoverlap _ _ => true
    | _ => false
  | .error _ => false

end LeanModels.Sv

#print axioms LeanModels.Sv.SvaContract.holds_iff_evalRegion
