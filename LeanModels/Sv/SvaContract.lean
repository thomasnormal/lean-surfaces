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

/-! ## Structured property-to-E conversion

The extractor has already parsed the Slang assertion tree.  This bridge only
instantiates its `PExpr` leaves into `Expr2`; it never inspects source text.
-/

def instantiateExpr (env : IEnv) (elems : List (String × Nat)) (value : PExpr) : Expr2 :=
  -- SVA leaves are self-determined expressions. Supplying that width as the
  -- instantiation context preserves ordinary identifiers while giving
  -- unbased unsized fills (`'0`, `'1`, `'x`, `'z`) their required width.
  let allElems := elems ++ env.widths
  instExpr2 env allElems (selfWidth2 env allElems value) value

def svaValueWidth (env : IEnv) (elems : List (String × Nat)) : PSvaValue → Option Nat :=
  let allElems := elems ++ env.widths
  let rec width : PSvaValue → Option Nat
    | .current value | .past _ value => selfWidth2 env allElems value
    | .binary _ left right =>
      match width left, width right with
      | some a, some b => some (max a b)
      | some a, none => some a
      | none, some b => some b
      | none, none => none
  width

def instantiateValueAt (env : IEnv) (elems : List (String × Nat))
    (ctx : Option Nat) : PSvaValue → SvaValue := by
  let allElems := elems ++ env.widths
  let rec go : PSvaValue → SvaValue
    | .current value => .current (instExpr2 env allElems ctx value)
    | .past cycles value => .past cycles (instExpr2 env allElems ctx value)
    | .binary op left right => .binary op (go left) (go right)
  exact go

def instantiateValue (env : IEnv) (elems : List (String × Nat)) (value : PSvaValue) : SvaValue :=
  instantiateValueAt env elems (svaValueWidth env elems value) value

def instantiateBool (env : IEnv) (elems : List (String × Nat)) : PSvaBool → Except String SvaBool
  | .expr value => .ok (.expr (instantiateExpr env elems value))
  | .valueEq left right =>
      let ctx := (svaValueWidth env elems left).orElse (fun _ => svaValueWidth env elems right)
      .ok (.valueEq (instantiateValueAt env elems ctx left)
        (instantiateValueAt env elems ctx right))
  | .past cycles value => .ok (.past cycles (.expr (instantiateExpr env elems value)))
  | .rose value => .ok (.roseExpr (instantiateExpr env elems value))
  | .fell value => .ok (.fellExpr (instantiateExpr env elems value))
  | .stable value => .ok (.stableExpr (instantiateExpr env elems value))

def instantiateSeq (env : IEnv) (elems : List (String × Nat)) : PSvaSeq → Except String SvaSeq
  | .atom test => .atom <$> instantiateBool env elems test
  | .delay cycles body => .delay cycles <$> instantiateSeq env elems body
  | .range lo hi body => .range lo hi <$> instantiateSeq env elems body
  | .concat left right => .concat <$> instantiateSeq env elems left <*> instantiateSeq env elems right

def instantiateProp (env : IEnv) (elems : List (String × Nat)) : PSvaProp → Except String SvaProp
  | .always body => .always <$> instantiateSeq env elems body
  | .implies left right => .implies <$> instantiateSeq env elems left <*> instantiateSeq env elems right
  | .nonoverlap left right => .nonoverlap <$> instantiateSeq env elems left <*> instantiateSeq env elems right
  | .disable guard body => .disable <$> instantiateBool env elems guard <*> instantiateProp env elems body

private def instantiateKind : PSvaKind → SvaKind
  | .assert => .assert
  | .assume => .assume
  | .cover => .cover

private def instantiateEdge : PSvaEdge → String
  | .posedge => "posedge"
  | .negedge => "negedge"
  | .any => "any"

def ofProperty (env : IEnv) (elems : List (String × Nat))
    (source : PProperty) : Except String SvaContract := do
  let some ast := source.ast
    | throw s!"SVA property '{source.name}': missing structured Slang AST"
  let property ← instantiateProp env elems ast.property
  let check : SvaCheck :=
    { kind := instantiateKind ast.kind
      clock := ast.clock
      edge := instantiateEdge ast.edge
      property := property }
  ofCheck source check

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
    text := "assert property (@(posedge clk) a |-> b);",
    ast := some {
      kind := .assert, edge := .posedge, clock := "clk",
      property := .implies
        (.atom (.expr (.ident "a")))
        (.atom (.expr (.ident "b"))) } }

private def sourceCheck : SvaCheck :=
  { kind := .assert, clock := "clk",
    property := .implies (.atom (.signal "a")) (.atom (.signal "b")) }

private def portTrace : List (CycleObs PortSample) :=
  [ { pre := { vals := [("clk", LVec.ofNat 1 0), ("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 0)] },
      post := { vals := [("clk", LVec.ofNat 1 0), ("a", LVec.ofNat 1 0), ("b", LVec.ofNat 1 0)] } }
  , { pre := { vals := [("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 1 1), ("b", LVec.ofNat 1 1)] },
      post := { vals := [("clk", LVec.ofNat 1 1), ("a", LVec.ofNat 1 1), ("b", LVec.ofNat 1 1)] } } ]

#guard (SvaContract.ofCheck sourceProperty sourceCheck).toOption.isSome
#guard match SvaContract.ofProperty ({} : IEnv) [] sourceProperty with
  | .ok C => C.check.kind == .assert && C.check.edge == "posedge"
  | .error _ => false
#guard match SvaContract.ofProperty ({} : IEnv) [] sourceProperty with
  | .ok C => match C.check.property with
    | .implies (.atom (.expr (.ident "a"))) (.atom (.expr (.ident "b"))) => true
    | _ => false
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

end LeanModels.Sv

#print axioms LeanModels.Sv.SvaContract.holds_iff_evalRegion
