import LeanModels.Sv.Regions
import LeanModels.Sv.Pure2

/-!
# F1 — the finite SVA safety fragment over E samples

This is a retained property envelope. It does not add a `Stmt2` constructor or
rewrite a procedural body. A frontend may keep an assertion in this shape until
the full `Sv.Ast` property vocabulary is available; the evaluator below gives
the retained shape its exact finite-trace meaning.

The input to `runRegion` is a `RegionTrace`. `clockSamples` selects the
Preponed samples at `posedge` events, and the property evaluator then works on
that edge trace. There is no semantic fuel: every recursion is over the
property tree, a finite delay range written in the property, or the supplied
trace. Unbounded and liveness operators are intentionally absent and therefore
remain a loud frontend boundary.
-/

namespace LeanModels.Sv

set_option autoImplicit false

/-! ## Retained boolean and sequence vocabulary -/

/-- The boolean portion of the F1 SVA envelope. `past`, `rose`, `fell`, and
`stable` are sampled at the edge-trace index, not at an arbitrary active-region
state. -/
inductive SvaBool where
  | lit (value : Bool)
  | signal (name : String)
  | expr (value : Expr2)
  | not (arg : SvaBool)
  | and (left right : SvaBool)
  | or (left right : SvaBool)
  | caseEq (left right : SvaBool)
  | past (cycles : Nat) (arg : SvaBool)
  | rose (name : String)
  | fell (name : String)
  | stable (name : String)
  | roseExpr (value : Expr2)
  | fellExpr (value : Expr2)
  | stableExpr (value : Expr2)
deriving Repr, Inhabited

/-- A finite sequence expression. `delay n` is `##n`; `range lo hi` is
`##[lo:hi]`. -/
inductive SvaSeq where
  | atom (test : SvaBool)
  | delay (cycles : Nat) (body : SvaSeq)
  | range (lo hi : Nat) (body : SvaSeq)
  | concat (left right : SvaSeq)
deriving Repr, Inhabited

/-- A safety property sampled once per clock edge. `implies` is `|->`, while
`nonoverlap` is `|=>`. `disable` is the retained `disable iff` wrapper. -/
inductive SvaProp where
  | always (body : SvaSeq)
  | implies (antecedent consequent : SvaSeq)
  | nonoverlap (antecedent consequent : SvaSeq)
  | disable (guard : SvaBool) (body : SvaProp)
deriving Repr, Inhabited

inductive SvaKind where
  | assert
  | assume
  | cover
deriving Repr, BEq, DecidableEq, Inhabited

/-- A concurrent check, retained with its clock and optional reset guard. -/
structure SvaCheck where
  kind : SvaKind
  clock : String
  edge : String := "posedge"
  disable : Option SvaBool := none
  property : SvaProp
deriving Repr, Inhabited

/-! ## Sampling -/

/-- A missing signal is an error once a sample exists. A sample outside the
finite trace is represented by `none` and simply cannot satisfy a sequence. -/
def signalAt (trace : List SvState) (index : Nat) (name : String) : Except String (Option LVec) :=
  match trace[index]? with
  | none => .ok none
  | some state =>
      match SvState.lookup state name with
      | some value => .ok (some value)
      | none => .error s!"SVA: unknown signal '{name}'"

def logicAt (trace : List SvState) (index : Nat) (name : String) : Except String (Option Logic) := do
  return (← signalAt trace index name).map (fun value => value.bits[0]?.getD .lx)

def boolValue (value : Option LVec) : Bool :=
  match value with
  | none => false
  | some bits => bits.condTrue

def caseEqual (left right : Option LVec) : Bool :=
  match left, right with
  | some a, some b => LVec.eqCase a b == .l1
  | _, _ => false

def edgeValue (rises : Logic → Logic → Bool) (trace : List SvState)
    (index : Nat) (name : String) : Except String Bool := do
  let previous ← if index == 0 then pure (some .lx) else logicAt trace (index - 1) name
  let current ← logicAt trace index name
  return match previous, current with
  | some old, some new => rises old new
  | _, _ => false

def exprLogicAt (trace : List SvState) (index : Nat) (value : Expr2) :
    Except String (Option Logic) :=
  match trace[index]? with
  | none => .ok none
  | some state =>
      match evalPure2 state value with
      | .ok v => .ok (some (v.bits[0]?.getD .lx))
      | .timeout => .error "SVA: expression evaluation timed out"
      | .unsupported msg => .error s!"SVA: {msg}"

def edgeExprValue (rises : Logic → Logic → Bool) (trace : List SvState)
    (index : Nat) (value : Expr2) : Except String Bool := do
  let previous ← if index == 0 then pure (some .lx) else exprLogicAt trace (index - 1) value
  let current ← exprLogicAt trace index value
  return match previous, current with
  | some old, some new => rises old new
  | _, _ => false

/-- SVA sampled-value edges are value transitions to 1/0 (§16.9.3), rather
than event-control edges: 0->x and 0->z are not `$rose`, and the first sample
uses the default x value. -/
def svaRose (old new : Logic) : Bool := new == .l1 && old != .l1
def svaFell (old new : Logic) : Bool := new == .l0 && old != .l0

/-!
The `caseEq` constructor is intentionally a signal-oriented first fragment:
its operands must both be `signal` nodes. Other forms remain a named error,
rather than evaluating an invented expression language.
-/
def SvaBool.evalChecked (trace : List SvState) (index : Nat) : SvaBool → Except String Bool
  | .caseEq (.signal left) (.signal right) =>
      return caseEqual (← signalAt trace index left) (← signalAt trace index right)
  | .caseEq _ _ => .error "SVA: case equality currently requires signal operands"
  | .lit value => .ok value
  | .signal name => boolValue <$> signalAt trace index name
  | .expr value => do
      match (← exprLogicAt trace index value) with
      | some .l1 => .ok true
      | some .l0 => .ok false
      | some .lx | some .lz =>
          .error "SVA: boolean expression evaluated to unknown; require a known sampled decision"
      | none => .ok false
  | .not (.signal name) => do
      match (← logicAt trace index name) with
      | some .l0 => .ok true
      | some .l1 => .ok false
      | some .lx | some .lz =>
          .error "SVA: negation operand evaluated to unknown; require a known sampled decision"
      | none => .ok false
  | .not arg => return !(← arg.evalChecked trace index)
  | .and left right => return (← left.evalChecked trace index) && (← right.evalChecked trace index)
  | .or left right => return (← left.evalChecked trace index) || (← right.evalChecked trace index)
  | .past cycles arg =>
      if cycles ≤ index then arg.evalChecked trace (index - cycles)
      else .error "SVA: $past reads the default unknown sampled value"
  | .rose name => edgeValue svaRose trace index name
  | .fell name => edgeValue svaFell trace index name
  | .roseExpr value => edgeExprValue svaRose trace index value
  | .fellExpr value => edgeExprValue svaFell trace index value
  | .stableExpr value =>
      if index == 0 then
        .error "SVA: $stable reads the default unknown sampled value"
      else do
        let previous ← exprLogicAt trace (index - 1) value
        let current ← exprLogicAt trace index value
        match previous, current with
        | some old, some new =>
            if old.isKnown && new.isKnown then .ok (old == new)
            else .error "SVA: $stable reads an unknown sampled value"
        | _, _ => .ok false
  | .stable name =>
      if index == 0 then .ok false
      else do
        let previous ← signalAt trace (index - 1) name
        let current ← signalAt trace index name
        return caseEqual previous current

/-! ## Finite sequence and property evaluation -/

def SvaSeq.matches (trace : List SvState) (index : Nat) : SvaSeq → Except String Bool
  | .atom test => test.evalChecked trace index
  | .delay cycles body => body.matches trace (index + cycles)
  | .concat left right => do
      if ← left.matches trace index then right.matches trace (index + 1) else .ok false
  | .range lo hi body =>
      if hi < lo then
        .error "SVA: descending ## range"
      else
        rangeMatches trace index lo body hi
where
  /-- Scan a written finite range by structural recursion on its upper bound. -/
  rangeMatches (trace : List SvState) (index lo : Nat) (body : SvaSeq) : Nat → Except String Bool
    | 0 =>
        if lo == 0 then body.matches trace index else .ok false
    | hi + 1 =>
        if lo > hi + 1 then .ok false
        else do
          let hit ← body.matches trace (index + hi + 1)
          if hit then .ok true else rangeMatches trace index lo body hi

def allAt (trace : List SvState) (start : Nat)
    (test : Nat → Except String Bool) : List SvState → Except String Bool
  | [] => .ok true
  | _ :: rest => do
      if ← test start then allAt trace (start + 1) test rest else .ok false

def anyAt (trace : List SvState) (start : Nat)
    (test : Nat → Except String Bool) : List SvState → Except String Bool
  | [] => .ok false
  | _ :: rest => do
      if ← test start then .ok true else anyAt trace (start + 1) test rest

def SvaProp.at (trace : List SvState) (index : Nat) : SvaProp → Except String Bool
  | .always body => body.matches trace index
  | .implies antecedent consequent => do
      if ← antecedent.matches trace index then consequent.matches trace index else .ok true
  | .nonoverlap antecedent consequent => do
      if ← antecedent.matches trace index then consequent.matches trace (index + 1) else .ok true
  | .disable guard body => do
      if ← guard.evalChecked trace index then .ok true else body.at trace index

def SvaProp.holds (trace : List SvState) (property : SvaProp) : Except String Bool :=
  allAt trace 0 (property.at trace) trace

def SvaCheck.step (trace : List SvState) (check : SvaCheck) (index : Nat) : Except String Bool := do
  match check.disable with
  | some guard =>
      if ← guard.evalChecked trace index then return true
  | none => pure ()
  check.property.at trace index

def SvaCheck.evalEdges (edges : List SvState) (check : SvaCheck) : Except String Bool :=
  match check.kind with
  | .cover => anyAt edges 0 (fun index => SvaCheck.step edges check index) edges
  | .assert | .assume => allAt edges 0 (fun index => SvaCheck.step edges check index) edges

/-! Select Preponed samples at a named positive clock edge.  The worker is
over sampled states directly, making final-state irrelevance explicit. -/
def clockSamplesFrom (clock edge : String) (previous : Logic) :
    List SvState → List SvState → Except String (List SvState)
  | [], selected => .ok selected.reverse
  | sampled :: rest, selected => do
      let now := (← logicAt [sampled] 0 clock).getD .lx
      let hit := if edge == "posedge" then isPosedge previous now
        else if edge == "negedge" then isNegedge previous now
        else true
      let selected' := if hit then sampled :: selected else selected
      clockSamplesFrom clock edge now rest selected'

def clockSamples (clock : String) (trace : RegionTrace) : Except String (List SvState) :=
  clockSamplesFrom clock "posedge" .lx (trace.map (·.sampled)) []

def clockSamplesEdge (clock edge : String) (trace : RegionTrace) : Except String (List SvState) :=
  clockSamplesFrom clock edge .lx (trace.map (·.sampled)) []

def SvaCheck.evalRegion (trace : RegionTrace) (check : SvaCheck) : Except String Bool := do
  check.evalEdges (← clockSamplesEdge check.clock check.edge trace)

/-- Concurrent properties consume the Preponed sample only.  Replacing every
slot's final state therefore cannot change the selected edge samples; this
is the small refinement fact that lets an E contract expose only its sampled
cycle view to SVA. -/
theorem clockSamples_final_irrel (clock : String) (trace : RegionTrace) :
    clockSamples clock trace =
      clockSamples clock (trace.map fun slot => { slot with final := slot.sampled }) := by
  simp only [clockSamples, List.map_map]
  rfl

theorem clockSamplesEdge_final_irrel (clock edge : String) (trace : RegionTrace) :
    clockSamplesEdge clock edge trace =
      clockSamplesEdge clock edge (trace.map fun slot => { slot with final := slot.sampled }) := by
  simp only [clockSamplesEdge, List.map_map]
  rfl

theorem evalRegion_final_irrel (trace : RegionTrace) (check : SvaCheck) :
    check.evalRegion trace =
      check.evalRegion (trace.map fun slot => { slot with final := slot.sampled }) := by
  unfold SvaCheck.evalRegion
  rw [clockSamplesEdge_final_irrel]

/-! ## Kernel-reducible witnesses for the F1 fragment -/

private def svaState (clk a b : Logic) : SvState :=
  [("clk", LVec.ofLogic clk), ("a", LVec.ofLogic a), ("b", LVec.ofLogic b)]

private def svaTrace : RegionTrace :=
  [ { time := 0, sampled := svaState .l0 .l0 .l0, final := svaState .l0 .l0 .l0 }
  , { time := 1, sampled := svaState .l1 .l1 .l1, final := svaState .l1 .l1 .l1 }
  , { time := 2, sampled := svaState .l0 .l1 .l0, final := svaState .l0 .l1 .l0 }
  , { time := 3, sampled := svaState .l1 .l0 .l0, final := svaState .l1 .l0 .l0 }
  , { time := 4, sampled := svaState .l0 .l0 .l0, final := svaState .l0 .l0 .l0 }
  , { time := 5, sampled := svaState .l1 .l1 .l1, final := svaState .l1 .l1 .l1 } ]

private def svaTraceFinalChanged : RegionTrace :=
  svaTrace.map fun slot => { slot with final := [] }

private def svaImplication : SvaCheck :=
  { kind := .assert, clock := "clk"
    property := .implies (.atom (.signal "a")) (.atom (.signal "b")) }

private def svaPast : SvaCheck :=
  { kind := .assert, clock := "clk"
    property := .always (.atom (.or (.past 1 (.signal "a")) (.signal "a"))) }

private def svaCover : SvaCheck :=
  { kind := .cover, clock := "clk"
    property := .always (.range 0 1 (.atom (.rose "a"))) }

#guard (SvaCheck.evalRegion svaTrace svaImplication).toOption == some true
#guard (SvaCheck.evalRegion svaTrace svaPast).toOption.isNone
#guard (SvaCheck.evalRegion svaTrace svaCover).toOption == some true
#guard match SvaBool.evalChecked [svaState .l0 .lx .l0] 0 (.not (.signal "a")) with
  | .error _ => true
  | .ok _ => false
#guard (SvaBool.evalChecked [svaState .l0 .l1 .l0] 0 (.rose "a")).toOption == some true
#guard (SvaBool.evalChecked [svaState .l0 .l0 .l0, svaState .l0 .lx .l0] 1 (.rose "a")).toOption == some false
#guard (SvaBool.evalChecked [svaState .l0 .l1 .l0, svaState .l0 .lx .l0] 1 (.fell "a")).toOption == some false
#guard match SvaBool.evalChecked [svaState .l0 .l1 .l0] 0
  (.past 1 (.expr (.ident "a"))) with
  | .error _ => true
  | .ok _ => false
#guard match SvaBool.evalChecked [svaState .l0 .lx .l0] 0
  (.stableExpr (.ident "a")) with
  | .error _ => true
  | .ok _ => false
#guard (SvaSeq.matches [svaState .l1 .l1 .l0] 0 (.delay 1 (.atom (.signal "a")))).toOption == some false
#guard (SvaCheck.evalRegion svaTrace svaImplication).toOption ==
  (SvaCheck.evalRegion svaTraceFinalChanged svaImplication).toOption

end LeanModels.Sv
