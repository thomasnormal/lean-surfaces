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

/-! A sampled value may read the current expression, a finite `$past`, or
combine two such values with an ordinary arithmetic operator.  Keeping this
tree separate from `Expr2` prevents a previous-cycle read from becoming a
live signal lookup. -/
inductive SvaValue where
  | current (value : Expr2)
  | past (cycles : Nat) (value : Expr2)
  | countOnes (value : Expr2)
  /-- A parameter-sized cast after the parameter point has been selected.
      `none` is retained as a loud unbound/invalid-width boundary. -/
  | paramCast (width : Option Nat) (value : SvaValue)
  | binary (op : BinOp) (left right : SvaValue)
deriving Repr, Inhabited

/-- The boolean portion of the F1 SVA envelope. `past`, `rose`, `fell`, and
`stable` are sampled at the edge-trace index, not at an arbitrary active-region
state. -/
inductive SvaBool where
  | lit (value : Bool)
  | signal (name : String)
  | expr (value : Expr2)
  | valueEq (left right : SvaValue)
  | not (arg : SvaBool)
  | and (left right : SvaBool)
  | or (left right : SvaBool)
  | isUnknown (value : Expr2)
  | oneHot0 (value : Expr2)
  | valueCmp (op : BinOp) (left right : SvaValue)
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

/-! The endpoint offset of a finite sequence. Ranges use their upper
endpoint; the admitted fragment does not place another sequence after a
range, while this definition keeps concatenation structural and fuel-free. -/
def SvaSeq.endOffset : SvaSeq → Nat
  | .atom _ => 0
  | .delay cycles body => cycles + body.endOffset
  | .range _ hi body => hi + body.endOffset
  | .concat left right => left.endOffset + right.endOffset

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
/-! SVA's sampled boolean conversion is 4-state until the assertion result is
observed: an unknown expression is converted to false at the property boundary
(IEEE 1800-2023 §16.6).  Keeping the intermediate `Logic` value is essential
for `!x`, `$past`, and the sampled edge functions; converting each leaf to
`Bool` would turn `!x` into a false positive. -/

def boolLogic (value : LVec) : Logic :=
  if value.condTrue then .l1 else if value.isKnownZero then .l0 else .lx

def exprAt (trace : List SvState) (index : Nat) (value : Expr2) :
    Except String (Option LVec) :=
  match trace[index]? with
  | none => .ok none
  | some state =>
      match evalPure2 state value with
      | .ok v => .ok (some v)
      | .timeout => .error "SVA: expression evaluation timed out"
      | .unsupported msg => .error s!"SVA: {msg}"

def signalStable (trace : List SvState) (index : Nat) (name : String) : Except String Bool :=
  if index == 0 then .ok false
  else return caseEqual (← signalAt trace (index - 1) name) (← signalAt trace index name)

def exprStable (trace : List SvState) (index : Nat) (value : Expr2) : Except String Bool :=
  if index == 0 then .ok false
  else return caseEqual (← exprAt trace (index - 1) value) (← exprAt trace index value)

def SvaValue.eval (trace : List SvState) (index : Nat) : SvaValue →
    Except String (Option LVec)
  | .current value => exprAt trace index value
  | .past cycles value =>
      if cycles ≤ index then exprAt trace (index - cycles) value else .ok none
  | .countOnes value => do
      let some v ← exprAt trace index value | .ok none
      .ok (some (LVec.ofNat 32 (v.bits.toList.countP (fun b => b == Logic.l1))))
  | .paramCast none _ => .error "SVA: parameter-sized cast has no concrete width"
  | .paramCast (some width) value => do
      let some v ← value.eval trace index | .ok none
      .ok (some (v.resizeU width))
  | .binary op left right => do
      let some l ← left.eval trace index | .ok none
      let some r ← right.eval trace index | .ok none
      .ok (some (evalBinOp op l r))

def SvaBool.evalLogic (trace : List SvState) (index : Nat) : SvaBool → Except String (Option Logic)
  | .caseEq (.signal left) (.signal right) =>
      return some (if caseEqual (← signalAt trace index left) (← signalAt trace index right)
        then .l1 else .l0)
  | .caseEq _ _ => .error "SVA: case equality currently requires signal operands"
  | .valueEq left right => do
      let some l ← left.eval trace index | .ok none
      let some r ← right.eval trace index | .ok none
      let width := max l.width r.width
      return some (LVec.eqLogical (l.resizeU width) (r.resizeU width))
  | .isUnknown value => do
      let some v ← exprAt trace index value | .ok none
      return some (if v.allKnown then .l0 else .l1)
  | .oneHot0 value => do
      let some v ← exprAt trace index value | .ok none
      let ones := v.bits.toList.countP (fun b => b == Logic.l1)
      return some (if v.allKnown then
        if ones ≤ 1 then .l1 else .l0
      else if ones > 1 then .l0 else .lx)
  | .valueCmp op left right => do
      let some l ← left.eval trace index | .ok none
      let some r ← right.eval trace index | .ok none
      return some (boolLogic (evalBinOp op l r))
  | .lit value => .ok (some (if value then .l1 else .l0))
  | .signal name => return (← signalAt trace index name).map boolLogic
  | .expr value => return (← exprAt trace index value).map boolLogic
  | .not arg => return (← arg.evalLogic trace index).map (fun v => Logic.not v)
  | .and left right => do
      let l ← left.evalLogic trace index
      let r ← right.evalLogic trace index
      return match l, r with
      | some a, some b => some (Logic.and a b)
      | _, _ => none
  | .or left right => do
      let l ← left.evalLogic trace index
      let r ← right.evalLogic trace index
      return match l, r with
      | some a, some b => some (Logic.or a b)
      | _, _ => none
  | .past cycles arg =>
      if cycles ≤ index then arg.evalLogic trace (index - cycles) else .ok (some .lx)
  | .rose name => do
      let hit ← edgeValue svaRose trace index name
      return some (if hit then .l1 else .l0)
  | .fell name => do
      let hit ← edgeValue svaFell trace index name
      return some (if hit then .l1 else .l0)
  | .roseExpr value => do
      let hit ← edgeExprValue svaRose trace index value
      return some (if hit then .l1 else .l0)
  | .fellExpr value => do
      let hit ← edgeExprValue svaFell trace index value
      return some (if hit then .l1 else .l0)
  | .stableExpr value => do
      let hit ← exprStable trace index value
      return some (if hit then .l1 else .l0)
  | .stable name => do
      let hit ← signalStable trace index name
      return some (if hit then .l1 else .l0)

/-- Apply §16.6's x/z-as-false conversion once, at the assertion boundary. -/
def SvaBool.evalChecked (trace : List SvState) (index : Nat) (value : SvaBool) :
    Except String Bool := do
  return match ← value.evalLogic trace index with
  | some .l1 => true
  | _ => false

/-! ## Finite sequence and property evaluation -/

def SvaSeq.matches (trace : List SvState) (index : Nat) : SvaSeq → Except String Bool
  | .atom test => test.evalChecked trace index
  | .delay cycles body => body.matches trace (index + cycles)
  | .concat left right => do
      -- A delayed sequence element already carries its `##n` offset.  Start
      -- the right-hand sequence after the left sequence's endpoint, rather
      -- than adding an unconditional extra cycle: `a ##1 b` is represented
      -- as `concat a (delay 1 b)`, so the delay must be counted exactly once.
      if ← left.matches trace index then
        right.matches trace (index + left.endOffset) else .ok false
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
#guard (SvaCheck.evalRegion svaTrace svaPast).toOption == some true
#guard (SvaCheck.evalRegion svaTrace svaCover).toOption == some true
#guard (SvaBool.evalChecked [svaState .l0 .lx .l0] 0 (.not (.signal "a"))).toOption == some false
#guard (SvaBool.evalChecked [svaState .l0 .l1 .l0] 0 (.rose "a")).toOption == some true
#guard (SvaBool.evalChecked [svaState .l0 .l0 .l0] 0 (.fell "a")).toOption == some true
#guard (SvaBool.evalChecked [svaState .l0 .lx .l0, svaState .l0 .l1 .l0] 1 (.rose "a")).toOption == some true
#guard (SvaBool.evalChecked [svaState .l0 .lx .l0, svaState .l0 .l0 .l0] 1 (.fell "a")).toOption == some true
#guard (SvaBool.evalChecked [svaState .l0 .l0 .l0, svaState .l0 .l1 .l0] 1 (.rose "a")).toOption == some true
#guard (SvaBool.evalChecked [svaState .l0 .l0 .l0, svaState .l0 .lx .l0] 1 (.rose "a")).toOption == some false
#guard (SvaBool.evalChecked [svaState .l0 .l1 .l0, svaState .l0 .lx .l0] 1 (.fell "a")).toOption == some false
#guard (SvaBool.evalChecked [svaState .l0 .l1 .l0] 0
  (.past 1 (.expr (.ident "a")))).toOption == some false
#guard (SvaBool.evalChecked [svaState .l0 .lx .l0] 0
  (.stableExpr (.ident "a"))).toOption == some false
#guard (SvaSeq.matches [svaState .l1 .l1 .l0] 0 (.delay 1 (.atom (.signal "a")))).toOption == some false
#guard (SvaCheck.evalRegion svaTrace svaImplication).toOption ==
  (SvaCheck.evalRegion svaTraceFinalChanged svaImplication).toOption

end LeanModels.Sv
