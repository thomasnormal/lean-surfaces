import Lean
import LeanModels.Sv.Semantics
import LeanModels.Sv.Sem2
import LeanModels.Sv.Param
import LeanModels.Sv.FormattedInput
import LeanModels.Sv.Plusargs

/-!
# SV self-check tier (`LeanModels.Sv.SelfCheck`)

Executes the *self-check* slice of the IEEE 1800 conformance corpus
(sv-tests-2): single-module designs whose only processes are `initial`
blocks that compute at time 0 and print `PASS`/`FAIL` via `$display`.
Vocabulary: the M0 tier plus the §f extensions of
`docs/sv-corpus-coverage.md` — `initial`, `$display`/`$write`/`$finish`/
`$stop`, string-literal constants, local variable declarations
(unsigned 4-state or 2-state), case equality `===`/`!==`, logical
`&&`/`||`, signed order comparisons (`s<` …), zero-extend/truncate
`Resize`, and the 4-state→2-state `Squash2` conversion.

## Relationship to the M0 core (deliberate wrapper, not a rewrite)

`Ast.Expr`/`Ast.Stmt` are closed inductives that the M0 interpreter and
proofs match exhaustively, so this tier does NOT add constructors to them.
Instead `SExpr`/`SStmt` **embed** the M0 types as leaves (`.m0`): the JSON
parser collapses every pure-M0 subtree back into a single `.m0` node, and
the evaluators delegate those to the *existing* `evalExpr`/`execStmt`
machinery of `Semantics.lean` — the same `LVec` operator library, state
discipline (`SvState.set`, NBA queue), and fuel discipline (match fuel
first, decrement into every recursive call, siblings share).

## Semantics of a run (`runSelfCheck`)

1. Any process that is not an `initial` block is **loud**
   (`.unsupported`) — always/comb/assign interaction is out of tier
   (conformance tests with an always block are dropped from the runnable
   set, per the tier contract).
2. Module-level declarations initialize in order: variables to their
   initializer else all-x (§6.8), nets to all-z (undriven), 2-state
   variables arrive from the extractor with an explicit 0 initializer.
3. `initial` processes run **once each, to completion, in source order**
   (all at time 0; `#delay` inside a body arrives as `Unsupported` and is
   loud when reached). Blocking assigns hit the state immediately;
   nonblocking assigns queue and would commit in the time-0 NBA region —
   after every initial has finished, hence never observable in output
   (kept for fidelity, not observability).
4. `$display`/`$write` render into an output buffer; lines split on the
   newlines `$display` appends (`$write` does not append one).
5. `$finish`/`$stop` halt the whole run cleanly (remaining statements and
   remaining initial processes are skipped); the collected lines are the
   result.

## Rendering (`%b %h %d %s %c`, plus `%0`-variants)

Ground truth: Xcelium 24.03 (spot-checked 2026-07-21, see
`docs/sv-corpus-coverage.md` §f). Notable LRM/simulator facts encoded in
the `#guard` tests below: `%0b` of an all-x vector is `"x"`; `%h` renders
a nibble with mixed known/unknown bits as `X`; `%d` right-justifies to the
natural decimal width of the *type* (11 chars for signed 32-bit, 10 for
unsigned); `%s` renders NUL bytes as spaces. `SysCall` args carry a
parallel `arg_signed` list, so signed decimal output uses the
two's-complement interpretation rather than its unsigned bit-pattern value.
-/

namespace LeanModels.Sv
namespace SelfCheck

/-! ## Value helpers (on top of `Basic.lean`'s `LVec`) -/

/-- 4-state → 2-state value conversion, LRM §6.3.1: `x`/`z` bits become 0.
Applied wherever the extractor inserted a `Squash2` node (assignments and
initializers whose target is a 2-state variable, and the corresponding
implicit conversions). -/
def squash2v (v : LVec) : LVec :=
  v.toTwoState

/-- Unsigned resize (the `Resize` node): zero-extend on the MSB side, or
keep the low `w` bits. The extractor emits `Resize` for an unsigned
propagated conversion context, where the LRM extension rule is zero-fill
(x/z bits are kept, never extended). -/
def resizeV (w : Nat) (v : LVec) : LVec :=
  if v.width ≥ w then ⟨v.bits.extract 0 w⟩
  else ⟨v.bits ++ Array.replicate (w - v.width) .l0⟩

/-- Most significant bit (`bits` is LSB-first; width 0 ⇒ `l0`). -/
def msb (v : LVec) : Logic := v.bits.back?.getD .l0

/-- Two's-complement value of a fully known vector, else `none`. -/
def toIntS? (v : LVec) : Option Int := do
  let n ← v.toNat?
  return if msb v == .l1 then (n : Int) - ((2 ^ v.width : Nat) : Int) else (n : Int)

/-- Signed relational-op skeleton (mirrors `LVec.relOp`): compare the
two's-complement values when both operands are fully known, else `x`. -/
def scmpOp (cmp : Int → Int → Bool) (a b : LVec) : Logic :=
  match toIntS? a, toIntS? b with
  | some x, some y => if cmp x y then .l1 else .l0
  | _, _ => .lx

/-- Signed `< <= > >=` dispatch (`BinOp` reused as the op vocabulary; the
non-order constructors are unreachable from the parser). -/
def evalScmp : BinOp → LVec → LVec → Logic
  | .lt, a, b => scmpOp (· < ·) a b
  | .le, a, b => scmpOp (· ≤ ·) a b
  | .gt, a, b => scmpOp (· > ·) a b
  | .ge, a, b => scmpOp (· ≥ ·) a b
  | _, _, _ => .lx

/-- Truthiness as a 1-bit `Logic` (LRM §11.4.7 operand conversion for
`&&`/`||`): some `1` bit ⇒ `1`, all-known-zero ⇒ `0`, else `x`. -/
def truthy (v : LVec) : Logic :=
  if v.condTrue then .l1 else if v.isKnownZero then .l0 else .lx

def selectedIndex (signed : Bool) (value : LVec) : Option Int :=
  if signed then toIntS? value else value.toNat?.map Int.ofNat

def selectedRead (width : Nat) (descending indexSigned : Bool)
    (value index : LVec) : LVec :=
  match selectedIndex indexSigned index with
  | none => LVec.xVec width
  | some position =>
      let low := if descending then position - (width : Int) + 1 else position
      ⟨Array.ofFn (n := width) fun offset =>
        let position := low + (offset.val : Int)
        if position < 0 then .lx else value.bits[position.toNat]?.getD .lx⟩

def selectedWrite (width : Nat) (descending indexSigned : Bool)
    (value index replacement : LVec) : LVec :=
  match selectedIndex indexSigned index with
  | none => value
  | some position =>
      let low := if descending then position - (width : Int) + 1 else position
      let replacement := replacement.resizeU width
      if low < 0 then
        let skipped := (-low).toNat
        value.insertAt 0 (replacement.extract skipped (width - skipped))
      else value.insertAt low.toNat replacement

/-- A compound part-select that overlaps storage but is not wholly inside it.
Independent observations disagree on its copyback; this tier refuses it. -/
def partialCompoundSelection (width : Nat) (descending indexSigned : Bool)
    (value index : LVec) : Bool :=
  match selectedIndex indexSigned index with
  | none => false
  | some position =>
      let low := if descending then position - (width : Int) + 1 else position
      let high := low + (width : Int)
      low < (value.width : Int) && 0 < high &&
        (low < 0 || (value.width : Int) < high)

def compoundRead (width : Nat) (descending indexSigned : Bool)
    (value index : LVec) : Res LVec :=
  if partialCompoundSelection width descending indexSigned value index then
    .unsupported "AssignmentExpression:compound-partial-range"
  else .ok (selectedRead width descending indexSigned value index)

abbrev AssignmentOrder := Nat → List Nat

def rightToLeftAssignmentOrder : AssignmentOrder := fun count => (List.range count).reverse

def leftToRightAssignmentOrder : AssignmentOrder := List.range

/-! ## Self-check expressions -/

/-- Self-check expressions: M0 `Expr` embedded as a leaf (`.m0`, evaluated
by the existing `evalExpr` — the parser collapses maximal pure-M0 subtrees
into it) plus the §f extensions. `Expr.unsupported` leaves arrive inside
`.m0` and stay loud. -/
inductive BitQuery where
  | countbits | countones | onehot | onehot0 | isunknown
deriving Repr, BEq, DecidableEq, Inhabited

def countSelected (value : LVec) (controls : List Logic) : Nat :=
  value.bits.foldl (fun count bit => count + if controls.contains bit then 1 else 0) 0

theorem countSelected_duplicate (value : LVec) (control : Logic) :
    countSelected value [control, control] = countSelected value [control] := by
  simp [countSelected]

def evalBitQuery (query : BitQuery) (value : LVec) (controls : List LVec) : LVec :=
  match query with
  | .countbits => .ofNat 32 (countSelected value (controls.map fun control =>
      control.bits[0]?.getD .l0))
  | .countones => .ofNat 32 (countSelected value [.l1])
  | .onehot => .ofLogic (if countSelected value [.l1] == 1 then .l1 else .l0)
  | .onehot0 => .ofLogic (if countSelected value [.l1] ≤ 1 then .l1 else .l0)
  | .isunknown => .ofLogic (if countSelected value [.lx, .lz] > 0 then .l1 else .l0)

/-- IEEE 20.8.1: read the finite vector as unsigned and reuse the shared
ceiling logarithm. Unknown arguments stay loud; no frontend approximation. -/
def evalClog2 (value : LVec) : Res LVec :=
  match value.toNat? with
  | some n => .ok (.ofNat 32 (LeanModels.Sv.clog2 n))
  | none => .unsupported "$clog2 requires a fully known integral argument"

inductive SExpr where
  | m0 (e : Expr)
  | unary (op : UnaryOp) (a : SExpr)
  | binary (op : BinOp) (l r : SExpr)
  /-- Signed order comparison (`s<` `s<=` `s>` `s>=`); `op ∈ {lt,le,gt,ge}`. -/
  | scmp (op : BinOp) (l r : SExpr)
  | caseEq (l r : SExpr)   -- `===`
  | caseNe (l r : SExpr)   -- `!==`
  /-- Symmetric `casez`/`casex` match, after whole-case sizing. -/
  | caseMatch (wildX : Bool) (l r : SExpr)
  | logAnd (l r : SExpr)   -- `&&`
  | logOr (l r : SExpr)    -- `||`
  | resize (w : Nat) (a : SExpr)
  | signedResize (width : Nat) (operand : SExpr)
  | squash2 (a : SExpr)
  | ternary (c t f : SExpr)
  | concat (parts : Array SExpr)
  | selectRead (width : Nat) (descending indexSigned : Bool) (value index : SExpr)
  | compoundRead (width : Nat) (descending indexSigned : Bool) (value index : SExpr)
  | bitQuery (query : BitQuery) (operand : SExpr) (controls : Array SExpr)
  | clog2 (operand : SExpr)
  /-- `$sformatf` with one literal format and one integral operand. The
  formatted text is represented as an ASCII packed vector so ordinary string
  equality keeps the existing pure expression path. -/
  | sformatf (format : String) (operand : SExpr) (signed : Bool)
  /-- One-dimensional fixed-array `%p` text assembled from flat cells. -/
  | arrayDisplay (elements : Array (SExpr × Bool))
  /-- A declaration-order enum `.name()` result. The selected string keeps
  its exact byte width, so `%s` does not inherit padding from another member. -/
  | enumName (subject : SExpr) (cases : Array (LVec × String)) (default : String)
deriving Repr, BEq, Inhabited

/-- Collapse-aware constructors: keep pure-M0 subtrees as single `.m0`
nodes so the M0 interpreter does the bulk of the work. -/
def SExpr.mkUnary (op : UnaryOp) : SExpr → SExpr
  | .m0 e => .m0 (.unary op e)
  | a => .unary op a

def SExpr.mkBinary (op : BinOp) : SExpr → SExpr → SExpr
  | .m0 l, .m0 r => .m0 (.binary op l r)
  | l, r => .binary op l r

def SExpr.mkTernary : SExpr → SExpr → SExpr → SExpr
  | .m0 c, .m0 t, .m0 f => .m0 (.ternary c t f)
  | c, t, f => .ternary c t f

def SExpr.mkConcat (parts : Array SExpr) : SExpr :=
  let m0s := parts.filterMap fun p => match p with | .m0 e => some e | _ => none
  if m0s.size == parts.size then .m0 (.concat m0s) else .concat parts

private def asciiVec (text : String) : LVec :=
  LVec.concatMany (text.toList.toArray.map fun c => LVec.ofNat 8 c.toNat)

/-! ## Self-check statements -/

/-- Edge sensitivity for event control (`@`).

Introduced for R1's scheduler (`docs/sv-r1-scheduler.md` §9.11). The M0
tier has no notion of an edge at all: `Process.alwaysFF (clock : String)`
hardcodes `posedge` and the extractor rejects anything else. So this is a
NEW type rather than a new constructor of an existing one, and nothing
existing matches on it. -/
inductive Edge where
  | pos | neg | any
deriving Repr, BEq, DecidableEq, Inhabited

inductive PackedTarget where
  | whole (name : String) (width : Nat) (twoState : Bool)
  | selected (name : String) (width : Nat)
      (descending indexSigned twoState : Bool) (index : SExpr)
  deriving Repr, BEq, Inhabited

def PackedTarget.width : PackedTarget → Nat
  | .whole _ width _ | .selected _ width _ _ _ _ => width

def packedTargetSlices : List PackedTarget → List (PackedTarget × Nat)
  | [] => []
  | target :: rest =>
      (target, rest.foldl (fun width part => width + part.width) 0) :: packedTargetSlices rest

def validAssignmentOrder (count : Nat) (order : List Nat) : Bool :=
  order.length == count && order.all (· < count) && order.eraseDups.length == count

/-- Self-check statements: M0 `Stmt` embedded as a leaf (`.m0`, executed by
the existing `execStmt`; statement-level `Unsupported` arrives as
`.m0 (.unsupported …)`) plus the §f extensions. `sysCall` args carry the
envelope's `arg_signed` flag. -/
inductive SStmt where
  | m0 (s : Stmt)
  | assign (nonblocking : Bool) (target : String) (value : SExpr)
  | selectedAssign (target : String) (width : Nat)
      (descending indexSigned twoState : Bool) (index value : SExpr)
  | selectedNbaAssign (target : String) (width : Nat)
      (descending indexSigned twoState : Bool) (index value : SExpr)
  /-- One bounded `$dist_uniform` call, including its inout seed update. -/
  | distUniformAssign (target seed : String) (low high : Int) (twoState : Bool)
  | packedAssign (targets : List PackedTarget) (value : SExpr)
  | packedNbaAssign (targets : List PackedTarget) (value : SExpr)
  | scanf (input : SExpr) (format : List FormattedInput.Token)
      (outputs : List (List PackedTarget)) (result : List PackedTarget)
  | ifStmt (cond : SExpr) (thenB : SStmt) (elseB : Option SStmt)
  | block (body : Array SStmt)
  /-- `for` source phases. The extra constructors are also the resumable
  continuation markers used by `Step.lean`; they are not emitted by the
  extractor. -/
  | forLoop (initializers : Array SStmt) (condition : SExpr)
      (steps : Array SStmt) (body : SStmt)
  | forAfterInit (condition : SExpr) (steps : Array SStmt) (body : SStmt)
  | forHeader (condition : SExpr) (steps : Array SStmt) (body : SStmt)
  | forAfterBody (condition : SExpr) (steps : Array SStmt) (body : SStmt)
  | forAfterStep (condition : SExpr) (steps : Array SStmt) (body : SStmt)
  /-- `repeat` samples its count once. `repeatAfterBody` commits one
  iteration only after the body has completed. -/
  | repeatLoop (count : SExpr) (countSigned : Bool) (body : SStmt)
  | repeatBody (remaining : Nat) (body : SStmt)
  | repeatAfterBody (remaining : Nat) (body : SStmt)
  /-- Body-first entry; subsequent tests and iterations use the ordinary
  empty-step `for` control, including its retained body boundary. -/
  | doWhileLoop (condition : SExpr) (body : SStmt)
  | breakLoop
  | continueLoop
  | localDecl (name : String) (width : Nat) (twoState : Bool) (init : Option SExpr)
  /-- `$display` (`write = false`, appends a newline) or `$write`. -/
  | sysCall (write : Bool) (format : Option String) (args : Array (SExpr × Bool))
  /-- `$strobe`: evaluate and emit at the end of the time-zero slot. -/
  | strobe (format : Option String) (args : Array (SExpr × Bool))
  /-- `$monitor`: replace the active registration; the call is sampled in
  the Postponed region and emits only on its first sample or a value change. -/
  | monitor (format : Option String) (args : Array (SExpr × Bool))
  /-- Severity diagnostics evaluate arguments but have no self-check stream. -/
  | severity (args : Array (SExpr × Bool))
  /-- `$fatal` evaluates its arguments, reports outside the self-check stream,
  then halts the run. -/
  | fatal (args : Array (SExpr × Bool))
  | finish  -- `$finish` and `$stop`: halt the run cleanly
  | skip    -- `;` (Empty)
  /-- `#d` — delay control; suspends until `amount` time units pass.

  R1 SUSPENSION FORM. These three constructors are the points at which an
  IEEE 1800 process can pause mid-body. They live on `SStmt` rather than
  on `Ast.Stmt` because `Ast.Stmt` is matched EXHAUSTIVELY by the M0
  interpreter and by the 156-declaration trace-shaped estate, whereas
  `SStmt` is matched in this file alone and carries no proofs
  (`docs/sv-r1-scheduler.md` §9.11).

  They are deliberately NOT executable by `execSStmt`: the self-check tier
  runs at time 0 with no scheduler, so reaching one is out of tier and is
  LOUD — exactly the contract this module's docstring already states for
  `#delay`. The resumable stepper that DOES handle them is
  `LeanModels/Sv/Step.lean`. -/
  | delay (amount : Nat)
  /-- `@(posedge sig)` / `@(negedge sig)` / `@(sig)` — event control.
  R1 suspension form; see `delay`. -/
  | waitEvent (sig : String) (edge : Edge)
  /-- `wait (cond)` — level-sensitive wait. R1 suspension form; see
  `delay`. -/
  | waitCond (cond : SExpr)
deriving Repr, BEq, Inhabited

/-! ## Implicit-sensitivity metadata -/

private def addName (name : String) (names : List String) : List String :=
  if names.contains name then names else names ++ [name]

private def addNames (names : List String) (acc : List String) : List String :=
  names.foldl (fun seen name => addName name seen) acc

partial def Expr.readNames : Expr → List String
  | .lit _ | .unsupported _ _ => []
  | .ident name => [name]
  | .unary _ arg | .reduce _ arg | .resizeSigned _ arg | .squash2 arg =>
      Expr.readNames arg
  | .binary _ left right => Expr.readNames left ++ Expr.readNames right
  | .ternary cond thenE elseE =>
      Expr.readNames cond ++ Expr.readNames thenE ++ Expr.readNames elseE
  | .concat parts => parts.toList.flatMap Expr.readNames

partial def SExpr.readNames : SExpr → List String
  | .m0 e => Expr.readNames e
  | .unary _ arg | .resize _ arg | .signedResize _ arg | .squash2 arg
  | .clog2 arg | .enumName arg _ _ => SExpr.readNames arg
  | .binary _ left right | .scmp _ left right | .caseEq left right
  | .caseNe left right | .caseMatch _ left right | .logAnd left right
  | .logOr left right => SExpr.readNames left ++ SExpr.readNames right
  | .ternary cond thenE elseE =>
      SExpr.readNames cond ++ SExpr.readNames thenE ++ SExpr.readNames elseE
  | .concat parts => parts.toList.flatMap SExpr.readNames
  | .selectRead _ _ _ value index | .compoundRead _ _ _ value index =>
      SExpr.readNames value ++ SExpr.readNames index
  | .bitQuery _ operand controls =>
      SExpr.readNames operand ++ controls.toList.flatMap SExpr.readNames
  | .sformatf _ operand _ => SExpr.readNames operand
  | .arrayDisplay elements =>
      elements.toList.flatMap fun (element, _) => SExpr.readNames element

partial def Stmt.readNames : Stmt → List String
  | .blockingAssign _ value | .nbaAssign _ value => Expr.readNames value
  | .ifStmt cond thenBranch elseBranch =>
      Expr.readNames cond ++ Stmt.readNames thenBranch ++
        (elseBranch.map Stmt.readNames |>.getD [])
  | .block body => body.toList.flatMap Stmt.readNames
  | .unsupported _ _ => []

partial def SStmt.readNames : SStmt → List String
  | .m0 s => Stmt.readNames s
  | .assign _ _ value => SExpr.readNames value
  | .selectedAssign _ _ _ _ _ index value
  | .selectedNbaAssign _ _ _ _ _ index value =>
      SExpr.readNames index ++ SExpr.readNames value
  | .distUniformAssign _ seed _ _ _ => [seed]
  | .packedAssign targets value | .packedNbaAssign targets value =>
      targets.flatMap fun target =>
        match target with
        | .whole _ _ _ => []
        | .selected _ _ _ _ _ index => SExpr.readNames index
      ++ SExpr.readNames value
  | .scanf input _ outputs result =>
      SExpr.readNames input ++
        (outputs ++ [result]).flatMap fun targets =>
          targets.flatMap fun target =>
            match target with
            | .whole _ _ _ => []
            | .selected _ _ _ _ _ index => SExpr.readNames index
  | .ifStmt cond thenBranch elseBranch =>
      SExpr.readNames cond ++ SStmt.readNames thenBranch ++
        (elseBranch.map SStmt.readNames |>.getD [])
  | .block body => body.toList.flatMap SStmt.readNames
  | .forLoop initializers condition steps body =>
      initializers.toList.flatMap SStmt.readNames ++ SExpr.readNames condition ++
        steps.toList.flatMap SStmt.readNames ++ SStmt.readNames body
  | .forAfterInit condition steps body | .forHeader condition steps body
  | .forAfterBody condition steps body | .forAfterStep condition steps body =>
      SExpr.readNames condition ++ steps.toList.flatMap SStmt.readNames ++
        SStmt.readNames body
  | .repeatLoop count _ body => SExpr.readNames count ++ SStmt.readNames body
  | .repeatBody _ body | .repeatAfterBody _ body => SStmt.readNames body
  | .doWhileLoop condition body => SExpr.readNames condition ++ SStmt.readNames body
  | .localDecl _ _ _ init => init.map SExpr.readNames |>.getD []
  | .sysCall _ _ args | .strobe _ args | .monitor _ args | .severity args | .fatal args =>
      args.toList.flatMap fun (arg, _) => SExpr.readNames arg
  | .waitCond condition => SExpr.readNames condition
  | .breakLoop | .continueLoop | .finish | .skip | .delay _ | .waitEvent _ _ => []

partial def Stmt.writeNames : Stmt → List String
  | .blockingAssign target _ | .nbaAssign target _ => [target]
  | .ifStmt _ thenBranch elseBranch =>
      Stmt.writeNames thenBranch ++ (elseBranch.map Stmt.writeNames |>.getD [])
  | .block body => body.toList.flatMap Stmt.writeNames
  | .unsupported _ _ => []

partial def SStmt.writeNames : SStmt → List String
  | .m0 s => Stmt.writeNames s
  | .assign _ target _ | .selectedAssign target _ _ _ _ _ _
  | .selectedNbaAssign target _ _ _ _ _ _ => [target]
  | .distUniformAssign target seed _ _ _ => [target, seed]
  | .packedAssign targets _ | .packedNbaAssign targets _ =>
      targets.map fun target =>
        match target with
        | .whole name _ _ | .selected name _ _ _ _ _ => name
  | .scanf _ _ outputs result =>
      (outputs ++ [result]).flatMap fun targets =>
        targets.map fun target =>
          match target with
          | .whole name _ _ | .selected name _ _ _ _ _ => name
  | .ifStmt _ thenBranch elseBranch =>
      SStmt.writeNames thenBranch ++ (elseBranch.map SStmt.writeNames |>.getD [])
  | .block body => body.toList.flatMap SStmt.writeNames
  | .forLoop initializers _ steps body =>
      initializers.toList.flatMap SStmt.writeNames ++
        steps.toList.flatMap SStmt.writeNames ++ SStmt.writeNames body
  | .forAfterInit _ steps body | .forHeader _ steps body
  | .forAfterBody _ steps body | .forAfterStep _ steps body =>
      steps.toList.flatMap SStmt.writeNames ++ SStmt.writeNames body
  | .repeatLoop _ _ body | .repeatBody _ body | .repeatAfterBody _ body
  | .doWhileLoop _ body => SStmt.writeNames body
  | .localDecl name _ _ _ => [name]
  | .sysCall _ _ _ | .strobe _ _ | .monitor _ _ | .severity _ | .fatal _
  | .finish | .skip | .delay _ | .waitEvent _ _ | .waitCond _
  | .breakLoop | .continueLoop => []

def SStmt.mkAssign (nonblocking : Bool) (target : String) : SExpr → SStmt
  | .m0 e => .m0 (if nonblocking then .nbaAssign target e else .blockingAssign target e)
  | v => .assign nonblocking target v

def SStmt.mkIf : SExpr → SStmt → Option SStmt → SStmt
  | .m0 c, .m0 t, none => .m0 (.ifStmt c t none)
  | .m0 c, .m0 t, some (.m0 e) => .m0 (.ifStmt c t (some e))
  | c, t, e => .ifStmt c t e

def SStmt.mkBlock (body : Array SStmt) : SStmt :=
  let m0s := body.filterMap fun s => match s with | .m0 st => some st | _ => none
  if m0s.size == body.size then .m0 (.block m0s) else .block body

def SStmt.isLoopBoundary : SStmt → Bool
  | .forAfterBody _ _ _ | .repeatAfterBody _ _ => true
  | _ => false

def transferRest (statements : List SStmt) : List SStmt :=
  statements.dropWhile (fun statement => !statement.isLoopBoundary)

/-- Convert an integral repeat count to the signed 32-bit loop count used by
the procedural control. Unknown bits are zero for this conversion; a
nonpositive converted count executes no iterations. -/
def repeatCount (v : LVec) (signed : Bool) : Res Nat :=
  let known := squash2v v
  let converted := if signed then known.resizeSigned 32 else known.resizeU 32
  if msb converted == .l1 then
    .ok 0
  else
    .ok (converted.toNat?.getD 0)

/-- The bounded 32-bit seed step used by the admitted literal random-system
function slice. Keeping the recurrence here makes the seed mutation and
returned value one auditable operation instead of pretending a random call is
a pure literal. -/
def distUniformValues (seed : LVec) (low high : Int) : Option (LVec × LVec) :=
  if seed.width != 32 || low > high then
    none
  else do
    let current ← seed.toNat?
    let next := (69069 * current + 1) % (2 ^ 32)
    let span := high - low + 1
    let value := low + (((next / 2 : Nat) : Int) * span) / (2 ^ 31 : Int)
    some (.ofNat 32 next, .ofInt 32 value)

/-! ## Output collection -/

inductive LoopTransfer where
  | normal
  | breakLoop
  | continueLoop
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

/-- One active `$monitor` registration and its last Postponed sample. -/
structure Monitor where
  format : Option String
  args : Array (SExpr × Bool)
  last : Option (List LVec) := none
deriving Repr, BEq, Inhabited

/-- Collected simulator output: finished `lines`, the unterminated tail
`cur` (`$write` without a newline), and the `halted` flag set by
`$finish`/`$stop`. -/
structure Out where
  lines : Array String := #[]
  cur : String := ""
  /-- Deferred `$strobe` calls, evaluated after all Active statements. -/
  pending : Array SStmt := #[]
  halted : Bool := false
  transfer : LoopTransfer := .normal
  /-- The single active `$monitor` registration.  The array keeps the
  registration state extensible while the executor replaces it on every
  `$monitor` call, as required by IEEE 1800. -/
  monitors : Array Monitor := #[]
deriving Repr, BEq, Inhabited

/-- Append rendered text, splitting completed lines on `'\n'`. -/
def Out.emit (o : Out) (s : String) : Out :=
  s.foldl
    (fun o c =>
      if c == '\n' then { o with lines := o.lines.push o.cur, cur := "" }
      else { o with cur := o.cur.push c })
    o

/-- All lines, flushing a nonempty unterminated tail. -/
def Out.flush (o : Out) : List String :=
  o.lines.toList ++ (if o.cur.isEmpty then [] else [o.cur])

/-! ## Format rendering (Xcelium-verified, see module docstring) -/

/-- Decimal digit count of `n` (`0` ⇒ 1). -/
def decDigits (n : Nat) : Nat := (toString n).length

/-- Natural `%d` field width of a `w`-bit value: `len(2^w − 1)` unsigned,
`len(-2^(w−1))` signed (e.g. 10 vs 11 for 32 bits). -/
def dWidth (w : Nat) (signed : Bool) : Nat :=
  if signed then decDigits (2 ^ (w - 1)) + 1 else decDigits (2 ^ w - 1)

/-- Right-justify with spaces to width `n` (never truncates). -/
def padLeft (s : String) (n : Nat) : String :=
  if s.length ≥ n then s else String.ofList (List.replicate (n - s.length) ' ') ++ s

/-- The whole-vector unknown summary char: `"x"` all-x, `"z"` all-z,
`"X"` if any x bit, else `"Z"` (mixed z/known) — Xcelium's `%d` behavior. -/
def unknownChar (v : LVec) : String :=
  if v.bits.all (· == .lx) then "x"
  else if v.bits.all (· == .lz) then "z"
  else if v.bits.any (· == .lx) then "X"
  else "Z"

/-- `%b`: MSB-first bit chars at full width. -/
def renderBin (v : LVec) : String := v.toBinString

/-- `%0b`: minimal width — all-x ⇒ `"x"`, all-z ⇒ `"z"`, else leading
zeros stripped (at least one char). Xcelium-verified. -/
def renderBin0 (v : LVec) : String :=
  if v.width > 0 && v.bits.all (· == .lx) then "x"
  else if v.width > 0 && v.bits.all (· == .lz) then "z"
  else
    let s := (v.toBinString.toList.dropWhile (· == '0'))
    if s.isEmpty then "0" else String.ofList s

/-- One hex digit from ≤ 4 bits (LSB-first slice): all known ⇒ lowercase
hex; all x ⇒ `x`; all z ⇒ `z`; mixed with an x ⇒ `X`; else ⇒ `Z`. -/
def hexDigit (nib : Array Logic) : Char :=
  if nib.all Logic.isKnown then
    let n := nib.foldr (fun b acc => 2 * acc + (if b == .l1 then 1 else 0)) 0
    (Nat.toDigits 16 n).headD '0'
  else if nib.all (· == .lx) then 'x'
  else if nib.all (· == .lz) then 'z'
  else if nib.any (· == .lx) then 'X'
  else 'Z'

/-- `%h`: `ceil(w/4)` MSB-first hex digits (top nibble zero-padded). -/
def renderHex (v : LVec) : String :=
  let ndig := (v.width + 3) / 4
  let chars := (List.range ndig).reverse.map fun i =>
    hexDigit (v.bits.extract (4 * i) (min (4 * i + 4) v.width))
  String.ofList chars

/-- `%0h`: leading zeros stripped (at least one char). -/
def renderHex0 (v : LVec) : String :=
  let s := (renderHex v).toList.dropWhile (· == '0')
  if s.isEmpty then "0" else String.ofList s

/-- One octal digit from up to three bits. Unknown summaries follow the
same display convention as `%h`/`%b`. -/
def octDigit (bits : Array Logic) : Char :=
  if bits.all Logic.isKnown then
    let n := bits.foldr (fun b acc => 2 * acc + (if b == .l1 then 1 else 0)) 0
    (Nat.toDigits 8 n).headD '0'
  else if bits.all (· == .lx) then 'x'
  else if bits.all (· == .lz) then 'z'
  else if bits.any (· == .lx) then 'X'
  else 'Z'

/-- `%o`: ceil(w/3) MSB-first octal digits (top digit zero-padded). -/
def renderOct (v : LVec) : String :=
  let ndig := (v.width + 2) / 3
  let chars := (List.range ndig).reverse.map fun i =>
    octDigit (v.bits.extract (3 * i) (min (3 * i + 3) v.width))
  String.ofList chars

#guard renderOct (.ofNat 8 0xab) == "253"

/-- `%d`/`%0d`. Unknown bits render as the summary char. Fully known
signed values use two's-complement decimal; unsigned values use natural
decimal. The field width comes from the argument's type. -/
def renderDec (v : LVec) (signed : Bool) (zero : Bool) : Res String :=
  match v.toNat? with
  | some unsignedValue =>
      let number : Int := if signed && msb v == .l1 then
        (unsignedValue : Int) - (2 ^ v.width : Nat) else unsignedValue
      let decimal := toString number
      .ok (if zero then decimal else padLeft decimal (dWidth v.width signed))
  | none =>
      let c := unknownChar v
      .ok (if zero then c else padLeft c (dWidth v.width signed))

/-- `%s`: one char per byte, MSB-first (top byte zero-padded); NUL bytes
print as spaces (Xcelium-verified). Unknown bits are loud. -/
def renderStr (v : LVec) : Res String :=
  let nbytes := (v.width + 7) / 8
  let bytes := (List.range nbytes).reverse.map fun i =>
    (⟨v.bits.extract (8 * i) (min (8 * i + 8) v.width)⟩ : LVec)
  if bytes.all (·.allKnown) then
    .ok (String.ofList (bytes.map fun b =>
      let n := b.toNat
      if n == 0 then ' ' else Char.ofNat n))
  else
    .unsupported "x/z bits under %s"

/-- `%c`: the low byte as a character; unknown bits are loud. -/
def renderChr (v : LVec) : Res String :=
  let low : LVec := ⟨v.bits.extract 0 (min 8 v.width)⟩
  match low.toNat? with
  | some n => .ok (String.singleton (Char.ofNat n))
  | none => .unsupported "x/z bits under %c"

def renderArrayDisplay (values : List (LVec × Bool)) : Res String := do
  let rendered ← values.mapM fun (value, signed) =>
    renderDec value signed true
  return "'{" ++ String.intercalate ", " rendered ++ "}"

/-- One conversion spec applied to one argument. `zero` is the `%0` flag. -/
def renderSpec (c : Char) (zero : Bool) (v : LVec) (signed : Bool) : Res String :=
  match c.toLower with
  | 'b' => .ok (if zero then renderBin0 v else renderBin v)
  | 'h' => .ok (if zero then renderHex0 v else renderHex v)
  | 'x' => .ok (if zero then renderHex0 v else renderHex v)
  | 'o' => .ok (renderOct v)
  | 'd' => renderDec v signed zero
  | 's' => renderStr v
  | 'c' => renderChr v
  | other => .unsupported s!"format specifier '%{other}' is outside the self-check tier"

/-- Render a format string against evaluated `(value, signed)` args.
Literal text and `%%` pass through; every spec consumes one arg; leftover
or missing args are loud (LRM makes both errors). -/
def renderFmt : List Char → List (LVec × Bool) → Res String
  | [], [] => .ok ""
  | [], _ :: _ => .unsupported "extra $display arguments (no matching format specifier)"
  | '%' :: rest, args =>
    match rest, args with
    | '%' :: rest', _ => do return "%" ++ (← renderFmt rest' args)
    | '0' :: c :: rest', (v, sg) :: args' => do
        return (← renderSpec c true v sg) ++ (← renderFmt rest' args')
    | c :: rest', (v, sg) :: args' =>
        if c == '0' then .unsupported "dangling '%0' at end of format"
        else do return (← renderSpec c false v sg) ++ (← renderFmt rest' args')
    | _, [] => .unsupported "missing $display argument for format specifier"
    | [], _ => .unsupported "dangling '%' at end of format"
  | c :: rest, args => do return String.singleton c ++ (← renderFmt rest args)

/-- Full `$display`/`$write` text (before the trailing newline). No format
string: no args ⇒ empty text (`$display;`), args without a format are
outside the tier. -/
def renderCall (format : Option String) (args : List (LVec × Bool)) : Res String :=
  match format with
  | some fmt => renderFmt fmt.toList args
  | none =>
      match args with
      | [] => .ok ""
      | _ => .unsupported "$display arguments without a format string"

/-! ## The fueled interpreter (wrapper around `evalExpr`/`execStmt`) -/

mutual

/-- Evaluate a self-check expression. `.m0` leaves delegate to the M0
`evalExpr`; everything else dispatches into the same `Basic.lean` operator
library (`LVec.eqCase`, `Logic.and` on truthiness, …). Fuel discipline as
in `Semantics.lean`. -/
def evalSExpr (fuel : Nat) (st : SvState) (e : SExpr) : Res LVec :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match e with
    | .m0 e0 => evalExpr fuel st e0
    | .unary op a => do
        return evalUnaryOp op (← evalSExpr fuel st a)
    | .binary op l r => do
        return evalBinOp op (← evalSExpr fuel st l) (← evalSExpr fuel st r)
    | .scmp op l r => do
        return .ofLogic (evalScmp op (← evalSExpr fuel st l) (← evalSExpr fuel st r))
    | .caseEq l r => do
        return .ofLogic (LVec.eqCase (← evalSExpr fuel st l) (← evalSExpr fuel st r))
    | .caseNe l r => do
        return .ofLogic (LVec.neCase (← evalSExpr fuel st l) (← evalSExpr fuel st r))
    | .caseMatch wildX l r => do
        let a ← evalSExpr fuel st l
        let b ← evalSExpr fuel st r
        return .ofLogic (if LVec.matchesCase wildX a b then .l1 else .l0)
    | .logAnd l r => do
        return .ofLogic (Logic.and (truthy (← evalSExpr fuel st l)) (truthy (← evalSExpr fuel st r)))
    | .logOr l r => do
        return .ofLogic (Logic.or (truthy (← evalSExpr fuel st l)) (truthy (← evalSExpr fuel st r)))
    | .resize w a => do
        return resizeV w (← evalSExpr fuel st a)
    | .signedResize width operand => do
        return LVec.resizeSigned (← evalSExpr fuel st operand) width
    | .squash2 a => do
        return squash2v (← evalSExpr fuel st a)
    | .bitQuery query operand controls => do
        let value ← evalSExpr fuel st operand
        let selected ← evalSExprs fuel st controls.toList
        return evalBitQuery query value selected
    | .clog2 operand => do
        evalClog2 (← evalSExpr fuel st operand)
    | .sformatf format operand signed => do
        let value ← evalSExpr fuel st operand
        let text ← renderFmt format.toList [(value, signed)]
        return asciiVec text
    | .arrayDisplay elements => do
        let values ← evalSExprPairs fuel st elements.toList
        return asciiVec (← renderArrayDisplay values)
    | .enumName subject cases default => do
        let value ← evalSExpr fuel st subject
        let text := (cases.toList.find? (fun entry =>
          LVec.eqCase value entry.1 == .l1)).map (·.2) |>.getD default
        return asciiVec text
    | .ternary c t f => do
        let cv ← evalSExpr fuel st c
        let tv ← evalSExpr fuel st t
        let fv ← evalSExpr fuel st f
        return LVec.ternary cv tv fv
    | .concat parts => do
        return LVec.concatMany (← evalSExprs fuel st parts.toList).toArray
    | .selectRead width descending indexSigned value index => do
        let source ← evalSExpr fuel st value
        let position ← evalSExpr fuel st index
        return selectedRead width descending indexSigned source position
    | .compoundRead width descending indexSigned value index => do
        let source ← evalSExpr fuel st value
        let position ← evalSExpr fuel st index
        compoundRead width descending indexSigned source position

/-- Left-to-right list evaluation (concat parts, source order). -/
def evalSExprs (fuel : Nat) (st : SvState) (es : List SExpr) : Res (List LVec) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match es with
    | [] => .ok []
    | e :: rest => do
        let v ← evalSExpr fuel st e
        let vs ← evalSExprs fuel st rest
        return v :: vs

def evalSExprPairs (fuel : Nat) (st : SvState)
    (es : List (SExpr × Bool)) : Res (List (LVec × Bool)) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match es with
    | [] => .ok []
    | (e, signed) :: rest => do
        let value ← evalSExpr fuel st e
        let values ← evalSExprPairs fuel st rest
        return (value, signed) :: values

/-- `(value, signed)` pairs for `$display` args. -/
def evalArgs (fuel : Nat) (st : SvState) (args : List (SExpr × Bool)) :
    Res (List (LVec × Bool)) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match args with
    | [] => .ok []
    | (e, sg) :: rest => do
        let v ← evalSExpr fuel st e
        let vs ← evalArgs fuel st rest
        return (v, sg) :: vs

def execPackedTargets (fuel : Nat) (st : SvState) (replacement : LVec)
    (targets : List (PackedTarget × Nat)) (order : List Nat) : Res SvState :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
      match order with
      | [] => .ok st
      | position :: rest => do
          let (target, offset) ← match targets[position]? with
            | some target => pure target
            | none => .unsupported "concatenated assignment order selected an invalid destination"
          let part := replacement.extract offset target.width
          let updated ← match target with
            | .whole name width twoState => do
                let old ← match SvState.lookup st name with
                  | some old => pure old
                  | none => .unsupported s!"unknown packed assignment target '{name}'"
                if old.width != width then
                  .unsupported s!"packed assignment target '{name}' has inconsistent width"
                else pure (SvState.set st name (if twoState then squash2v part else part))
            | .selected name width descending indexSigned twoState index => do
                let position ← evalSExpr fuel st index
                let old ← match SvState.lookup st name with
                  | some old => pure old
                  | none => .unsupported s!"unknown selected assignment target '{name}'"
                let part := if twoState then squash2v part else part
                pure (SvState.set st name (selectedWrite width descending indexSigned old position part))
          execPackedTargets fuel updated replacement targets rest

def queuedValue (name : String) (st : SvState) (nba : NbaQueue) : Option LVec :=
  match nba.reverse.find? (fun u => u.1 == name) with
  | some u => some u.2
  | none => SvState.lookup st name

def enqueueSelectedNba (st : SvState) (nba : NbaQueue) (target : String)
    (width : Nat) (descending indexSigned twoState : Bool)
    (position replacement : LVec) : Res NbaQueue :=
  match SvState.lookup st target, selectedIndex indexSigned position with
  | none, _ => .unsupported s!"unknown selected assignment target '{target}'"
  | some _, none => .ok nba
  | some old, some _ =>
      let base := (queuedValue target st nba).getD old
      let replacement := if twoState then squash2v replacement else replacement
      let updated := selectedWrite width descending indexSigned base position replacement
      .ok (nba ++ [(target, updated)])

def enqueuePackedNba (fuel : Nat) (st : SvState) (nba : NbaQueue)
    (replacement : LVec) (targets : List (PackedTarget × Nat))
    (order : List Nat) : Res NbaQueue :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
      match order with
      | [] => .ok nba
      | position :: rest => do
          let (target, offset) ← match targets[position]? with
            | some target => pure target
            | none => .unsupported "concatenated assignment order selected an invalid destination"
          let part := replacement.extract offset target.width
          let nba' ← match target with
            | .whole name width twoState => do
                let old ← match SvState.lookup st name with
                  | some old => pure old
                  | none => .unsupported s!"unknown packed assignment target '{name}'"
                if old.width != width then
                  .unsupported s!"packed assignment target '{name}' has inconsistent width"
                else
                  let value := if twoState then squash2v part else part
                  pure (nba ++ [(name, value)])
            | .selected name width descending indexSigned twoState index => do
                let position ← evalSExpr fuel st index
                match SvState.lookup st name, selectedIndex indexSigned position with
                | none, _ => .unsupported s!"unknown selected assignment target '{name}'"
                | some _, none => pure nba
                | some old, some _ =>
                    let base := (queuedValue name st nba).getD old
                    let replacement := if twoState then squash2v part else part
                    let updated := selectedWrite width descending indexSigned base position replacement
                    pure (nba ++ [(name, updated)])
          enqueuePackedNba fuel st nba' replacement targets rest

/-- Successful outputs copy back left to right; later selectors see earlier writes. -/
def execScanWrites (fuel : Nat) (st : SvState) (outputs : List (List PackedTarget))
    (values : List LVec) (assignmentOrder : AssignmentOrder) : Res SvState :=
  match fuel, outputs, values with
  | 0, _, _ => .timeout
  | _, _, [] => .ok st
  | _, [], _ :: _ => .unsupported "Scanf: scanner produced excess outputs"
  | fuel + 1, targets :: rest, value :: values => do
      let order := assignmentOrder targets.length
      if !validAssignmentOrder targets.length order then
        .unsupported "Scanf: target assignment order must be a permutation"
      else
        let updated ← execPackedTargets fuel st value (packedTargetSlices targets) order
        execScanWrites fuel updated rest values assignmentOrder

def evalForCondition (fuel : Nat) (st : SvState) (condition : SExpr) : Res LVec :=
  evalSExpr fuel st condition

def sampleRepeatCount (fuel : Nat) (st : SvState) (count : SExpr) (signed : Bool) : Res Nat := do
  let value ← evalSExpr fuel st count
  repeatCount value signed

def execForLoop (fuel : Nat) (st : SvState) (nba : NbaQueue) (out : Out)
    (condition : SExpr) (steps : Array SStmt) (body : SStmt)
    (assignmentOrder : AssignmentOrder) :
    Res (SvState × NbaQueue × Out) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 => do
      if out.halted then return (st, nba, out)
      let c ← evalForCondition fuel st condition
      if c.condTrue then
        let (st', nba', out') ← execSStmt fuel st nba out body assignmentOrder
        if out'.halted then
          .ok (st', nba', out')
        else if out'.transfer == .breakLoop then
          .ok (st', nba', { out' with transfer := .normal })
        else
          let (st'', nba'', out'') ← execSStmts fuel st' nba'
            { out' with transfer := .normal }
            steps.toList assignmentOrder
          execForLoop fuel st'' nba'' out'' condition steps body assignmentOrder
      else
        .ok (st, nba, out)

def execRepeatLoop (fuel : Nat) (st : SvState) (nba : NbaQueue) (out : Out)
    (remaining : Nat) (body : SStmt) (assignmentOrder : AssignmentOrder) :
    Res (SvState × NbaQueue × Out) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
      if out.halted || remaining == 0 then
        .ok (st, nba, out)
      else do
        let (st', nba', out') ← execSStmt fuel st nba out body assignmentOrder
        if out'.halted then
          .ok (st', nba', out')
        else if out'.transfer == .breakLoop then
          .ok (st', nba', { out' with transfer := .normal })
        else
          execRepeatLoop fuel st' nba' { out' with transfer := .normal }
            (remaining - 1) body assignmentOrder

/-- Execute one self-check statement, threading state, NBA queue, and
output. Loop transfers are consumed at their nearest boundary. A halted
`Out` short-circuits (`$finish` skips the rest of the
run). `.m0` subtrees run under the existing `execStmt`. -/
def execSStmt (fuel : Nat) (st : SvState) (nba : NbaQueue) (out : Out)
    (stmt : SStmt) (assignmentOrder : AssignmentOrder := rightToLeftAssignmentOrder) :
    Res (SvState × NbaQueue × Out) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    if out.halted then .ok (st, nba, out)
    else
      match stmt with
      | .m0 s => do
          let (st', nba') ← execStmt fuel st nba s
          return (st', nba', out)
      | .assign nonblocking target value => do
          let v ← evalSExpr fuel st value
          if nonblocking then return (st, nba ++ [(target, v)], out)
          else return (SvState.set st target v, nba, out)
      | .scanf input format outputs result => do
          let input ← evalSExpr fuel st input
          let widths := outputs.map fun targets => targets.foldl (fun n target => n + target.width) 0
          let (count, values) ← match FormattedInput.scan input format widths with
            | .ok value => pure value
            | .error message => .unsupported message
          let updated ← execScanWrites fuel st outputs values assignmentOrder
          let width := result.foldl (fun n target => n + target.width) 0
          let order := assignmentOrder result.length
          if !validAssignmentOrder result.length order then
            .unsupported "Scanf: result assignment order must be a permutation"
          else
            let updated ← execPackedTargets fuel updated ((LVec.ofNat 32 count).resizeSigned width)
              (packedTargetSlices result) order
            return (updated, nba, out)
      | .selectedAssign target width descending indexSigned twoState index value => do
          let replacement ← evalSExpr fuel st value
          let position ← evalSExpr fuel st index
          let old ← match SvState.lookup st target with
            | some old => pure old
            | none => .unsupported s!"unknown selected assignment target '{target}'"
          let replacement := if twoState then squash2v replacement else replacement
          let updated := selectedWrite width descending indexSigned old position replacement
          return (SvState.set st target updated, nba, out)
      | .selectedNbaAssign target width descending indexSigned twoState index value => do
          let replacement ← evalSExpr fuel st value
          let position ← evalSExpr fuel st index
          let nba' ← enqueueSelectedNba st nba target width descending indexSigned twoState
            position replacement
          return (st, nba', out)
      | .distUniformAssign target seed low high twoState => do
          let seedValue ← match SvState.lookup st seed with
            | some value => pure value
            | none => .unsupported s!"unknown dist_uniform seed '{seed}'"
          let old ← match SvState.lookup st target with
            | some value => pure value
            | none => .unsupported s!"unknown dist_uniform target '{target}'"
          if old.width != 32 then
            .unsupported "dist_uniform target must be a 32-bit integral cell"
          else
            match distUniformValues seedValue low high with
            | none => .unsupported "dist_uniform requires a known 32-bit seed"
            | some (nextSeed, sampled) =>
                let sampled := if twoState then squash2v sampled else sampled
                return (SvState.set (SvState.set st seed nextSeed) target sampled,
                  nba, out)
      | .packedNbaAssign targets value => do
          let replacement ← evalSExpr fuel st value
          let order := assignmentOrder targets.length
          if !validAssignmentOrder targets.length order then
            .unsupported "concatenated assignment order must be a permutation of destinations"
          else
            let nba' ← enqueuePackedNba fuel st nba replacement
              (packedTargetSlices targets) order
            return (st, nba', out)
      | .packedAssign targets value => do
          let replacement ← evalSExpr fuel st value
          let order := assignmentOrder targets.length
          if !validAssignmentOrder targets.length order then
            .unsupported "concatenated assignment order must be a permutation of destinations"
          else
            let width := targets.foldl (fun width target => width + target.width) 0
            let updated ← execPackedTargets fuel st (replacement.resizeU width)
              (packedTargetSlices targets) order
            return (updated, nba, out)
      | .ifStmt cond thenB elseB => do
          let c ← evalSExpr fuel st cond
          if c.condTrue then
            execSStmt fuel st nba out thenB assignmentOrder
          else
            match elseB with
            | some s => execSStmt fuel st nba out s assignmentOrder
            | none => .ok (st, nba, out)
      | .block body => execSStmts fuel st nba out body.toList assignmentOrder
      | .forLoop initializers condition steps body => do
          let (st', nba', out') ← execSStmts fuel st nba out
            initializers.toList assignmentOrder
          execForLoop fuel st' nba' out' condition steps body assignmentOrder
      | .forAfterInit condition steps body =>
          execForLoop fuel st nba out condition steps body assignmentOrder
      | .forHeader condition steps body =>
          execForLoop fuel st nba out condition steps body assignmentOrder
      | .forAfterBody condition steps body => do
          if out.transfer == .breakLoop then
            .ok (st, nba, { out with transfer := .normal })
          else
            let (st', nba', out') ← execSStmts fuel st nba
              { out with transfer := .normal } steps.toList assignmentOrder
            execForLoop fuel st' nba' out' condition steps body assignmentOrder
      | .forAfterStep condition steps body =>
          execForLoop fuel st nba out condition steps body assignmentOrder
      | .repeatLoop count countSigned body => do
          let remaining ← sampleRepeatCount fuel st count countSigned
          execRepeatLoop fuel st nba out remaining body assignmentOrder
      | .repeatBody remaining body =>
          execRepeatLoop fuel st nba out remaining body assignmentOrder
      | .repeatAfterBody remaining body =>
          if out.transfer == .breakLoop then
            .ok (st, nba, { out with transfer := .normal })
          else
            execRepeatLoop fuel st nba { out with transfer := .normal }
              (remaining - 1) body assignmentOrder
      | .doWhileLoop condition body => do
          let (st', nba', out') ← execSStmt fuel st nba out body assignmentOrder
          if out'.halted then
            .ok (st', nba', out')
          else if out'.transfer == .breakLoop then
            .ok (st', nba', { out' with transfer := .normal })
          else
            execForLoop fuel st' nba' { out' with transfer := .normal }
              condition #[] body assignmentOrder
      | .breakLoop => .ok (st, nba, { out with transfer := .breakLoop })
      | .continueLoop => .ok (st, nba, { out with transfer := .continueLoop })
      | .delay _ =>
          .unsupported "#delay: the self-check tier runs at time 0 (no scheduler)"
      | .waitEvent _ _ =>
          .unsupported "@(event): the self-check tier runs at time 0 (no scheduler)"
      | .waitCond condition => do
          let value ← evalSExpr fuel st condition
          if value.condTrue then
            .ok (st, nba, out)
          else
            .unsupported "wait(cond): the self-check tier runs at time 0 (no scheduler)"
      | .localDecl name width twoState init => do
          let v ← match init with
            | none => pure (if twoState then LVec.ofNat width 0 else LVec.xVec width)
            | some e => evalSExpr fuel st e
          let v := if twoState then squash2v v else v
          return (SvState.set st name v, nba, out)
      | .sysCall write format args => do
          let vals ← evalArgs fuel st args.toList
          let text ← renderCall format vals
          return (st, nba, out.emit (if write then text else text ++ "\n"))
      | .strobe format args =>
          return (st, nba, { out with pending := out.pending.push (.sysCall false format args) })
      | .monitor format args =>
          return (st, nba, { out with monitors := #[{ format := format, args := args }] })
      | .severity args => do
          let _ ← evalArgs fuel st args.toList
          return (st, nba, out)
      | .fatal args => do
          let _ ← evalArgs fuel st args.toList
          return (st, nba, { out with halted := true })
      | .finish => .ok (st, nba, { out with halted := true })
      | .skip => .ok (st, nba, out)

/-- Execute statements in order. -/
def execSStmts (fuel : Nat) (st : SvState) (nba : NbaQueue) (out : Out)
    (ss : List SStmt) (assignmentOrder : AssignmentOrder := rightToLeftAssignmentOrder) :
    Res (SvState × NbaQueue × Out) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match ss with
    | [] => .ok (st, nba, out)
    | s :: rest => do
        let (st', nba', out') ← execSStmt fuel st nba out s assignmentOrder
        if out'.transfer != .normal then
          match transferRest rest with
          | [] => .ok (st', nba', out')
          | boundary :: tail =>
              execSStmts fuel st' nba' out' (boundary :: tail) assignmentOrder
        else execSStmts fuel st' nba' out' rest assignmentOrder

end

/-! ## Designs and the runner -/

/-- One module-level declaration. `init` is the (possibly synthesized —
2-state vars) initializer; a four-state var without one starts all-x (§6.8),
a net or unconnected input all-z. Two-state declarations convert those
unknown/high-impedance startup values to zero. -/
structure SDecl where
  name : String
  width : Nat
  isNet : Bool := false
  isInput : Bool := false
  isOutput : Bool := false
  isSigned : Bool := false
  twoState : Bool := false
  init : Option SExpr := none
deriving Repr, Inhabited

/-- A self-check process: an `initial` body, or anything else (kept with
its envelope tag — `runSelfCheck` is loud on it, never silently drops). -/
inductive SProc where
  | initial (body : SStmt)
  | alwaysBody (body : SStmt)
  | alwaysPosedge (clock : String) (body : SStmt)
  | alwaysNegedge (clock : String) (body : SStmt)
  | alwaysFF (clock : String) (body : SStmt)
  | alwaysFFNegedge (clock : String) (body : SStmt)
  | alwaysFFReset (clock : String) (reset : String) (body : SStmt)
  | alwaysImplicit (body : SStmt)
  | alwaysComb (body : SStmt)
  | alwaysLatch (body : SStmt)
  | assign (target : String) (value : SExpr)
  | other (svKind : String) (text : String)
deriving Repr, Inhabited

/-- A self-check design (the analog of `Sv.Design` for this tier). -/
structure Design where
  name : String
  decls : Array SDecl
  procs : Array SProc
  /-- Envelope literals produced by time-zero-only query lowering must not
  enter an executor whose clock can advance. -/
  requiresTimeZero : Bool := false
deriving Repr, Inhabited

/-- Initialize declarations in order (later initializers may read earlier
signals; reading a not-yet-declared one is loud via `readSignal`). -/
def initDecls (fuel : Nat) : List SDecl → SvState → Res SvState
  | [], st => .ok st
  | dc :: rest, st => do
      let v ← match dc.init with
        | none => pure (if dc.twoState then LVec.replicate dc.width .l0
                        else if dc.isNet || dc.isInput then LVec.replicate dc.width .lz
                        else LVec.xVec dc.width)
        | some e => do
            let value ← evalSExpr fuel st e
            pure (if dc.twoState then squash2v value else value)
      initDecls fuel rest (SvState.set st dc.name v)

/-- Run the initial processes once each, in source order, at time 0.
Any non-initial process is loud. A halt (`$finish`) stops the fold. -/
def runInits (fuel : Nat) : List SProc → SvState → NbaQueue → Out →
    (assignmentOrder : AssignmentOrder := rightToLeftAssignmentOrder) →
    Res (SvState × NbaQueue × Out)
  | [], st, nba, out, _ => .ok (st, nba, out)
  | .other svKind _ :: _, _, _, _, _ =>
      .unsupported s!"non-initial process '{svKind}' (self-check tier runs initial-only designs)"
  | .alwaysPosedge clock _ :: _, _, _, _, _ =>
      .unsupported s!"non-initial process 'AlwaysPosedge:{clock}' (self-check tier runs initial-only designs)"
  | .alwaysNegedge clock _ :: _, _, _, _, _ =>
      .unsupported s!"non-initial process 'AlwaysNegedge:{clock}' (self-check tier runs initial-only designs)"
  | .alwaysFF clock _ :: _, _, _, _, _ =>
      .unsupported s!"non-initial process 'AlwaysFF:{clock}' (self-check tier runs initial-only designs)"
  | .alwaysFFNegedge clock _ :: _, _, _, _, _ =>
      .unsupported s!"non-initial process 'AlwaysFFNegedge:{clock}' (self-check tier runs initial-only designs)"
  | .alwaysFFReset clock reset _ :: _, _, _, _, _ =>
      .unsupported s!"non-initial process 'AlwaysFF:{clock}+negedge {reset}' (self-check tier runs initial-only designs)"
  | .alwaysImplicit _ :: _, _, _, _, _ =>
      .unsupported "non-initial process 'AlwaysImplicit' (self-check tier runs initial-only designs)"
  | .alwaysBody _ :: _, _, _, _, _ =>
      .unsupported "non-initial process 'Always' (self-check tier runs initial-only designs)"
  | .alwaysComb _ :: _, _, _, _, _ =>
      .unsupported "non-initial process 'AlwaysComb' (self-check tier runs initial-only designs)"
  | .alwaysLatch _ :: _, _, _, _, _ =>
      .unsupported "non-initial process 'AlwaysLatch' (self-check tier runs initial-only designs)"
  | .assign _ _ :: _, _, _, _, _ =>
      .unsupported "non-initial process 'Assign' (self-check tier runs initial-only designs)"
  | .initial body :: rest, st, nba, out, assignmentOrder => do
      let (st', nba', out') ← execSStmt fuel st nba out body assignmentOrder
      if out'.halted then .ok (st', nba', out')
      else runInits fuel rest st' nba' out' assignmentOrder

def flushStrobes (fuel : Nat) (st : SvState) (out : Out) :
    Res (SvState × Out) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
      match out.pending.toList with
      | [] => .ok (st, { out with pending := #[] })
      | pending :: rest => do
          let (st', _, out') ← execSStmt fuel st []
            { out with pending := #[], halted := false } pending
          let next := { out' with pending := rest.toArray }
          flushStrobes fuel st' { next with halted := out.halted }

/-- Sample the active `$monitor` registration in Postponed.  A registration
is emitted on its first sample and thereafter only when one of its argument
values changes.  The comparison uses the evaluated values, while rendering
retains each argument's signedness metadata. -/
def flushMonitor (fuel : Nat) (st : SvState) (out : Out) :
    Res (SvState × Out) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
      match out.monitors.toList with
      | [] => .ok (st, out)
      | monitor :: _ => do
          let values ← evalArgs fuel st monitor.args.toList
          let sampled := values.map fun value => value.1
          if monitor.last == some sampled then
            .ok (st, out)
          else
            let text ← renderCall monitor.format values
            let emitted := out.emit (text ++ "\n")
            .ok (st, { emitted with monitors := #[{ monitor with last := some sampled }] })

/-- The self-check entry point: execute every `initial` process once at
time 0 (source order), collecting the rendered `$display` output lines.
`$finish` ends the run cleanly. The time-0 NBA queue commits after all
initials — after the last possible output, so it is dropped here. -/
def runSelfCheck (d : Design) (fuel : Nat)
    (assignmentOrder : AssignmentOrder := rightToLeftAssignmentOrder) : Res (List String) := do
  if let some tag := d.procs.findSome? fun p =>
      match p with
      | .other svKind _ => some svKind
      | .alwaysPosedge clock _ => some s!"AlwaysPosedge:{clock}"
      | .alwaysNegedge clock _ => some s!"AlwaysNegedge:{clock}"
      | .alwaysFF clock _ => some s!"AlwaysFF:{clock}"
      | .alwaysFFNegedge clock _ => some s!"AlwaysFFNegedge:{clock}"
      | .alwaysFFReset clock reset _ => some s!"AlwaysFF:{clock}+negedge {reset}"
      | .alwaysImplicit _ => some "AlwaysImplicit"
      | .alwaysBody _ => some "Always"
      | .alwaysComb _ => some "AlwaysComb"
      | .alwaysLatch _ => some "AlwaysLatch"
      | .assign _ _ => some "Assign"
      | _ => none then
    return ← .unsupported
      s!"non-initial process '{tag}' (self-check tier runs initial-only designs)"
  let st ← initDecls fuel d.decls.toList []
  let (st', _, out) ← runInits fuel d.procs.toList st [] {} assignmentOrder
  let (st'', out) ← flushMonitor fuel st' out
  let (_, out) ← flushStrobes fuel st'' out
  if out.transfer != .normal then
    .unsupported "loop transfer outside a loop"
  else
    return out.flush

/-! ## Envelope ingestion (schema `sv-0.1` + the §f self-check vocabulary)

Parses the *actual* extractor output (`docs/sv-envelope-schema.md`
vocabulary — `design.modules[]`, `Port`/`Var`/`Net`, expression-node
assignment targets — plus the §f nodes: `Initial`, `SysCall`, `LocalDecl`,
`Empty`, `Resize`, `Squash2`, the extended `Binary` ops, and 2-state
`Var`s). `Json.lean`'s parser predates the schema doc and does not match
it (see `harness/sv/runner.lean`'s adapter note), so this tier parses the
schema directly. Pure `Except String`; parse errors are loud. -/

open Lean (Json)

private def getF (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{name}'"

private def getFOpt (j : Json) (name : String) : Option Json :=
  match j.getObjVal? name with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

private def getStrF (j : Json) (name : String) : Except String String := do
  match (← getF j name).getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"field '{name}' is not a string"

private def getNatF (j : Json) (name : String) : Except String Nat := do
  match (← getF j name).getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"field '{name}' is not a Nat"

private def getIntF (j : Json) (name : String) : Except String Int := do
  match (← getF j name).getInt? with
  | .ok n => .ok n
  | .error _ => .error s!"field '{name}' is not an Int"

private def getArrF (j : Json) (name : String) : Except String (Array Json) := do
  match (← getF j name).getArr? with
  | .ok a => .ok a
  | .error _ => .error s!"field '{name}' is not an array"

private def getBoolF (j : Json) (name : String) : Except String Bool := do
  match (← getF j name).getBool? with
  | .ok b => .ok b
  | .error _ => .error s!"field '{name}' is not a Bool"

private def unsupportedText (j : Json) : String :=
  (getFOpt j "text").bind (·.getStr?.toOption) |>.getD ""

/-- Envelope `Binary.op` spellings of this tier. -/
def parseSBinOp (op : String) (l r : SExpr) : Except String SExpr :=
  match op with
  | "+" => .ok (.mkBinary .add l r)
  | "-" => .ok (.mkBinary .sub l r)
  | "*" => .ok (.mkBinary .mul l r)
  | "u/" => .ok (.mkBinary .div l r)
  | "s/" => .ok (.mkBinary .sdiv l r)
  | "u%" => .ok (.mkBinary .rem l r)
  | "s%" => .ok (.mkBinary .srem l r)
  | "u**u" => .ok (.mkBinary (.pow false false) l r)
  | "u**s" => .ok (.mkBinary (.pow false true) l r)
  | "s**u" => .ok (.mkBinary (.pow true false) l r)
  | "s**s" => .ok (.mkBinary (.pow true true) l r)
  | "<<" | "u<<" => .ok (.mkBinary (.shl false) l r)
  | "s<<" => .ok (.mkBinary (.shl true) l r)
  | ">>" | "u>>" => .ok (.mkBinary (.shr false) l r)
  | "s>>" => .ok (.mkBinary (.shr true) l r)
  | "<<<" | "u<<<" => .ok (.mkBinary (.ashl false) l r)
  | "s<<<" => .ok (.mkBinary (.ashl true) l r)
  | "u>>>" => .ok (.mkBinary (.ashr false) l r)
  | "s>>>" => .ok (.mkBinary (.ashr true) l r)
  | "&" => .ok (.mkBinary .and l r)
  | "|" => .ok (.mkBinary .or l r)
  | "^" => .ok (.mkBinary .xor l r)
  | "==" => .ok (.mkBinary .eq l r)
  | "!=" => .ok (.mkBinary .ne l r)
  | "<" => .ok (.mkBinary .lt l r)
  | "<=" => .ok (.mkBinary .le l r)
  | ">" => .ok (.mkBinary .gt l r)
  | ">=" => .ok (.mkBinary .ge l r)
  | "s<" => .ok (.scmp .lt l r)
  | "s<=" => .ok (.scmp .le l r)
  | "s>" => .ok (.scmp .gt l r)
  | "s>=" => .ok (.scmp .ge l r)
  | "===" => .ok (.caseEq l r)
  | "!==" => .ok (.caseNe l r)
  | "==?" => .ok (.mkBinary .wildEq l r)
  | "!=?" => .ok (.mkBinary .wildNe l r)
  | "&&" => .ok (.logAnd l r)
  | "||" => .ok (.logOr l r)
  | other => .error s!"unknown binary op '{other}'"

/-- Envelope `Reduce.op` spellings of this tier. -/
def parseSRedOp (op : String) : Except String RedOp :=
  match op with
  | "|" => .ok .or
  | "&" => .ok .and
  | "^" => .ok .xor
  | "~|" => .ok .nor
  | "~&" => .ok .nand
  | "~^" | "^~" => .ok .xnor
  | other => .error s!"unknown reduction op '{other}'"

partial def parseSExpr (j : Json) : Except String SExpr := do
  let kind ← getStrF j "kind"
  match kind with
  | "Literal" =>
      let width ← getNatF j "width"
      let bits ← getStrF j "bits"
      match LVec.ofBinLit? width bits with
      | some v => return .m0 (.lit v)
      | none => .error s!"Literal: bad bits string {bits.quote}"
  | "Ident" => return .m0 (.ident (← getStrF j "name"))
  | "Unary" =>
      let a ← parseSExpr (← getF j "operand")
      match ← getStrF j "op" with
      | "~" => return .mkUnary .bnot a
      | "!" => return .mkUnary .lnot a
      | "-" => return .mkUnary .neg a
      | "+" => return .mkUnary .pos a
      | other => .error s!"unknown unary op '{other}'"
  | "Reduce" =>
      let a ← parseSExpr (← getF j "operand")
      return .m0 (.reduce (← parseSRedOp (← getStrF j "op"))
        (match a with | .m0 e => e | _ => .unsupported "Reduce:operand" "non-M0 operand"))
  | "Binary" =>
      let l ← parseSExpr (← getF j "left")
      let r ← parseSExpr (← getF j "right")
      parseSBinOp (← getStrF j "op") l r
  | "CaseMatch" =>
      let wildX ← match ← getStrF j "mode" with
        | "casez" => pure false
        | "casex" => pure true
        | other => .error s!"unknown wildcard case mode '{other}'"
      return .caseMatch wildX (← parseSExpr (← getF j "left"))
        (← parseSExpr (← getF j "right"))
  | "Ternary" =>
      return .mkTernary (← parseSExpr (← getF j "cond"))
        (← parseSExpr (← getF j "then")) (← parseSExpr (← getF j "else"))
  | "Concat" =>
      return .mkConcat (← (← getArrF j "parts").mapM parseSExpr)
  | "Resize" =>
      return .resize (← getNatF j "width") (← parseSExpr (← getF j "operand"))
  | "SignedResize" =>
      return .signedResize (← getNatF j "width") (← parseSExpr (← getF j "operand"))
  | "Squash2" =>
      return .squash2 (← parseSExpr (← getF j "operand"))
  | "Clog2" =>
      if (← getNatF j "width") != 32 || !(← getBoolF j "signed") then
        throw "clog2 result must be a signed 32-bit int"
      return .clog2 (← parseSExpr (← getF j "operand"))
  | "SFormatF" =>
      return .sformatf (← getStrF j "format")
        (← parseSExpr (← getF j "operand")) (← getBoolF j "signed")
  | "ArrayDisplay" =>
      let elements ← (← getArrF j "elements").mapM parseSExpr
      let signed ← getBoolF j "element_signed"
      return .arrayDisplay (elements.map (fun element => (element, signed)))
  | "MinTypMax" =>
      let choice ← getStrF j "choice"
      if choice != "min" && choice != "typ" && choice != "max" then
        throw "invalid min/typ/max elaboration choice"
      let value ← getF j "value"
      let width ← getNatF j "width"
      if width == 0 || (← getNatF value "width") != width then
        throw "min/typ/max selected width disagrees with its bound context"
      parseSExpr value
  | "BitQuery" =>
      let query ← match ← getStrF j "op" with
        | "$countbits" => pure BitQuery.countbits
        | "$countones" => pure BitQuery.countones
        | "$onehot" => pure BitQuery.onehot
        | "$onehot0" => pure BitQuery.onehot0
        | "$isunknown" => pure BitQuery.isunknown
        | other => .error s!"unknown bit-vector query '{other}'"
      let controls ← (← getArrF j "controls").mapM parseSExpr
      if (query == .countbits && controls.isEmpty) ||
          (query != .countbits && !controls.isEmpty) then
        .error "invalid bit-vector query control arity"
      else
        return .bitQuery query (← parseSExpr (← getF j "operand")) controls
  | "EnumName" =>
      let cases ← (← getArrF j "cases").mapM fun item => do
        let valueJson ← getF item "value"
        let width ← getNatF valueJson "width"
        let bits ← getStrF valueJson "bits"
        let value ← match LVec.ofBinLit? width bits with
          | some value => pure value
          | none => throw s!"EnumName: bad bits string {bits.quote}"
        return (value, ← getStrF item "name")
      return .enumName (← parseSExpr (← getF j "subject")) cases
        (← getStrF j "default")
  | "SelectRead" =>
      return .selectRead (← getNatF j "width")
        (← getBoolF j "descending") (← getBoolF j "index_signed")
        (← parseSExpr (← getF j "value")) (← parseSExpr (← getF j "index"))
  | "CompoundRead" =>
      let width ← getNatF j "width"
      if width == 0 then throw "compound read has zero width"
      return .compoundRead width (← getBoolF j "descending") (← getBoolF j "index_signed")
        (← parseSExpr (← getF j "value")) (← parseSExpr (← getF j "index"))
  | "Unsupported" =>
      return .m0 (.unsupported (← getStrF j "sv_kind") (unsupportedText j))
  | other => .error s!"unknown expression kind '{other}'"

/-- Assignment target: the schema guarantees an `Ident` node. -/
def targetName (j : Json) : Except String String := do
  match ← parseSExpr j with
  | .m0 (.ident n) => .ok n
  | .m0 (.unsupported svKind _) => .error s!"unsupported assignment target ({svKind})"
  | _ => .error "assignment target is not a plain identifier"

partial def parsePackedTargets (j : Json) : Except String (List PackedTarget) := do
  let width ← getNatF j "width"
  if width == 0 then throw "packed assignment target has zero width"
  match ← getStrF j "kind" with
  | "Ident" =>
      return [.whole (← targetName j) width (← getBoolF j "two_state")]
  | "SelectTarget" =>
      return [.selected (← targetName (← getF j "value")) width
        (← getBoolF j "descending") (← getBoolF j "index_signed")
        (← getBoolF j "two_state") (← parseSExpr (← getF j "index"))]
  | "ConcatTarget" =>
      let parts ← (← getArrF j "parts").toList.mapM parsePackedTargets
      let targets := parts.flatten
      if targets.foldl (fun total target => total + target.width) 0 != width then
        throw "concatenated assignment target has inconsistent width"
      return targets
  | other => throw s!"unknown packed assignment target kind '{other}'"

partial def parseSStmt (j : Json) : Except String SStmt := do
  let kind ← getStrF j "kind"
  match kind with
  | "Block" => return .mkBlock (← (← getArrF j "stmts").mapM parseSStmt)
  | "BlockingAssign" =>
      let target ← getF j "target"
      let targetKind ← getStrF target "kind"
      if targetKind == "ConcatTarget" then
        return .packedAssign (← parsePackedTargets target) (← parseSExpr (← getF j "value"))
      else if targetKind == "SelectTarget" then
        let width ← getNatF target "width"
        if width == 0 then throw "selected assignment target has zero width"
        return .selectedAssign (← targetName (← getF target "value")) width
          (← getBoolF target "descending") (← getBoolF target "index_signed")
          (← getBoolF target "two_state") (← parseSExpr (← getF target "index"))
          (← parseSExpr (← getF j "value"))
      else
        return .mkAssign false (← targetName target) (← parseSExpr (← getF j "value"))
  | "DistUniformAssign" =>
      let low ← getIntF j "low"
      let high ← getIntF j "high"
      if high < low || low < -2147483648 || high > 2147483647 then
        throw "dist_uniform assignment bounds are outside the admitted signed 32-bit slice"
      return .distUniformAssign (← getStrF j "target") (← getStrF j "seed")
        low high (← getBoolF j "two_state")
  | "Scanf" =>
      let format ← FormattedInput.parse (← getStrF j "format")
      let outputs ← (← getArrF j "outputs").toList.mapM parsePackedTargets
      if FormattedInput.destinations format != outputs.length then
        throw "Scanf: output arity requires diagnostics"
      return .scanf (← parseSExpr (← getF j "input")) format outputs
        (← parsePackedTargets (← getF j "result"))
  | "NonblockingAssign" =>
      let target ← getF j "target"
      let targetKind ← getStrF target "kind"
      if targetKind == "SelectTarget" then
        let width ← getNatF target "width"
        if width == 0 then throw "selected assignment target has zero width"
        return .selectedNbaAssign (← targetName (← getF target "value")) width
          (← getBoolF target "descending") (← getBoolF target "index_signed")
          (← getBoolF target "two_state") (← parseSExpr (← getF target "index"))
          (← parseSExpr (← getF j "value"))
      else if targetKind == "ConcatTarget" then
        return .packedNbaAssign (← parsePackedTargets target)
          (← parseSExpr (← getF j "value"))
      else
        return .mkAssign true (← targetName target) (← parseSExpr (← getF j "value"))
  | "If" =>
      let elseB ← match getFOpt j "else" with
        | none => pure none
        | some je => pure (some (← parseSStmt je))
      return .mkIf (← parseSExpr (← getF j "cond"))
        (← parseSStmt (← getF j "then")) elseB
  | "For" =>
      return .forLoop (← (← getArrF j "initializers").mapM parseSStmt)
        (← parseSExpr (← getF j "condition"))
        (← (← getArrF j "steps").mapM parseSStmt)
        (← parseSStmt (← getF j "body"))
  | "Repeat" =>
      return .repeatLoop (← parseSExpr (← getF j "count"))
        (← getBoolF j "count_signed") (← parseSStmt (← getF j "body"))
  | "While" =>
      return .forLoop #[] (← parseSExpr (← getF j "condition")) #[]
        (← parseSStmt (← getF j "body"))
  | "DoWhile" =>
      return .doWhileLoop (← parseSExpr (← getF j "condition"))
        (← parseSStmt (← getF j "body"))
  | "Forever" =>
      return .forLoop #[] (.m0 (.lit (.ofNat 1 1))) #[]
        (← parseSStmt (← getF j "body"))
  | "Delay" =>
      let amount ← getNatF j "amount"
      if amount >= 2 ^ 64 then throw "delay exceeds the admitted integral range"
      let body ← parseSStmt (← getF j "body")
      return match body with
        | .skip => .delay amount
        | _ => .block #[.delay amount, body]
  | "WaitEvent" =>
      let signal ← getStrF j "signal"
      let edge ← getStrF j "edge"
      match edge with
      | "posedge" => return .waitEvent signal .pos
      | "negedge" => return .waitEvent signal .neg
      | "any" => return .waitEvent signal .any
      | _ => throw "unsupported WaitEvent edge"
  | "WaitCond" =>
      return .waitCond (← parseSExpr (← getF j "condition"))
  | "Break" => return .breakLoop
  | "Continue" => return .continueLoop
  | "LocalDecl" =>
      let init ← match getFOpt j "init" with
        | none => pure none
        | some ji => pure (some (← parseSExpr ji))
      return .localDecl (← getStrF j "name") (← getNatF j "width")
        (← getBoolF j "two_state") init
  | "SysCall" =>
      let name ← getStrF j "name"
      match name with
      | "$finish" | "$stop" =>
          let fatalTask := (getFOpt j "fatal_task").bind (·.getBool?.toOption)
          if name == "$finish" && fatalTask == some true then
            let args ← (← getArrF j "args").mapM parseSExpr
            let signed ← (← getArrF j "arg_signed").mapM fun b =>
              match b.getBool? with
              | .ok v => .ok v
              | .error _ => .error "arg_signed entries must be Bools"
            unless signed.size == args.size do
              throw "SysCall: args/arg_signed length mismatch"
            return .fatal (args.zip signed)
          return .finish
      | "$display" | "$write" =>
          let format := (getFOpt j "format").bind (·.getStr?.toOption)
          let args ← (← getArrF j "args").mapM parseSExpr
          let signed ← (← getArrF j "arg_signed").mapM fun b =>
            match b.getBool? with
            | .ok v => .ok v
            | .error _ => .error "arg_signed entries must be Bools"
          unless signed.size == args.size do
            throw "SysCall: args/arg_signed length mismatch"
          return .sysCall (name == "$write") format (args.zip signed)
      | "$strobe" =>
          let format := (getFOpt j "format").bind (·.getStr?.toOption)
          let args ← (← getArrF j "args").mapM parseSExpr
          let signed ← (← getArrF j "arg_signed").mapM fun b =>
            match b.getBool? with
            | .ok v => .ok v
            | .error _ => .error "arg_signed entries must be Bools"
          unless signed.size == args.size do
            throw "SysCall: args/arg_signed length mismatch"
          return .strobe format (args.zip signed)
      | "$monitor" =>
          let format := (getFOpt j "format").bind (·.getStr?.toOption)
          let args ← (← getArrF j "args").mapM parseSExpr
          let signed ← (← getArrF j "arg_signed").mapM fun b =>
            match b.getBool? with
            | .ok v => .ok v
            | .error _ => .error "arg_signed entries must be Bools"
          unless signed.size == args.size do
            throw "SysCall: args/arg_signed length mismatch"
          return .monitor format (args.zip signed)
      | "$info" | "$warning" | "$error" =>
          let args ← (← getArrF j "args").mapM parseSExpr
          let signed ← (← getArrF j "arg_signed").mapM fun b =>
            match b.getBool? with
            | .ok v => .ok v
            | .error _ => .error "arg_signed entries must be Bools"
          unless signed.size == args.size do
            throw "SysCall: args/arg_signed length mismatch"
          return .severity (args.zip signed)
      | other => .error s!"unknown SysCall name '{other}'"
  | "Empty" => return .skip
  | "Unsupported" =>
      return .m0 (.unsupported (← getStrF j "sv_kind") (unsupportedText j))
  | other => .error s!"unknown statement kind '{other}'"

def parseSProc (j : Json) : Except String SProc := do
  let kind ← getStrF j "kind"
  match kind with
  | "Initial" => return .initial (← parseSStmt (← getF j "body"))
  | "Always" => return .alwaysBody (← parseSStmt (← getF j "body"))
  | "AlwaysImplicit" =>
      return .alwaysImplicit (← parseSStmt (← getF j "body"))
  | "AlwaysPosedge" =>
      let body ← parseSStmt (← getF j "body")
      let style := (getStrF j "style").toOption.getD "always"
      if style == "always_ff" then
        let clock ← getStrF j "clock"
        match (getStrF j "areset_n").toOption with
        | some reset => return .alwaysFFReset clock reset body
        | none =>
            match (getStrF j "edge").toOption.getD "pos" with
            | "pos" => return .alwaysFF clock body
            | "neg" => return .alwaysFFNegedge clock body
            | edge => throw s!"AlwaysPosedge: unknown edge '{edge}'"
      else
        let clock ← getStrF j "clock"
        match (getStrF j "edge").toOption.getD "pos" with
        | "pos" => return .alwaysPosedge clock body
        | "neg" => return .alwaysNegedge clock body
        | edge => throw s!"AlwaysPosedge: unknown edge '{edge}'"
  | "AlwaysComb" =>
      return .alwaysComb (← parseSStmt (← getF j "body"))
  | "AlwaysLatch" =>
      return .alwaysLatch (← parseSStmt (← getF j "body"))
  | "Assign" =>
      let target ← getF j "target"
      if (getStrF target "kind").toOption != some "Ident" then
        return .other "Assign" "continuous assignment target is outside the timed tier"
      else
        return .assign (← targetName target) (← parseSExpr (← getF j "value"))
  | "Unsupported" =>
      return .other (← getStrF j "sv_kind") (unsupportedText j)
  | other => .error s!"unknown process kind '{other}'"

/-- `Port` → declaration, retaining input direction and two-state conversion.
Unsupported ports poison the design via an `.other` proc. -/
def parsePortD (j : Json) : Except String (Sum SDecl SProc) := do
  match ← getStrF j "kind" with
  | "Port" =>
      let dir ← getStrF j "dir"
      let isSigned ← match getFOpt j "signed" with
        | none => pure false
        | some _ => getBoolF j "signed"
      let twoState ← match getFOpt j "two_state" with
        | none => pure false
        | some value => match value.getBool? with
          | .ok b => pure b
          | .error _ => .error "field 'two_state' must be a Bool"
      let init ← match getFOpt j "init" with
        | none => pure none
        | some value => some <$> parseSExpr value
      return .inl { name := ← getStrF j "name", width := ← getNatF j "width"
                    isInput := dir == "in", isOutput := dir == "out", isSigned, twoState, init }
  | "Unsupported" =>
      return .inr (.other (← getStrF j "sv_kind") (unsupportedText j))
  | k => .error s!"unknown port kind '{k}'"

def parseSDecl (j : Json) : Except String (Sum SDecl SProc) := do
  match ← getStrF j "kind" with
  | "Var" | "Net" =>
      let isSigned ← match getFOpt j "signed" with
        | none => pure false
        | some _ => getBoolF j "signed"
      let init ← match getFOpt j "init" with
        | none => pure none
        | some ji => pure (some (← parseSExpr ji))
      return .inl { name := ← getStrF j "name", width := ← getNatF j "width"
                    isNet := (← getStrF j "kind") == "Net", isSigned, init }
  | "Unsupported" =>
      return .inr (.other (← getStrF j "sv_kind") (unsupportedText j))
  | k => .error s!"unknown decl kind '{k}'"

/-- Local declaration names of a body (for the flat-state shadow check). -/
partial def localNames : SStmt → List String
  | .localDecl name _ _ _ => [name]
  | .block body => body.toList.flatMap localNames
  | .ifStmt _ t e => localNames t ++ (match e with | some s => localNames s | none => [])
  | .forLoop initializers _ steps body =>
      initializers.toList.flatMap localNames ++ steps.toList.flatMap localNames ++ localNames body
  | .forAfterInit _ steps body | .forHeader _ steps body
  | .forAfterBody _ steps body | .forAfterStep _ steps body =>
      steps.toList.flatMap localNames ++ localNames body
  | .repeatLoop _ _ body | .repeatBody _ body | .repeatAfterBody _ body
  | .doWhileLoop _ body => localNames body
  | _ => []

/-- Preserve time-zero query provenance through envelope ingestion.

The expression parser intentionally shares ordinary literal evaluation with
M0. Keep its admission restriction at design scope so a timed loader cannot
silently turn the approximation into a clock-independent value. This walk is
in the ingestion layer, alongside the other partial JSON parsers. -/
partial def hasTimeZeroLiteral : Json → Bool
  | .obj fields =>
      (fields.get? "kind" == some (.str "Literal") &&
        fields.get? "time_zero" == some (.bool true)) ||
      fields.toArray.any (fun (_, value) => hasTimeZeroLiteral value)
  | .arr values => values.any hasTimeZeroLiteral
  | _ => false

/-- One `Module` payload → self-check `Design`. Ports and vars/nets share
the flat state; module `others` and unsupported members become `.other`
processes (loud at run). The state is a flat namespace, so a local decl
shadowing a module-level name, or re-declared within one process, is a
parse error (its SV scoping semantics would be silently wrong here). -/
def parseModuleD (j : Json) : Except String Design := do
  let name ← getStrF j "name"
  let mut decls : Array SDecl := #[]
  let mut procs : Array SProc := #[]
  for pj in ← getArrF j "ports" do
    match ← parsePortD pj with
    | .inl d => decls := decls.push d
    | .inr p => procs := procs.push p
  for dj in ← getArrF j "decls" do
    -- Declaration-only extractor slices may erase a source declaration to
    -- `Empty` when its value is never represented (for example, a mixed
    -- fixed/dynamic array used only by dimension metadata queries).  It has
    -- no flat state to initialize and must be skipped at ingestion, just as
    -- statement-level `Empty` is skipped by `parseSStmt`.
    if (getStrF dj "kind").toOption == some "Empty" then
      pure ()
    else
      match ← parseSDecl dj with
      | .inl d => decls := decls.push d
      | .inr p => procs := procs.push p
  for pj in ← getArrF j "processes" do
    procs := procs.push (← parseSProc pj)
  let others ← getArrF j "others"
  for oj in others do
    procs := procs.push (.other ((getStrF oj "sv_kind").toOption.getD "ModuleOther")
      (unsupportedText oj))
  -- Flat-state shadow check.
  let moduleNames := decls.toList.map (·.name)
  for p in procs do
    let body? := match p with
      | .initial body | .alwaysBody body | .alwaysImplicit body
      | .alwaysComb body
      | .alwaysLatch body => some body
      | _ => none
    if let some body := body? then
      let ln := localNames body
      for n in ln do
        if moduleNames.contains n then
          throw s!"local variable '{n}' shadows a module-level declaration (flat state)"
      if ln.length != ln.eraseDups.length then
        throw "duplicate local variable declarations within one process (flat state)"
  return { name, decls, procs, requiresTimeZero := hasTimeZeroLiteral j }

/-- Resolve explicit immutable inputs before parsing the ordinary statement
vocabulary. Stateful queries compile to existing copyback and assignment nodes;
the process keeps its original control placement and retained continuation. -/
partial def specializePlusargs (inputs : Option (List String)) (j : Json) : Except String Json := do
  match j with
  | .arr values => return .arr (← values.mapM (specializePlusargs inputs))
  | .obj fields =>
      let kind := (getStrF j "kind").toOption.getD ""
      if kind == "TestPlusargs" || kind == "ValuePlusargs" then
        let some inputs := inputs | throw "Plusargs: supply explicit command-line inputs"
        unless inputs.all Plusargs.ascii do throw "Plusargs: non-ASCII or NUL input"
        let text ← getStrF j "format"
        unless Plusargs.ascii text do throw "Plusargs: non-ASCII or NUL format"
        let literal (value : LVec) : Json := Json.mkObj [
          ("kind", .str "Literal"), ("width", Lean.toJson value.width),
          ("bits", .str value.toBinString)]
        if kind == "TestPlusargs" then
          return literal (.ofNat 32 (if Plusargs.test inputs text then 1 else 0))
        let format ← Plusargs.parse text
        let target ← specializePlusargs (some inputs) (← getF j "target")
        let targets ← parsePackedTargets target
        let width := targets.foldl (fun n t => n + t.width) 0
        let value ← Plusargs.value inputs format width
        let result ← getF j "result"
        let assign (target value : Json) : Json := Json.mkObj [
          ("kind", .str "BlockingAssign"), ("target", target), ("value", value)]
        let resultWrite := assign result (literal (.ofNat 32 (if value.isSome then 1 else 0)))
        let writes := match value with
          | none => #[resultWrite]
          | some value =>
              -- A one-part concatenation delegates state-kind conversion and
              -- selected copyback to the existing packed assignment operation.
              let target := Json.mkObj [("kind", .str "ConcatTarget"),
                ("width", Lean.toJson width), ("parts", .arr #[target])]
              #[assign target (literal value), resultWrite]
        return Json.mkObj [("kind", .str "Block"), ("stmts", .arr writes)]
      return Json.mkObj (← fields.toArray.toList.mapM fun (key, value) => do
        return (key, ← specializePlusargs inputs value))
  | _ => return j

/-- Envelope text → self-check `Design`. Validates the single-module shape.
Input-dependent envelopes require `loadEnvelopeDesignWithPlusargs`. -/
def loadEnvelopeDesignInputs (inputs : Option (List String)) (text : String) : Except String Design := do
  let j ← Json.parse text
  let sv ← getStrF j "schema_version"
  unless sv == "sv-0.1" do throw s!"unsupported schema_version '{sv}' (want sv-0.1)"
  let lang ← getStrF j "language"
  unless lang == "systemverilog" do throw s!"unsupported language '{lang}'"
  let design ← specializePlusargs inputs (← getF j "design")
  let modules ← getArrF design "modules"
  let dOthers ← getArrF design "others"
  unless dOthers.isEmpty do throw s!"design.others is non-empty ({dOthers.size} node(s))"
  match modules with
  | #[m] => parseModuleD m
  | ms => .error s!"expected exactly one module in the envelope, got {ms.size}"

/-! ## Tests — value helpers and rendering (Xcelium 24.03 fixtures) -/

section Tests

-- squash2 / resize
#guard squash2v (.lit "1x0z") == .lit "1000"
#guard resizeV 8 (.lit "101x") == .lit "0000101x"
#guard resizeV 2 (.lit "0110") == .lit "10"
#guard resizeV 4 (.lit "1111") == .lit "1111"
#guard LVec.resizeSigned (.lit "101x") 8 == .lit "1111101x"
#guard LVec.resizeSigned (.lit "x010") 8 == .lit "xxxxx010"
#guard LVec.resizeSigned (.lit "z010") 8 == .lit "zzzzz010"
#guard LVec.resizeSigned (.lit "0110") 2 == .lit "10"

-- signed comparison: 4'b1111 (=-1) vs 4'b0000
#guard evalScmp .lt (.lit "1111") (.lit "0000") == .l1
#guard LVec.lt (.lit "1111") (.lit "0000") == .l0   -- unsigned disagrees
#guard evalScmp .ge (.lit "0111") (.lit "1000") == .l1  -- 7 ≥ -8
#guard evalScmp .lt (.lit "1x11") (.lit "0000") == .lx  -- unknown → x
#guard toIntS? (.lit "1111") == some (-1)
#guard toIntS? (.lit "0111") == some 7

-- truthiness (&&/||)
#guard Logic.and (truthy (.lit "10")) (truthy (.lit "0x")) == .lx
#guard Logic.and (truthy (.lit "00")) (truthy (.lit "xx")) == .l0
#guard Logic.or (truthy (.lit "10")) (truthy (.lit "xx")) == .l1

-- %b / %0b (Xcelium T01–T06)
#guard renderBin (.lit "00001010") == "00001010"
#guard renderBin0 (.lit "00001010") == "1010"
#guard renderBin (.lit "xxxxxxxx") == "xxxxxxxx"
#guard renderBin0 (.lit "xxxxxxxx") == "x"
#guard renderBin0 (.lit "0000101x") == "101x"
#guard renderBin0 (.lit "00000000") == "0"

-- %h / %0h (T07–T10)
#guard renderHex (.lit "00001010") == "0a"
#guard renderHex (.lit "1x0z") == "X"
#guard renderHex (.lit "1x0z1010") == "Xa"
#guard renderHex0 (.lit "00000000000000000000000011111111") == "ff"
#guard renderHex (.lit "xxxxxxxx") == "xx"

-- %d / %0d (T11–T19)
#guard renderDec (.lit "00001010") false false == .ok " 10"
#guard renderDec (.lit "00001010") false true == .ok "10"
#guard renderDec (.lit "xxxxxxxx") false false == .ok "  x"
#guard renderDec (.lit "0000101x") false false == .ok "  X"
#guard renderDec (.lit "xxxxxxxx") false true == .ok "x"
#guard renderDec (.lit "0000101x") false true == .ok "X"
#guard renderDec (.ofNat 32 7) false false == .ok "         7"   -- 10 wide
#guard renderDec (.ofNat 32 7) true false == .ok "          7"   -- 11 wide (signed)
#guard renderDec (.ofNat 32 7) true true == .ok "7"
#guard renderDec (.lit "11111111") true true == .ok "-1"
#guard renderDec (.lit "11111111") true false == .ok "  -1"
#guard renderDec (.lit "10000000") true false == .ok "-128"

-- %s (T20–T21: NUL bytes render as spaces) and %c (T29)
#guard renderStr (.ofNat 24 0x414243) == .ok "ABC"
#guard renderStr (.ofNat 32 0x414243) == .ok " ABC"
#guard renderChr (.ofNat 8 65) == .ok "A"

-- full format strings (T22: `%%` is a runtime format escape — the string
-- literal VALUE still contains both chars; a bare `%` is loud)
#guard renderFmt "100%% done".toList [] == .ok "100% done"
#guard (renderFmt "100% done".toList []).toOption == none
#guard renderFmt "a=%b!".toList [(.lit "1x", false)] == .ok "a=1x!"
#guard (renderFmt "%b".toList []).toOption == none            -- missing arg
#guard (renderFmt "hi".toList [(.lit "1", false)]).toOption == none  -- extra arg
#guard (renderFmt "%m".toList []).toOption == none            -- out-of-tier spec

-- Out: $write concatenation and line splitting (T23)
#guard (((Out.emit {} "T23[").emit "a").emit "b]\n").flush == ["T23[ab]"]
#guard (Out.emit {} "x\ny").flush == ["x", "y"]

-- end-to-end: two initials, $finish stops the second
private def displayPass : SStmt :=
  .sysCall false (some "PASS %0d") #[(.m0 (.lit (.ofNat 8 42)), false)]

#guard runSelfCheck
  { name := "t", decls := #[], procs := #[.initial displayPass] } 1000
  == .ok ["PASS 42"]
#guard runSelfCheck
  { name := "t", decls := #[]
    procs := #[.initial (.block #[displayPass, .finish]),
               .initial (.sysCall false (some "NOT REACHED") #[])] } 1000
  == .ok ["PASS 42"]
-- non-initial process: loud
#guard (runSelfCheck
  { name := "t", decls := #[], procs := #[.other "ProceduralBlockSymbol:Final" ""] }
  1000).toOption == none
-- local decl + case equality + if/else, x-init module var
#guard runSelfCheck
  { name := "t"
    decls := #[{ name := "v", width := 4 }]
    procs := #[.initial (.block #[
      .localDecl "loc" 4 false (some (.m0 (.lit (.lit "101x")))),
      .ifStmt (.caseEq (.m0 (.ident "loc")) (.m0 (.lit (.lit "101x"))))
        (.sysCall false (some "PASS %b") #[(.m0 (.ident "v"), false)])
        (some (.sysCall false (some "FAIL") #[]))])] } 1000
  == .ok ["PASS xxxx"]
-- NBA inside initial: reads see pre-commit values (LRM active/NBA split)
#guard runSelfCheck
  { name := "t"
    decls := #[{ name := "a", width := 4, init := some (.m0 (.lit (.ofNat 4 1))) }]
    procs := #[.initial (.block #[
      .m0 (.nbaAssign "a" (.lit (.ofNat 4 2))),
      .sysCall false (some "%0d") #[(.m0 (.ident "a"), false)]])] } 1000
  == .ok ["1"]

end Tests

/-- Loading without an input environment refuses every plusargs query. -/
def loadEnvelopeDesign (text : String) : Except String Design :=
  loadEnvelopeDesignInputs none text

/-- Explicit ordered plusarg contents, without their leading command-line `+`.
An empty list explicitly represents an invocation with no plusargs. -/
def loadEnvelopeDesignWithPlusargs (inputs : List String) (text : String) : Except String Design :=
  loadEnvelopeDesignInputs (some inputs) text

end SelfCheck
end LeanModels.Sv
