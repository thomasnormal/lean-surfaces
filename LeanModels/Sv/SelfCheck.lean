import Lean
import LeanModels.Sv.Semantics

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
unsigned); `%s` renders NUL bytes as spaces. The envelope carries no
signedness, so `SysCall` args come with a parallel `arg_signed` list;
rendering a *negative* signed value with `%d` is `.unsupported` (loud)
rather than printing the unsigned reinterpretation.
-/

namespace LeanModels.Sv
namespace SelfCheck

/-! ## Value helpers (on top of `Basic.lean`'s `LVec`) -/

/-- 4-state → 2-state value conversion, LRM §6.3.1: `x`/`z` bits become 0.
Applied wherever the extractor inserted a `Squash2` node (assignments and
initializers whose target is a 2-state variable, and the corresponding
implicit conversions). -/
def squash2v (v : LVec) : LVec :=
  ⟨v.bits.map fun b => if b == .l1 then .l1 else .l0⟩

/-- Unsigned resize (the `Resize` node): zero-extend on the MSB side, or
keep the low `w` bits. The extractor emits `Resize` only for *unsigned*
operands, where the LRM extension rule is zero-fill (x/z bits are kept,
never extended). -/
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

/-! ## Self-check expressions -/

/-- Self-check expressions: M0 `Expr` embedded as a leaf (`.m0`, evaluated
by the existing `evalExpr` — the parser collapses maximal pure-M0 subtrees
into it) plus the §f extensions. `Expr.unsupported` leaves arrive inside
`.m0` and stay loud. -/
inductive SExpr where
  | m0 (e : Expr)
  | unary (op : UnaryOp) (a : SExpr)
  | binary (op : BinOp) (l r : SExpr)
  /-- Signed order comparison (`s<` `s<=` `s>` `s>=`); `op ∈ {lt,le,gt,ge}`. -/
  | scmp (op : BinOp) (l r : SExpr)
  | caseEq (l r : SExpr)   -- `===`
  | caseNe (l r : SExpr)   -- `!==`
  | logAnd (l r : SExpr)   -- `&&`
  | logOr (l r : SExpr)    -- `||`
  | resize (w : Nat) (a : SExpr)
  | squash2 (a : SExpr)
  | ternary (c t f : SExpr)
  | concat (parts : Array SExpr)
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

/-! ## Self-check statements -/

/-- Self-check statements: M0 `Stmt` embedded as a leaf (`.m0`, executed by
the existing `execStmt`; statement-level `Unsupported` arrives as
`.m0 (.unsupported …)`) plus the §f extensions. `sysCall` args carry the
envelope's `arg_signed` flag. -/
inductive SStmt where
  | m0 (s : Stmt)
  | assign (nonblocking : Bool) (target : String) (value : SExpr)
  | ifStmt (cond : SExpr) (thenB : SStmt) (elseB : Option SStmt)
  | block (body : Array SStmt)
  | localDecl (name : String) (width : Nat) (twoState : Bool) (init : Option SExpr)
  /-- `$display` (`write = false`, appends a newline) or `$write`. -/
  | sysCall (write : Bool) (format : Option String) (args : Array (SExpr × Bool))
  | finish  -- `$finish` and `$stop`: halt the run cleanly
  | skip    -- `;` (Empty)
deriving Repr, BEq, Inhabited

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

/-! ## Output collection -/

/-- Collected simulator output: finished `lines`, the unterminated tail
`cur` (`$write` without a newline), and the `halted` flag set by
`$finish`/`$stop`. -/
structure Out where
  lines : Array String := #[]
  cur : String := ""
  halted : Bool := false
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

/-- `%d`/`%0d`. Unknown bits render as the summary char. A fully known
value prints its unsigned decimal — for signed args only when the sign bit
is 0; a negative signed value is `.unsupported` (the envelope carries the
bit pattern, and printing `4294967295` for `-1` would be silently wrong). -/
def renderDec (v : LVec) (signed : Bool) (zero : Bool) : Res String :=
  match v.toNat? with
  | some n =>
      if signed && msb v == .l1 then
        .unsupported "negative signed value under %d (envelope carries no sign)"
      else
        .ok (if zero then toString n else padLeft (toString n) (dWidth v.width signed))
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

/-- One conversion spec applied to one argument. `zero` is the `%0` flag. -/
def renderSpec (c : Char) (zero : Bool) (v : LVec) (signed : Bool) : Res String :=
  match c.toLower with
  | 'b' => .ok (if zero then renderBin0 v else renderBin v)
  | 'h' => .ok (if zero then renderHex0 v else renderHex v)
  | 'x' => .ok (if zero then renderHex0 v else renderHex v)
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
    | .logAnd l r => do
        return .ofLogic (Logic.and (truthy (← evalSExpr fuel st l)) (truthy (← evalSExpr fuel st r)))
    | .logOr l r => do
        return .ofLogic (Logic.or (truthy (← evalSExpr fuel st l)) (truthy (← evalSExpr fuel st r)))
    | .resize w a => do
        return resizeV w (← evalSExpr fuel st a)
    | .squash2 a => do
        return squash2v (← evalSExpr fuel st a)
    | .ternary c t f => do
        let cv ← evalSExpr fuel st c
        let tv ← evalSExpr fuel st t
        let fv ← evalSExpr fuel st f
        return LVec.ternary cv tv fv
    | .concat parts => do
        return LVec.concatMany (← evalSExprs fuel st parts.toList).toArray

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

/-- Execute one self-check statement, threading state, NBA queue, and
output. A halted `Out` short-circuits (`$finish` skips the rest of the
run). `.m0` subtrees run under the existing `execStmt`. -/
def execSStmt (fuel : Nat) (st : SvState) (nba : NbaQueue) (out : Out)
    (stmt : SStmt) : Res (SvState × NbaQueue × Out) :=
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
      | .ifStmt cond thenB elseB => do
          let c ← evalSExpr fuel st cond
          if c.condTrue then
            execSStmt fuel st nba out thenB
          else
            match elseB with
            | some s => execSStmt fuel st nba out s
            | none => .ok (st, nba, out)
      | .block body => execSStmts fuel st nba out body.toList
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
      | .finish => .ok (st, nba, { out with halted := true })
      | .skip => .ok (st, nba, out)

/-- Execute statements in order. -/
def execSStmts (fuel : Nat) (st : SvState) (nba : NbaQueue) (out : Out)
    (ss : List SStmt) : Res (SvState × NbaQueue × Out) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match ss with
    | [] => .ok (st, nba, out)
    | s :: rest => do
        let (st', nba', out') ← execSStmt fuel st nba out s
        execSStmts fuel st' nba' out' rest

end

/-! ## Designs and the runner -/

/-- One module-level declaration. `init` is the (possibly synthesized —
2-state vars) initializer; a var without one starts all-x (§6.8), a net
all-z (undriven). Port direction is irrelevant at time 0 (undriven inputs
are x, exactly the LRM elaboration of an unconnected top). -/
structure SDecl where
  name : String
  width : Nat
  isNet : Bool := false
  init : Option SExpr := none
deriving Repr, Inhabited

/-- A self-check process: an `initial` body, or anything else (kept with
its envelope tag — `runSelfCheck` is loud on it, never silently drops). -/
inductive SProc where
  | initial (body : SStmt)
  | other (svKind : String) (text : String)
deriving Repr, Inhabited

/-- A self-check design (the analog of `Sv.Design` for this tier). -/
structure Design where
  name : String
  decls : Array SDecl
  procs : Array SProc
deriving Repr, Inhabited

/-- Initialize declarations in order (later initializers may read earlier
signals; reading a not-yet-declared one is loud via `readSignal`). -/
def initDecls (fuel : Nat) : List SDecl → SvState → Res SvState
  | [], st => .ok st
  | dc :: rest, st => do
      let v ← match dc.init with
        | none => pure (if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width)
        | some e => evalSExpr fuel st e
      initDecls fuel rest (SvState.set st dc.name v)

/-- Run the initial processes once each, in source order, at time 0.
Any non-initial process is loud. A halt (`$finish`) stops the fold. -/
def runInits (fuel : Nat) : List SProc → SvState → NbaQueue → Out →
    Res (SvState × NbaQueue × Out)
  | [], st, nba, out => .ok (st, nba, out)
  | .other svKind _ :: _, _, _, _ =>
      .unsupported s!"non-initial process '{svKind}' (self-check tier runs initial-only designs)"
  | .initial body :: rest, st, nba, out => do
      let (st', nba', out') ← execSStmt fuel st nba out body
      if out'.halted then .ok (st', nba', out')
      else runInits fuel rest st' nba' out'

/-- The self-check entry point: execute every `initial` process once at
time 0 (source order), collecting the rendered `$display` output lines.
`$finish` ends the run cleanly. The time-0 NBA queue commits after all
initials — after the last possible output, so it is dropped here. -/
def runSelfCheck (d : Design) (fuel : Nat) : Res (List String) := do
  if let some tag := d.procs.findSome? fun p =>
      match p with | .other svKind _ => some svKind | _ => none then
    return ← .unsupported
      s!"non-initial process '{tag}' (self-check tier runs initial-only designs)"
  let st ← initDecls fuel d.decls.toList []
  let (_, _, out) ← runInits fuel d.procs.toList st [] {}
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
  | "&&" => .ok (.logAnd l r)
  | "||" => .ok (.logOr l r)
  | other => .error s!"unknown binary op '{other}'"

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
      | other => .error s!"unknown unary op '{other}'"
  | "Binary" =>
      let l ← parseSExpr (← getF j "left")
      let r ← parseSExpr (← getF j "right")
      parseSBinOp (← getStrF j "op") l r
  | "Ternary" =>
      return .mkTernary (← parseSExpr (← getF j "cond"))
        (← parseSExpr (← getF j "then")) (← parseSExpr (← getF j "else"))
  | "Concat" =>
      return .mkConcat (← (← getArrF j "parts").mapM parseSExpr)
  | "Resize" =>
      return .resize (← getNatF j "width") (← parseSExpr (← getF j "operand"))
  | "Squash2" =>
      return .squash2 (← parseSExpr (← getF j "operand"))
  | "Unsupported" =>
      return .m0 (.unsupported (← getStrF j "sv_kind") (unsupportedText j))
  | other => .error s!"unknown expression kind '{other}'"

/-- Assignment target: the schema guarantees an `Ident` node. -/
def targetName (j : Json) : Except String String := do
  match ← parseSExpr j with
  | .m0 (.ident n) => .ok n
  | .m0 (.unsupported svKind _) => .error s!"unsupported assignment target ({svKind})"
  | _ => .error "assignment target is not a plain identifier"

partial def parseSStmt (j : Json) : Except String SStmt := do
  let kind ← getStrF j "kind"
  match kind with
  | "Block" => return .mkBlock (← (← getArrF j "stmts").mapM parseSStmt)
  | "BlockingAssign" =>
      return .mkAssign false (← targetName (← getF j "target"))
        (← parseSExpr (← getF j "value"))
  | "NonblockingAssign" =>
      return .mkAssign true (← targetName (← getF j "target"))
        (← parseSExpr (← getF j "value"))
  | "If" =>
      let elseB ← match getFOpt j "else" with
        | none => pure none
        | some je => pure (some (← parseSStmt je))
      return .mkIf (← parseSExpr (← getF j "cond"))
        (← parseSStmt (← getF j "then")) elseB
  | "LocalDecl" =>
      let init ← match getFOpt j "init" with
        | none => pure none
        | some ji => pure (some (← parseSExpr ji))
      return .localDecl (← getStrF j "name") (← getNatF j "width")
        (← getBoolF j "two_state") init
  | "SysCall" =>
      let name ← getStrF j "name"
      match name with
      | "$finish" | "$stop" => return .finish
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
      | other => .error s!"unknown SysCall name '{other}'"
  | "Empty" => return .skip
  | "Unsupported" =>
      return .m0 (.unsupported (← getStrF j "sv_kind") (unsupportedText j))
  | other => .error s!"unknown statement kind '{other}'"

def parseSProc (j : Json) : Except String SProc := do
  let kind ← getStrF j "kind"
  match kind with
  | "Initial" => return .initial (← parseSStmt (← getF j "body"))
  | "AlwaysPosedge" | "AlwaysComb" | "Assign" =>
      return .other kind ""
  | "Unsupported" =>
      return .other (← getStrF j "sv_kind") (unsupportedText j)
  | other => .error s!"unknown process kind '{other}'"

/-- `Port` → declaration (starts all-x, exactly an unconnected top-level
input/output). Unsupported ports poison the design via an `.other` proc. -/
def parsePortD (j : Json) : Except String (Sum SDecl SProc) := do
  match ← getStrF j "kind" with
  | "Port" =>
      return .inl { name := ← getStrF j "name", width := ← getNatF j "width" }
  | "Unsupported" =>
      return .inr (.other (← getStrF j "sv_kind") (unsupportedText j))
  | k => .error s!"unknown port kind '{k}'"

def parseSDecl (j : Json) : Except String (Sum SDecl SProc) := do
  match ← getStrF j "kind" with
  | "Var" | "Net" =>
      let init ← match getFOpt j "init" with
        | none => pure none
        | some ji => pure (some (← parseSExpr ji))
      return .inl { name := ← getStrF j "name", width := ← getNatF j "width"
                    isNet := (← getStrF j "kind") == "Net", init }
  | "Unsupported" =>
      return .inr (.other (← getStrF j "sv_kind") (unsupportedText j))
  | k => .error s!"unknown decl kind '{k}'"

/-- Local declaration names of a body (for the flat-state shadow check). -/
partial def localNames : SStmt → List String
  | .localDecl name _ _ _ => [name]
  | .block body => body.toList.flatMap localNames
  | .ifStmt _ t e => localNames t ++ (match e with | some s => localNames s | none => [])
  | _ => []

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
    if let .initial body := p then
      let ln := localNames body
      for n in ln do
        if moduleNames.contains n then
          throw s!"local variable '{n}' shadows a module-level declaration (flat state)"
      if ln.length != ln.eraseDups.length then
        throw "duplicate local variable declarations within one process (flat state)"
  return { name, decls, procs }

/-- Envelope text → self-check `Design`. Validates `schema_version`/
`language` and the single-module shape. -/
def loadEnvelopeDesign (text : String) : Except String Design := do
  let j ← Json.parse text
  let sv ← getStrF j "schema_version"
  unless sv == "sv-0.1" do throw s!"unsupported schema_version '{sv}' (want sv-0.1)"
  let lang ← getStrF j "language"
  unless lang == "systemverilog" do throw s!"unsupported language '{lang}'"
  let design ← getF j "design"
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
#guard (renderDec (.lit "11111111") true true).toOption == none  -- negative signed: loud

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

end SelfCheck
end LeanModels.Sv
