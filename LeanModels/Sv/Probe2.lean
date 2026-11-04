import LeanModels.Sv.Hier2

/-!
# The multi-point cross-check (`PDesign.pointVerdict`, round 3 CX)

The extractor elaborates a symbolic envelope with slang at the DEFAULT
parameter point. Anything it computes there — a width, an offset, a cell, a
sign — and writes into the symbolic tree is a **default-point fold**: right
at the defaults, silently wrong at every other point `P`, so `name.sem P`
describes a circuit no simulator builds. Rounds 1–2 found these one at a
time; this check turns the whole class into a loud refusal at the points
it is run at.

**The check.** For a parameter point `P`, the extractor re-runs the SAME
symbolic extraction with slang's top-level `paramOverrides` set to `P`
(`extract.py --probe-points`, written to the opt-in sidecar
`<file>.sv.probes.json`; `docs/sv-envelope-schema.md`, "Probe sidecars").
Slang then elaborates `P` itself, so any fold in the point extraction is
`P`'s own. Both modules are brought to `P` by the SAME `PDesign.atPoint`
and instantiated by the SAME `instantiateG2`/`instantiateH` (the
differential runner's and `name.sem`'s pipeline, one-driver rule
included; a point that overrides EVERY parameter is exactly `name.sem` at
those values), and the two `Design2` values are compared
(`Design2.compare`): declarations by `Decl`'s `BEq`, processes in order
by the structural equality `Process2.xeqT` after the width-identity
normalization `Process2.norm`. A fold differs between the two extractions,
so it shows up as a difference at `P`.

**Canonicalization (measured, not guessed).** Slang inserts a conversion
exactly where the widths at ITS point differ, so two equal circuits can
differ by identity resizes; `Expr2.norm` removes exactly those (rules 0–5
below, each an equation of `evalExpr2` on width-correct values), and two
loud nodes are equal when their KINDS are, whatever their message. On the
2026-10-28 sweep (66 parametric envelopes, 967 points, 1145 entries) this
took the comparison from 36 false mismatches to none.

**Three outcomes of a comparison.** Equal; equal EXCEPT where one side is
loud (`DesignCmp.loudOnly` → `ProbeVerdict.unconfirmed`: typically the
point extraction refuses a conversion slang inserts only at `P`, e.g.
`ConversionExpression:width` on a 32-bit `N` compared against a 40-bit
case subject — nothing then vouches for the envelope's value there); or a
difference between two VALUES (`ProbeVerdict.differ`: a SILENT
default-point fold).

**Also checked at `P`.** The point extraction carries slang's own
`resolved` metadata AT `P` (parameter values, localparams, declared widths,
top-level generate counts); `PDesign.crossCheck` of the point module
replays the Lean elaboration at `P` against it — the load gate's
Lean-vs-slang differential, extended from the defaults to every probe
point. A frontend error count `> 0` at `P` (slang rejects the top there:
the extractor elaborates the `--top` module ALONE at a probe point, so an
unrelated top-level module of the same sources neither receives `P` nor
counts — round 3 CX repair) is reported too: a family member no tool
accepts is not agreement.

**Instances.** For a hierarchical envelope every instance of the
`P`-elaborated hierarchy is probed the same way: its definition is
re-extracted ALONE at the overrides that instance receives at `P`
(`PInst.given`'s point), and compared against the envelope's library
definition at the same overrides (`ProbeInst2`). Folds inside a child are
caught at the points the hierarchy actually uses.

**Verdicts.** `.agree` is the only passing verdict (`ProbeVerdict.ok`,
`PDesign.pointAgrees`): a refusal on either side (`instantiate` failing,
an unprobed instance) and an unconfirmed node count as mismatches, never as
agreement.

**Not covered** (recorded): folds whose dependency is a GENVAR rather than
a parameter (the extractor binds a generate-for body from its first
iteration at every point alike — a per-iteration comparison would need a
different probe), and folds at points nobody probes.

Consumers: `load_design_sv2` (`Ingest2.lean`) runs every point of a sidecar
when one exists; `harness/sv/runner2.lean` runs the case's own point when
the differential harness hands it one (`diff_test2.py --xcheck`, default
on); the svGolf checker calls `LeanModels.Sv.probeCheckString` /
`probeCheckFile` (`Ingest2.lean`).
-/

namespace LeanModels.Sv

/-! ## Loud-kind-insensitive structural equality

`xeqT false` is the comparison: syntactic equality, two loud nodes equal
when their KINDS are (whatever their message). `xeqT true` additionally
lets a loud node on EITHER side match anything at its position — it
separates "the two designs differ only where one of them refuses" (the
cross-check is unconfirmed there: `ProbeVerdict.unconfirmed`) from a
difference between two values (a silent fold: `ProbeVerdict.differ`). -/

/-- Structural equality of semantic-tier expressions (`tol`: a loud node
on either side matches anything). -/
partial def Expr2.xeqT (tol : Bool) : Expr2 → Expr2 → Bool
  | .unsupported k _, .unsupported k' _ => k == k' || tol
  | .unsupported _ _, _ | _, .unsupported _ _ => tol
  | .resizeSigned w a, .resizeSigned w' a' => w == w' && a.xeqT tol a'
  | .squash2 a, .squash2 a' => a.xeqT tol a'
  | .lit v, .lit v' => v == v'
  | .ident n, .ident n' => n == n'
  | .unary o a, .unary o' a' => o == o' && a.xeqT tol a'
  | .binary o l r, .binary o' l' r' => o == o' && l.xeqT tol l' && r.xeqT tol r'
  | .scmp o l r, .scmp o' l' r' => o == o' && l.xeqT tol l' && r.xeqT tol r'
  | .logical b l r, .logical b' l' r' => b == b' && l.xeqT tol l' && r.xeqT tol r'
  | .ternary c t e, .ternary c' t' e' => c.xeqT tol c' && t.xeqT tol t' && e.xeqT tol e'
  | .concat ps, .concat ps' =>
      ps.size == ps'.size && (ps.toList.zip ps'.toList).all fun (x, y) => x.xeqT tol y
  | .slice b lo w, .slice b' lo' w' => lo == lo' && w == w' && b.xeqT tol b'
  | .index b i w, .index b' i' w' => w == w' && b.xeqT tol b' && i.xeqT tol i'
  | .repl c a, .repl c' a' => c == c' && a.xeqT tol a'
  | .reduce o a, .reduce o' a' => o == o' && a.xeqT tol a'
  | .resize w a, .resize w' a' => w == w' && a.xeqT tol a'
  | _, _ => false

/-- `Expr2.xeqT` on assignment targets. -/
partial def Lhs2.xeqT (tol : Bool) : Lhs2 → Lhs2 → Bool
  | .ident n, .ident n' => n == n'
  | .slice n lo w, .slice n' lo' w' => n == n' && lo == lo' && w == w'
  | .index n i w, .index n' i' w' => n == n' && w == w' && i.xeqT tol i'
  | .concat ps, .concat ps' =>
      ps.length == ps'.length && (ps.zip ps').all fun (x, y) => x.xeqT tol y
  | _, _ => false

mutual
/-- `Expr2.xeqT` on statements. -/
partial def Stmt2.xeqT (tol : Bool) : Stmt2 → Stmt2 → Bool
  | .unsupported k _, .unsupported k' _ => k == k' || tol
  | .unsupported _ _, _ | _, .unsupported _ _ => tol
  | .blockingAssign t v, .blockingAssign t' v' => t.xeqT tol t' && v.xeqT tol v'
  | .nbaAssign t v, .nbaAssign t' v' => t.xeqT tol t' && v.xeqT tol v'
  | .ifStmt c t e, .ifStmt c' t' e' =>
      c.xeqT tol c' && t.xeqT tol t' &&
        (match e, e' with
         | none, none => true
         | some x, some y => x.xeqT tol y
         | _, _ => false)
  | .block b, .block b' =>
      b.size == b'.size && (b.toList.zip b'.toList).all fun (x, y) => x.xeqT tol y
  | .caseStmt s is d i c, .caseStmt s' is' d' i' c' =>
      i == i' && c == c' && s.xeqT tol s' &&
        is.size == is'.size && (is.toList.zip is'.toList).all (fun (x, y) => x.xeqT tol y) &&
        (match d, d' with
         | none, none => true
         | some x, some y => x.xeqT tol y
         | _, _ => false)
  | _, _ => false

/-- `Expr2.xeqT` on case arms. -/
partial def CaseItem2.xeqT (tol : Bool) : CaseItem2 → CaseItem2 → Bool
  | .mk ps b, .mk ps' b' =>
      ps.size == ps'.size && (ps.toList.zip ps'.toList).all (fun (x, y) => x.xeqT tol y) &&
        b.xeqT tol b'
end

/-- `Expr2.xeqT` on processes. -/
def Process2.xeqT (tol : Bool) : Process2 → Process2 → Bool
  | .unsupported k _, .unsupported k' _ => k == k' || tol
  | .unsupported _ _, _ | _, .unsupported _ _ => tol
  | .alwaysFF c b, .alwaysFF c' b' => c == c' && b.xeqT tol b'
  | .alwaysPlain c b, .alwaysPlain c' b' => c == c' && b.xeqT tol b'
  | .alwaysComb b, .alwaysComb b' => b.xeqT tol b'
  | .assign t v, .assign t' v' => t.xeqT tol t' && v.xeqT tol v'
  | .alwaysFFR c r b, .alwaysFFR c' r' b' => c == c' && r == r' && b.xeqT tol b'
  | _, _ => false

/-- THE comparison (`xeqT false`): structural equality, loud nodes by kind. -/
abbrev Expr2.xeq := Expr2.xeqT false
@[inherit_doc Expr2.xeq] abbrev Lhs2.xeq := Lhs2.xeqT false
@[inherit_doc Expr2.xeq] abbrev Stmt2.xeq := Stmt2.xeqT false
@[inherit_doc Expr2.xeq] abbrev CaseItem2.xeq := CaseItem2.xeqT false
@[inherit_doc Expr2.xeq] abbrev Process2.xeq := Process2.xeqT false

/-! ## Width-identity normalization

Slang inserts a conversion node exactly where the widths at ITS point
differ; at another point the same source carries a conversion that is the
identity there, or none. Both instantiate to `Expr2.resize`, so two equal
circuits can differ by identity resizes. `Expr2.norm` removes exactly the
resizes that are the identity on every value of their operand's width, and
pushes a resize through a ternary — each rule an equation of `evalExpr2`'s
LVec semantics on width-correct values (every signal at its declared
width, the invariant instantiation maintains):

1. `resize w e`, `resizeSigned w e` ↦ `e` when `e` has width exactly `w`
   (`Expr2.cwidth`; `resizeU`/`resizeSigned` at the operand's own width are
   the identity);
2. `resize w (lit v)` ↦ `lit (v.resizeU w)`, `resizeSigned w (lit v)` ↦
   `lit (v.resizeSigned w)` (the evaluation itself);
3. `resize w (resize w' e)` ↦ `resize w e` when `w ≤ w'` (zero-extend then
   keep the low `w` bits = keep the low `w` bits);
4. `resize w (c ? a : b)` ↦ `c ? resize w a : resize w b` when `a`, `b` have
   one width (`LVec.ternary` returns an arm or their bitwise merge, and
   resizing commutes with both; `merge l0 l0 = l0` for the zero padding);
5. `resize w (a op b)` ↦ `resize w a op resize w b` for the bitwise
   `& | ^` when `a`, `b` have one width (`LVec.zipWith` is per bit, and
   `0 op 0 = 0` for the zero padding);
6. `resize w (a op b)` ↦ `resize w (a' op b')` for the arithmetic `+ - *`
   (round 3 folds) when `a`, `b` have one width `W` and both NARROW to a
   width `k` with `w ≤ k < W` (`Expr2.narrowTo`: a literal whose bits at and
   above `k` are 0/1 becomes its low `k` bits; a zero-extension `resize W
   e` of an `e` at most `k` bits wide becomes `e` zero-extended to `k`);
   `k` is the widest such zero-extended operand (or `w`). The low `w` bits
   of a sum, difference or product depend only on the operands' low bits,
   and the whole-vector x-collapse (§11.4.3) fires on the same operands
   either way: every bit dropped is a known 0/1. (The envelope's `a + B` at
   a narrower point against slang's `resize w (resize 8 a + 8'hfd)` there,
   rows `fold_sparam_n3`, and the sweep points `N = 1, 2` of
   `fold_sparam`.)

Rule 0 (`Expr2.norm`): an expression with a loud operand IS that loud
operand (evaluation is strict in every operand). Nothing else is rewritten
(arithmetic does NOT commute with truncation under the whole-vector
x-collapse when an x can sit above the truncation — rule 6 is exactly the
case where none can), so a fold that changes a value still differs. -/

/-- The result width of an expression under `evalExpr2`, when it is
independent of the operand VALUES (`none` = unknown, never guessed):
declared widths for identifiers (`ws`), `max` for the arithmetic/bitwise
binaries (`LVec.arithWidth`, `zipWith`), the left width for shifts and
`**`, 1 for comparisons, logical operators, reductions and `!`, a ternary
only when both arms have one width. -/
partial def Expr2.cwidth (ws : List (String × Nat)) : Expr2 → Option Nat
  | .lit v => some v.width
  | .ident n => ws.lookup n
  | .resize w _ | .resizeSigned w _ => some w
  | .squash2 a => a.cwidth ws
  | .slice _ _ w | .index _ _ w => some w
  | .unary .lnot _ => some 1
  | .unary _ a => a.cwidth ws
  | .binary op l r =>
      match op with
      | .add | .sub | .mul | .div | .sdiv | .rem | .srem | .and | .or | .xor =>
          match l.cwidth ws, r.cwidth ws with
          | some a, some b => some (max a b)
          | _, _ => none
      | .pow _ _ | .shl _ | .shr _ | .ashl _ | .ashr _ => l.cwidth ws
      | _ => some 1
  | .scmp _ _ _ | .logical _ _ _ | .reduce _ _ => some 1
  | .ternary _ t f =>
      match t.cwidth ws, f.cwidth ws with
      | some a, some b => if a == b then some a else none
      | _, _ => none
  | .concat ps => ps.toList.foldlM (fun acc p => (acc + ·) <$> p.cwidth ws) 0
  | .repl n a => (n * ·) <$> a.cwidth ws
  | .unsupported _ _ => none

/-- `e` narrowed to `k` bits when every bit of `e` at and above `k` is a
known 0/1 (rule 6): a literal's low `k` bits, or a zero-extension
`resize W e'` of an `e'` at most `k` bits wide as `e'` zero-extended to `k`.
`none` for anything else. -/
partial def Expr2.narrowTo (ws : List (String × Nat)) (k : Nat) : Expr2 → Option Expr2
  | .lit v =>
      if (v.bits.toList.drop k).all (fun b => b == .l0 || b == .l1) then some (.lit (v.resizeU k))
      else none
  | .resize _ e => match e.cwidth ws with
      | some x => if x == k then some e else if x < k then some (.resize k e) else none
      | none => none
  | _ => none

/-- The width a zero-extension `resize W e` holds information in (`e`'s);
`none` for other nodes (rule 6). -/
partial def Expr2.zextInner (ws : List (String × Nat)) : Expr2 → Option Nat
  | .resize _ e => e.cwidth ws
  | _ => none

mutual
/-- `resize w e` with `e` already normalized (rules 1–6). -/
partial def Expr2.normResize (ws : List (String × Nat)) (w : Nat) (e : Expr2) : Expr2 :=
  if e.cwidth ws == some w then e
  else
    match e with
    | .lit v => .lit (v.resizeU w)
    | .resize w' e' => if w ≤ w' then Expr2.normResize ws w e' else .resize w e
    | .ternary c a b =>
        match a.cwidth ws, b.cwidth ws with
        | some x, some y =>
            if x == y then .ternary c (Expr2.normResize ws w a) (Expr2.normResize ws w b)
            else .resize w e
        | _, _ => .resize w e
    | .binary op a b =>
        let bitwise := match op with
          | .and | .or | .xor => true
          | _ => false
        let arith := match op with
          | .add | .sub | .mul => true
          | _ => false
        match bitwise, a.cwidth ws, b.cwidth ws with
        | true, some x, some y =>
            if x == y then .binary op (Expr2.normResize ws w a) (Expr2.normResize ws w b)
            else .resize w e
        | false, some x, some y =>
            let k := max w (max ((a.zextInner ws).getD 0) ((b.zextInner ws).getD 0))
            if arith && x == y && k < x then
              match a.narrowTo ws k, b.narrowTo ws k with
              | some a', some b' => Expr2.normResize ws w (.binary op a' b')
              | _, _ => .resize w e
            else .resize w e
        | _, _, _ => .resize w e
    | _ => .resize w e

/-- Bottom-up width-identity normalization (`Expr2.normResize`), with
LOUD ABSORPTION (rule 0): `evalExpr2` evaluates every operand of every
node (both ternary arms, both logical operands, every concat part), so an
expression with a loud operand is loud on every evaluation, with the
first loud operand's message in evaluation order — the node is replaced
by that operand. -/
partial def Expr2.norm (ws : List (String × Nat)) (e : Expr2) : Expr2 :=
  let absorb (cs : List Expr2) (k : Unit → Expr2) : Expr2 :=
    match cs.find? (fun c => match c with | .unsupported _ _ => true | _ => false) with
    | some l => l
    | none => k ()
  match e with
  | .resize w a =>
      let a' := a.norm ws
      absorb [a'] fun _ => Expr2.normResize ws w a'
  | .resizeSigned w a =>
      let a' := a.norm ws
      absorb [a'] fun _ =>
        if a'.cwidth ws == some w then a'
        else match a' with
          | .lit v => .lit (v.resizeSigned w)
          | _ => .resizeSigned w a'
  | .squash2 a => let a' := a.norm ws; absorb [a'] fun _ => .squash2 a'
  | .unary o a => let a' := a.norm ws; absorb [a'] fun _ => .unary o a'
  | .binary o l r =>
      let l' := l.norm ws; let r' := r.norm ws
      absorb [l', r'] fun _ => .binary o l' r'
  | .scmp o l r =>
      let l' := l.norm ws; let r' := r.norm ws
      absorb [l', r'] fun _ => .scmp o l' r'
  | .logical b l r =>
      let l' := l.norm ws; let r' := r.norm ws
      absorb [l', r'] fun _ => .logical b l' r'
  | .ternary c t f =>
      let c' := c.norm ws; let t' := t.norm ws; let f' := f.norm ws
      absorb [c', t', f'] fun _ => .ternary c' t' f'
  | .concat ps =>
      let ps' := ps.map (·.norm ws)
      absorb ps'.toList fun _ => .concat ps'
  | .slice b lo w => let b' := b.norm ws; absorb [b'] fun _ => .slice b' lo w
  | .index b i w =>
      let b' := b.norm ws; let i' := i.norm ws
      absorb [b', i'] fun _ => .index b' i' w
  | .repl n a => let a' := a.norm ws; absorb [a'] fun _ => .repl n a'
  | .reduce o a => let a' := a.norm ws; absorb [a'] fun _ => .reduce o a'
  | e => e
end

/-- `Expr2.norm` inside a target's index expressions. -/
partial def Lhs2.norm (ws : List (String × Nat)) : Lhs2 → Lhs2
  | .index n i w => .index n (i.norm ws) w
  | .concat ps => .concat (ps.map (·.norm ws))
  | t => t

mutual
/-- `Expr2.norm` throughout a statement. -/
partial def Stmt2.norm (ws : List (String × Nat)) : Stmt2 → Stmt2
  | .blockingAssign t v => .blockingAssign (t.norm ws) (v.norm ws)
  | .nbaAssign t v => .nbaAssign (t.norm ws) (v.norm ws)
  | .ifStmt c t e => .ifStmt (c.norm ws) (t.norm ws) (e.map (Stmt2.norm ws))
  | .block b => .block (b.map (Stmt2.norm ws))
  | .caseStmt s is d i c =>
      .caseStmt (s.norm ws) (is.map (CaseItem2.norm ws)) (d.map (Stmt2.norm ws)) i c
  | s => s

/-- `Expr2.norm` throughout a case arm. -/
partial def CaseItem2.norm (ws : List (String × Nat)) : CaseItem2 → CaseItem2
  | .mk ps b => .mk (ps.map (·.norm ws)) (b.norm ws)
end

/-- `Expr2.norm` throughout a process. -/
def Process2.norm (ws : List (String × Nat)) : Process2 → Process2
  | .alwaysFF c b => .alwaysFF c (b.norm ws)
  | .alwaysPlain c b => .alwaysPlain c (b.norm ws)
  | .alwaysComb b => .alwaysComb (b.norm ws)
  | .assign t v => .assign (t.norm ws) (v.norm ws)
  | .alwaysFFR c r b => .alwaysFFR c r (b.norm ws)
  | p => p

/-! ## The first difference -/

/-- A short one-line rendering for a difference message (`repr` with its
line breaks and indentation collapsed to single spaces, cut at `n`). -/
def probeShow {α} [Repr α] (a : α) (n : Nat := 600) : String :=
  let cs := (toString (repr a)).toList.map fun c => if c == '\n' then ' ' else c
  let cs := (cs.foldl (fun (acc : List Char) c =>
    match acc with
    | ' ' :: _ => if c == ' ' then acc else c :: acc
    | _ => c :: acc) []).reverse
  let s := String.join (cs.map Char.toString)
  if s.length ≤ n then s else String.join ((cs.take n).map Char.toString) ++ " …"

/-! ## Zooming in on a difference -/

/-- A zoomed difference: the two innermost differing nodes, rendered, and
whether each one is a loud node. -/
abbrev ProbeZoom := String × String × Bool × Bool

/-- The innermost pair under two expressions that are not `xeqT tol`
(the first child pair that is not, recursively; heads that differ stop
the descent). -/
partial def Expr2.zoom (tol : Bool) (a b : Expr2) : ProbeZoom :=
  let pairs : List (Expr2 × Expr2) :=
    match a, b with
    | .resizeSigned w x, .resizeSigned w' y | .resize w x, .resize w' y =>
        if w == w' then [(x, y)] else []
    | .unary o x, .unary o' y | .reduce o x, .reduce o' y =>
        if o == o' then [(x, y)] else []
    | .binary o l r, .binary o' l' r' | .scmp o l r, .scmp o' l' r' =>
        if o == o' then [(l, l'), (r, r')] else []
    | .logical o l r, .logical o' l' r' => if o == o' then [(l, l'), (r, r')] else []
    | .ternary c t f, .ternary c' t' f' => [(c, c'), (t, t'), (f, f')]
    | .concat ps, .concat ps' => if ps.size == ps'.size then ps.toList.zip ps'.toList else []
    | .slice x lo w, .slice y lo' w' => if lo == lo' && w == w' then [(x, y)] else []
    | .index x i w, .index y i' w' => if w == w' then [(x, y), (i, i')] else []
    | .repl n x, .repl n' y => if n == n' then [(x, y)] else []
    | .squash2 x, .squash2 y => [(x, y)]
    | _, _ => []
  let loud : Expr2 → Bool
    | .unsupported _ _ => true
    | _ => false
  match pairs.find? (fun (x, y) => !x.xeqT tol y) with
  | some (x, y) => x.zoom tol y
  | none => (probeShow a 240, probeShow b 240, loud a, loud b)

/-- `Expr2.zoom` from a whole-node pair (no descent). -/
def probeLeaf {α} [Repr α] (a b : α) (la lb : Bool) : ProbeZoom :=
  (probeShow a 240, probeShow b 240, la, lb)

mutual
/-- `Expr2.zoom` for statements. -/
partial def Stmt2.zoom (tol : Bool) (a b : Stmt2) : ProbeZoom :=
  let loud : Stmt2 → Bool
    | .unsupported _ _ => true
    | _ => false
  let sub : Option ProbeZoom :=
    match a, b with
    | .blockingAssign t v, .blockingAssign t' v' | .nbaAssign t v, .nbaAssign t' v' =>
        if t.xeqT tol t' then (if v.xeqT tol v' then none else some (v.zoom tol v')) else none
    | .ifStmt c t e, .ifStmt c' t' e' =>
        if !c.xeqT tol c' then some (c.zoom tol c')
        else if !t.xeqT tol t' then some (t.zoom tol t')
        else match e, e' with
          | some x, some y => some (x.zoom tol y)
          | _, _ => none
    | .block bs, .block bs' =>
        if bs.size == bs'.size then
          ((bs.toList.zip bs'.toList).find? (fun (x, y) => !x.xeqT tol y)).map
            fun (x, y) => x.zoom tol y
        else none
    | .caseStmt sj is d _ _, .caseStmt sj' is' d' _ _ =>
        if !sj.xeqT tol sj' then some (sj.zoom tol sj')
        else if is.size == is'.size then
          match (is.toList.zip is'.toList).find? (fun (x, y) => !x.xeqT tol y) with
          | some (x, y) => some (x.zoom tol y)
          | none => match d, d' with
            | some x, some y => some (x.zoom tol y)
            | _, _ => none
        else none
    | _, _ => none
  sub.getD (probeLeaf a b (loud a) (loud b))

/-- `Expr2.zoom` for case arms. -/
partial def CaseItem2.zoom (tol : Bool) (a b : CaseItem2) : ProbeZoom :=
  match a, b with
  | .mk ps x, .mk ps' y =>
      if ps.size == ps'.size then
        match (ps.toList.zip ps'.toList).find? (fun (p, q) => !p.xeqT tol q) with
        | some (p, q) => p.zoom tol q
        | none => x.zoom tol y
      else probeLeaf a b false false
end

/-- `Expr2.zoom` for processes (an `assign` of a loud value counts as a
loud process: it refuses on every evaluation). -/
def Process2.zoom (tol : Bool) (a b : Process2) : ProbeZoom :=
  let loud : Process2 → Bool
    | .unsupported _ _ | .assign _ (.unsupported _ _) => true
    | _ => false
  match a, b with
  | .alwaysFF _ x, .alwaysFF _ y | .alwaysPlain _ x, .alwaysPlain _ y
  | .alwaysComb x, .alwaysComb y | .alwaysFFR _ _ x, .alwaysFFR _ _ y => x.zoom tol y
  | .assign t v, .assign t' v' =>
      if t.xeqT tol t' then v.zoom tol v' else probeLeaf a b false false
  | _, _ => probeLeaf a b (loud a) (loud b)

/-- The outcome of comparing two designs (`Design2.compare`). -/
inductive DesignCmp where
  /-- Equal (after `Process2.norm`). -/
  | equal
  /-- Equal except at nodes where one side (or both) is LOUD: one line per
  such node, `process #i: <who> refuses: envelope … / point …`. -/
  | loudOnly (msgs : List String)
  /-- A difference between two VALUES (or declarations): the first one. -/
  | differ (msg : String)
deriving Repr, Inhabited

/-- Compare two designs: declarations by `BEq`, processes by
`Process2.xeqT` after `Process2.norm` (at the declared widths, which are
equal by then), in order. Trailing extra processes are loud-only when
they are all loud nodes. -/
def Design2.compare (a b : Design2) : DesignCmp :=
  let ds := a.decls.toList
  let ds' := b.decls.toList
  match (ds.zip ds').zipIdx.find? (fun ((x, y), _) => !(x == y)) with
  | some ((x, y), i) =>
      .differ s!"declaration #{i} '{x.name}': envelope {probeShow x} ≠ point {probeShow y}"
  | none =>
    if ds.length != ds'.length then
      .differ s!"declaration count: envelope {ds.length} ≠ point {ds'.length}"
    else
      let ws := ds.map fun dc => (dc.name, dc.width)
      let ps := a.processes.toList.map (·.norm ws)
      let ps' := b.processes.toList.map (·.norm ws)
      let isLoud : Process2 → Bool
        | .unsupported _ _ => true
        | _ => false
      match (ps.zip ps').zipIdx.find? (fun ((x, y), _) => !x.xeqT true y) with
      | some ((x, y), i) =>
          let (zx, zy, _, _) := x.zoom true y
          .differ s!"process #{i}, first differing node: envelope {zx} ≠ point {zy}; process: envelope {probeShow x} ≠ point {probeShow y}"
      | none =>
          let extra := ps.drop ps'.length ++ ps'.drop ps.length
          if !extra.all isLoud then
            .differ s!"process count: envelope {ps.length} ≠ point {ps'.length} (an extra process is not loud)"
          else
            let msgs := ((ps.zip ps').zipIdx.filter (fun ((x, y), _) => !x.xeq y)).map
              fun ((x, y), i) =>
                let (zx, zy, lx, ly) := x.zoom false y
                let who := if lx && ly then "both refuse" else if ly then "the point extraction refuses"
                  else "the envelope refuses"
                s!"process #{i}: {who}: envelope {zx} / point {zy}"
            let tail := if extra.isEmpty then [] else
              [s!"process count: envelope {ps.length} ≠ point {ps'.length} (the extra processes are loud)"]
            match msgs ++ tail with
            | [] => .equal
            | ms => .loudOnly ms

/-! ## Instantiating one module at an override point -/

/-- `d` at the override point `ov` (`#(.P(v), …)`: the named parameters
overridden with integers, the rest at their defaults — `PDesign.atPoint`),
instantiated exactly as the differential runner and `name.sem` do: an
instance-free module through `instantiateG2`, a hierarchical one through
`instantiateH lib` (one-driver rule included either way), the flattened
names distinct. Any failure is the error message. -/
def PDesign.instAtOverrides (d : PDesign) (lib : List PDesign)
    (ov : List (String × Int)) : Except String Design2 := do
  for (n, _) in ov do
    unless d.params.any (·.name == n) do
      throw s!"'{n}' is not a parameter of '{d.name}'"
  let (d', args) ← d.atPoint (d.params.map fun p => ov.lookup p.name)
  let F := PDesign.surfaceFuel args
  let flat := lib.isEmpty || GenItem.listInstFree d'.generates
  match (if flat then d'.instantiateG2 args F else d'.instantiateH lib args F) with
  | .ok m =>
      if lib.isEmpty || m.namesNodup then .ok m
      else throw "two declarations of one name after flattening"
  | .timeout => throw "generate expansion fuel exhausted"
  | .unsupported msg => throw msg

/-! ## Verdicts -/

/-- The outcome of comparing one probe entry. -/
inductive ProbeVerdict where
  /-- Both instantiate, the designs are equal, and slang's metadata at the
  point agrees with the Lean elaboration there. The only passing verdict. -/
  | agree
  /-- Both instantiate and two VALUES differ (or a declaration does): a
  SILENT default-point fold — at least one extraction computes something
  at its own elaboration point that is wrong at the other. -/
  | differ (msg : String)
  /-- Both instantiate and are equal except where one side is LOUD: the
  cross-check cannot confirm the envelope's value at those nodes (the
  point extraction refuses there — slang's own tree at the point holds a
  construct the extractor does not admit — or the envelope does). Not a
  pass: nothing vouches for the envelope there. -/
  | unconfirmed (msgs : List String)
  /-- The point extraction's `resolved` metadata (slang AT the point)
  disagrees with the Lean elaboration at the point (`PDesign.crossCheck`). -/
  | metaDiffer (msgs : List String)
  /-- Slang reported `n` errors elaborating the top (alone) at the point. -/
  | frontendRejects (n : Nat)
  /-- One side does not instantiate (or the entry could not be probed). -/
  | refused (msg : String)
deriving Repr, BEq, Inhabited

/-- Passing = `.agree`. -/
def ProbeVerdict.ok : ProbeVerdict → Bool
  | .agree => true
  | _ => false

/-- The status word of a verdict: `ok` (agree), `UNCONFIRMED` (equal
except where a side refuses), `FAIL` (everything else). -/
def ProbeVerdict.status : ProbeVerdict → String
  | .agree => "ok"
  | .unconfirmed _ => "UNCONFIRMED"
  | _ => "FAIL"

/-- A one-line rendering. -/
def ProbeVerdict.render : ProbeVerdict → String
  | .agree => "agree"
  | .differ m => s!"differ (SILENT default-point fold): {m}"
  | .unconfirmed ms => s!"unconfirmed (equal except where a side refuses): {String.intercalate " | " ms}"
  | .metaDiffer ms => s!"resolved metadata at the point disagrees: {String.intercalate " | " ms}"
  | .frontendRejects n => s!"slang reports {n} error(s) elaborating the top alone at the point (the two designs compare equal)"
  | .refused m => s!"refused: {m}"

/-- What a non-passing verdict MEANS, for refusal messages: only `.differ`
is a default-point fold; the other verdicts never compared two different
values (round 3 CX repair — one generic "a fold leaked" suffix misnamed
every one of them). -/
def ProbeVerdict.meaning : ProbeVerdict → String
  | .agree =>
      "the envelope and slang's own extraction at the point instantiate to the same design there"
  | .differ _ =>
      "the envelope, elaborated by slang at the DEFAULT parameters, and slang's own extraction AT this point instantiate to different designs there: something the extractor computed at the defaults leaked into the symbolic envelope"
  | .unconfirmed _ =>
      "the two designs are equal except where one side refuses: nothing vouches for the envelope's value at those nodes"
  | .metaDiffer _ =>
      "the two designs are equal, but slang's resolved metadata at the point disagrees with the Lean elaboration there"
  | .frontendRejects _ =>
      "the two designs are equal, but slang rejects the top (alone, its own hierarchy) at this point"
  | .refused _ =>
      "one side does not instantiate at the point, or the entry was not probed: nothing was compared"

/-- **The point check of one module.** `dflt` is the envelope's module,
`pt` the same module extracted at the override point `ov`, `lib` the
envelope's module library (both sides flatten through it). -/
def PDesign.pointVerdict (dflt pt : PDesign) (lib : List PDesign)
    (ov : List (String × Int)) (frontendErrors : Nat := 0) : ProbeVerdict :=
  if dflt.params.map (·.name) != pt.params.map (·.name) then
    .differ s!"parameter list: envelope {dflt.params.map (·.name)} ≠ point {pt.params.map (·.name)}"
  else
    match dflt.instAtOverrides lib ov, pt.instAtOverrides lib ov with
    | .error e, _ => .refused s!"envelope at the point: {e}"
    | _, .error e => .refused s!"point extraction: {e}"
    | .ok a, .ok b =>
        match a.compare b with
        | .differ m => .differ m
        | .loudOnly ms => .unconfirmed ms
        | .equal =>
            if frontendErrors != 0 then .frontendRejects frontendErrors
            else
              match pt.crossCheck with
              | [] => .agree
              | msgs => .metaDiffer msgs

/-- `pointVerdict` as a `Bool`: the check passes exactly at `.agree`. -/
def PDesign.pointAgrees (dflt pt : PDesign) (lib : List PDesign)
    (ov : List (String × Int)) : Bool :=
  (dflt.pointVerdict pt lib ov).ok

/-! ## Sidecars -/

/-- One instance of the point-elaborated hierarchy: its definition, the
overrides it receives (`none`: not an integer override, or an untyped
parameter given a type other than an integer's by a sized override —
IEEE 1800-2023 §6.20.2; an int probe would check another family member),
and the
definition re-extracted alone at them (`none`: slang could not). -/
structure ProbeInst2 where
  module : String
  overrides : Option (List (String × Int))
  design : Option PDesign
deriving Repr, Inhabited

/-- One probe point: the top-level overrides, slang's error count there,
the top module extracted at the point, and the probed instances. -/
structure ProbePoint2 where
  overrides : List (String × Int)
  frontendErrors : Nat := 0
  module : PDesign
  instances : List ProbeInst2 := []
deriving Repr, Inhabited

/-- A parsed probe sidecar (`<file>.sv.probes.json`). -/
structure Probes2 where
  top : String
  sourceFiles : List (String × String)
  points : List ProbePoint2
deriving Repr, Inhabited

/-- `N=4,W=8`. -/
def renderOverrides (ov : List (String × Int)) : String :=
  if ov.isEmpty then "(defaults)" else
  String.intercalate "," (ov.map fun (n, v) => s!"{n}={v}")

/-- Every verdict of one point: the top first (label `top`), then one per
probed instance (label `<definition>#(<overrides>)`). -/
def ProbePoint2.verdicts (p : ProbePoint2) (top : PDesign) (lib : List PDesign) :
    List (String × ProbeVerdict) :=
  ("top", top.pointVerdict p.module lib p.overrides p.frontendErrors) ::
    p.instances.map fun i =>
      let label := s!"{i.module}#({(i.overrides.map renderOverrides).getD "non-integer override"})"
      match lib.find? (·.name == i.module), i.overrides, i.design with
      | none, _, _ => (label, .refused s!"'{i.module}' is not in the envelope's module library")
      | _, none, _ => (label, .refused "an override is not an integer, or gives an untyped parameter another type than an integer override would (unprobed)")
      | _, _, none => (label, .refused "slang cannot elaborate the definition alone there (unprobed)")
      | some c, some ov, some cp => (label, c.pointVerdict cp lib ov)

/-- Every verdict of a sidecar against its envelope (`top`, `lib`), labelled
`<point> <entry>`. A sidecar for another top or other sources is one
refused line. -/
def Probes2.report (pr : Probes2) (top : String) (sourceFiles : List (String × String))
    (d : PDesign) (lib : List PDesign) : List (String × ProbeVerdict) :=
  if pr.top != top then
    [("sidecar", .refused s!"probe sidecar is for top '{pr.top}', the envelope's is '{top}'")]
  else if pr.sourceFiles != sourceFiles then
    [("sidecar", .refused "probe sidecar was extracted from other sources (path/sha256 list differs from the envelope's): regenerate it with --probe-points")]
  else
    pr.points.flatMap fun p =>
      (p.verdicts d lib).map fun (l, v) => (s!"{renderOverrides p.overrides} {l}", v)

/-! ## Hand-built checks

Detection (a default-point fold is a SILENT difference at a non-default
point and agreement at the default), the normalization rules (identity
resizes vanish; a resize through arithmetic does NOT), loud absorption, and
the loud-only (`unconfirmed`) class. The extractor-level evidence is the
mutation sweep recorded in `docs/sv-charter.md` (2026-10-28, round 3 CX):
each round-1/2 fold guard, disabled, is caught at every point it changes. -/

private def wm1P : PDim := ⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1), .int 0⟩

/-- `assign y = a` over `[W-1:0]` ports, with the declared range of `y`
given by `ydim` (the symbolic range, or a FOLDED one), `W` defaulting to
`w0`. -/
private def pProbe (w0 : Int) (ydim : PDim) : PDesign :=
  { name := "probe_w"
    params := [{ name := "W", default? := some (.int w0), resolved? := some w0 }]
    localParams := [], enums := []
    decls := [
      { name := "a", type := .packed [wm1P] none, isInput := true },
      { name := "y", type := .packed [ydim] none, isOutput := true }]
    processes := [.assign "y" (.ident "a")]
    generates := [] }

-- The envelope (W = 4 default) against slang's extraction at W = 8 (its
-- default literal is the override): the same symbolic design agrees …
#guard (pProbe 4 wm1P).pointAgrees (pProbe 8 wm1P) [] [("W", 8)]
-- … and a range folded at the default (`[3:0]` where the source says
-- `[W-1:0]`) is a SILENT difference at W = 8, invisible at W = 4.
#guard match (pProbe 4 ⟨.int 3, .int 0⟩).pointVerdict (pProbe 8 wm1P) [] [("W", 8)] with
  | .differ _ => true
  | _ => false
#guard (pProbe 4 ⟨.int 3, .int 0⟩).pointAgrees (pProbe 4 wm1P) [] [("W", 4)]
-- A refusal on either side is never agreement.
#guard match (pProbe 4 wm1P).pointVerdict (pProbe 8 wm1P) [] [("Q", 8)] with
  | .refused _ => true
  | _ => false

private def d4 (ps : Array Process2) : Design2 :=
  { name := "d", decls := #[{ name := "a", width := 4 }, { name := "b", width := 4 },
      { name := "c", width := 8 }, { name := "y", width := 4 }],
    processes := ps }

private def cmpClass (a b : Array Process2) : String :=
  match (d4 a).compare (d4 b) with
  | .equal => "equal"
  | .loudOnly _ => "loudOnly"
  | .differ _ => "differ"

-- Rule 1: an identity resize vanishes (`a` is 4 bits).
#guard cmpClass #[.assign (.ident "y") (.resize 4 (.ident "a"))]
                #[.assign (.ident "y") (.ident "a")] == "equal"
-- Rules 3+5: `resize 4 (c & resize 8 a)` = `resize 4 c & a`.
#guard cmpClass #[.assign (.ident "y") (.resize 4 (.binary .and (.ident "c") (.resize 8 (.ident "a"))))]
                #[.assign (.ident "y") (.binary .and (.resize 4 (.ident "c")) (.ident "a"))] == "equal"
-- Rule 2 + 4: a literal arm is resized in place through a ternary.
#guard cmpClass #[.assign (.ident "y") (.resize 4 (.ternary (.ident "a") (.lit (.ofNat 8 0)) (.ident "c")))]
                #[.assign (.ident "y") (.ternary (.ident "a") (.lit (.ofNat 4 0)) (.resize 4 (.ident "c")))] == "equal"
-- NOT pushed through arithmetic (the x-collapse sees the high bits).
#guard cmpClass #[.assign (.ident "y") (.resize 4 (.binary .add (.ident "c") (.ident "c")))]
                #[.assign (.ident "y") (.binary .add (.resize 4 (.ident "c")) (.resize 4 (.ident "c")))] == "differ"
-- Rule 0: an expression with a loud operand is that operand.
#guard cmpClass #[.assign (.ident "y") (.binary .add (.unsupported "K" "x") (.ident "a"))]
                #[.assign (.ident "y") (.resize 4 (.unsupported "K" "other text"))] == "equal"
-- One side loud, the other a value: loud-only (`unconfirmed`), never equal.
#guard cmpClass #[.assign (.ident "y") (.ident "a")]
                #[.assign (.ident "y") (.unsupported "ConversionExpression:width" "N")] == "loudOnly"
-- Two different values: a silent difference.
#guard cmpClass #[.assign (.ident "y") (.ident "a")]
                #[.assign (.ident "y") (.ident "b")] == "differ"
-- A loud node elsewhere does not hide a value difference.
#guard cmpClass #[.assign (.ident "y") (.ident "a"), .unsupported "K" ""]
                #[.assign (.ident "y") (.ident "b"), .assign (.ident "y") (.ident "a")] == "differ"

end LeanModels.Sv
