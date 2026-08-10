import LeanModels.Python.Runtime

/-!
# Fuel-based definitional interpreter (`LeanModels.Python`)

Implements the Python semantic tier of `docs/DESIGN.md` ("Semantic
decisions", normative), re-shaped over the H1 runtime core of
`docs/memory-model.md` v2 (normative for the heap layer):

* the interpreter runs over **runtime values** (`RVal`, which may contain
  heap refs) and threads a **`FrameState`** (shared `World` + this frame's
  locals) through the `Run σ α` outcome type — state is retained on `.ok`
  AND on `.exn`;
* `callIn` is the mutual-recursion point (and the frozen recursion point of
  the proof doctrine): nested Python-to-Python calls share the caller's
  `World`;
* `callFunction` is the isolated public observation — fresh world, **thaw**
  the boundary arguments (`Val → RVal`), run `callIn`, **deep-freeze** the
  result (`RVal → Res Val`) — with its signature UNCHANGED
  (`Module → String → Array Val → Nat → Res Val`), so `CallsTo` and every
  public theorem statement are untouched.

H1-proper (the dict tier, docs/memory-model.md §dict semantics) is LIVE:
dict literals allocate on the heap (`.ref` values), subscript stores
mutate it (aliasing-visible), reads/membership/`len`/`.get`/truthiness
resolve through it, `==` walks it (`heapEq` — a frozen recursion point;
ref-free pairs take the pure `valEq` fast path), identity is decided
dynamically, and the G1 module-init pass allocates top-level dict
literals into `initWorld`'s heap. The remaining `.ref` refusals below are
the loud H1 frontier (live iteration, value-container membership,
methods beyond `.get`, `del`, `.ref` operands of value-only helpers).

The v0 discipline is unchanged:

* **Fuel discipline** (normative): every function in the mutual block takes
  `fuel : Nat` and starts `match fuel with | 0 => .timeout | fuel + 1 => …`,
  passing the *decremented* fuel to **every** recursive call (expressions
  included). Termination is structural on fuel; proofs do induction on fuel.
  Fuel is a *depth* bound, not a step count: sibling calls receive the same
  (already decremented) fuel.
* **Loud failure**: anything outside the tier yields `unsupported` with a
  message naming the construct — never a silently wrong value. Real Python
  runtime errors yield `exn` with the corresponding `PyErr`. `.timeout` is
  fuel exhaustion ONLY; `unsupported` is the fuel-INDEPENDENT frontier.
* **Provability**: the semantics is factored into small, pure, fuel-free
  helpers (`truthy`, `asInt`, `valEq`, `evalBinOp`, `evalUnaryOp`,
  `evalCompareOp`, `Env.lookup`, `Env.set`, `indexVal`, `lenVal`,
  `sortedVal`, `assignTo`, and the dict tier's heap readers) that proofs
  can `simp`-unfold — the heap-aware steps (`truthyH`, `evalCompareOpH`,
  `evalUnaryOpH`, `lenValH`, `indexValH`) delegate to the pure ones on
  non-ref values, which is what keeps the proof-layer vocabulary pure —
  plus a mutual block of the normative functions (`evalExpr`, `execStmt`,
  `execStmts`, `callIn`) and the fueled chain helpers (`evalExprs`,
  `evalBoolChain`, `evalCompareChain`, `evalDictItems`, `execWhile`,
  `execFor`). The fueled `heapEq` block is a FROZEN recursion point.

Tier-boundary decisions refining DESIGN.md (Python supports these, the
tier does not — so they are `unsupported`, never a fake `TypeError`):
sequence repetition (`"a" * 2`), `%` string formatting, `str` unpacking
(`a, b = "xy"`), nested/starred unpacking targets, `break`/`continue`
escaping a function body, negative `**` exponents (incl. `0 ** -1`),
referencing a function (or a builtin — `len`/`sorted`) as a value, calling a
non-`Name` expression, `is`/`is not` without a `None` side (identity is not
value-determined), non-literal parameter defaults, `sorted` on anything but
an all-int list (see `sortedVal`), and the `.ref` arms noted above (the loud
H1 frontier — every operation on a heap object that is not in the dict
inventory).

In tier since the F1/F2 sprint: LITERAL parameter defaults (missing trailing
arguments filled in `mkCallEnv`; arity window `arityOk`) and `is`/`is not`
against the literal `None` (`evalCompareOp`). In tier since the
call:sorted sprint: the builtin `sorted` on all-int lists (`sortedVal`,
`sortInts`).

`Env` is an abbrev for `REnv = List (String × RVal)`, so `Env.lookup` /
`Env.set` must be called by their full names (dot notation on an `Env`
value resolves into the `List` namespace). They are polymorphic in the
value type (the G1 accumulator uses them at `Val`).
-/

namespace LeanModels.Python

/-! ## Pure helpers (fuel-free; proofs `simp`-unfold these) -/

/-- Python type name of a boundary value, as used in CPython error
messages. -/
def Val.typeName : Val → String
  | .none => "NoneType"
  | .bool _ => "bool"
  | .int _ => "int"
  | .str _ => "str"
  | .list _ => "list"
  | .tuple _ => "tuple"

/-- Python type name of a runtime value. A `.ref`'s real type name lives in
the heap (H1-proper resolves it there); the `"object"` placeholder is never
part of a *decided* outcome — every helper refuses `.ref` operands loudly
BEFORE building an error message from `typeName`. A namedtuple names its
own class (`Move`), exactly as CPython error messages do. -/
def RVal.typeName : RVal → String
  | .none => "NoneType"
  | .bool _ => "bool"
  | .int _ => "int"
  | .str _ => "str"
  | .listV _ => "list"
  | .tuple _ => "tuple"
  | .ntuple tn _ _ => tn
  | .ref _ => "object"

/-- Is this runtime value one of the value-sequence types
(`str`/`listV`/`tuple`/namedtuple)? Namedtuples ARE tuples in CPython
(sequence protocol included), so they answer `true` — which routes
repetition to the loud sequence-repetition arm, never a fake `TypeError`. -/
def RVal.isSeq : RVal → Bool
  | .str _ | .listV _ | .tuple _ => true
  | .ntuple _ _ _ => true
  | _ => false

/-- Is this runtime value Python's `None` singleton? (The value-level test
behind `is None` / `is not None` — see `evalCompareOp`.) A heap object is
never `None`, so the `.ref` arm is a faithful `false`, not a refusal. -/
def RVal.isNone : RVal → Bool
  | .none => true
  | _ => false

/-- Python surface syntax of a binary operator (error messages). -/
def BinOp.symbol : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mult => "*"
  | .floorDiv => "//"
  | .mod => "%"
  | .pow => "**"

/-- Python surface syntax of a comparison operator (error messages). -/
def CmpOp.symbol : CmpOp → String
  | .eq => "=="
  | .notEq => "!="
  | .lt => "<"
  | .ltE => "<="
  | .gt => ">"
  | .gtE => ">="
  | .is => "is"
  | .isNot => "is not"
  | .inOp => "in"
  | .notIn => "not in"

/-- Schema `kind` name of an expression node (error messages). For
`unsupported` nodes this is the recorded CPython class name. -/
def Expr.kindName : Expr → String
  | .constant .. => "Constant"
  | .name .. => "Name"
  | .binOp .. => "BinOp"
  | .unaryOp .. => "UnaryOp"
  | .boolOp .. => "BoolOp"
  | .compare .. => "Compare"
  | .call .. => "Call"
  | .list .. => "List"
  | .tuple .. => "Tuple"
  | .subscript .. => "Subscript"
  | .dict .. => "Dict"
  | .attribute .. => "Attribute"
  | .ifExp .. => "IfExp"
  | .slice .. => "Slice"
  | .genExp .. => "GeneratorExp"
  | .unsupported pyKind _ _ => pyKind

/-- Schema `kind` name of a statement node (error messages) — the
`Expr.kindName` counterpart. -/
def Stmt.kindName : Stmt → String
  | .ret .. => "Return"
  | .assign .. => "Assign"
  | .augAssign .. => "AugAssign"
  | .whileLoop .. => "While"
  | .forStmt .. => "For"
  | .ifStmt .. => "If"
  | .exprStmt .. => "Expr"
  | .yieldStmt .. => "Yield"
  | .defStmt .. => "NestedDef"
  | .pass _ => "Pass"
  | .brk _ => "Break"
  | .cont _ => "Continue"
  | .unsupported pyKind _ _ => pyKind

/-- Python truthiness `bool(x)`: `None` → false; `bool` → itself;
`int` → `≠ 0`; `str`/`listV`/`tuple` → nonempty. `Res`-valued since H1:
a `.ref`'s truthiness lives in the heap (`bool(d)` is `len(d) != 0`) —
loud until the dict tier reads it there. -/
def truthy : RVal → Res Bool
  | .none => .ok false
  | .bool b => .ok b
  | .int n => .ok (n != 0)
  | .str s => .ok (!s.isEmpty)
  | .listV xs => .ok (xs.size != 0)
  | .tuple xs => .ok (xs.size != 0)
  | .ntuple _ _ xs => .ok (xs.size != 0)
  | .ref _ => .unsupported
      "truthiness of a heap object lives in the heap (`truthyH` decides it; this pure helper is the proof-layer vocabulary)"

/-- bool→int coercion (Python's `bool` is an `int` subtype): `int` passes
through, `True`/`False` become `1`/`0`, everything else is `none`. -/
def asInt : RVal → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => Option.none

mutual
  /-- Python `==` on runtime values. Numeric (`int`/`bool`) compare by
  value after bool→int coercion (`True == 1`); `str` by string equality;
  `listV`/`tuple` elementwise (recursively, so `[True] == [1]`);
  `None == None`; any cross-type combination (after coercion) is `False`.
  `Res`-valued since H1: `==` on a `.ref` is the heap-walking dict equality
  (identity shortcut, size check, left-order traversal, active-pair cycle
  detection — docs/memory-model.md) — loud until the dict tier implements
  it. On ref-free values it never fails. -/
  def valEq : RVal → RVal → Res Bool
    | .none, .none => .ok true
    | .bool a, .bool b => .ok (a == b)
    | .bool a, .int m => .ok ((if a then (1 : Int) else 0) == m)
    | .int n, .bool b => .ok (n == (if b then (1 : Int) else 0))
    | .int n, .int m => .ok (n == m)
    | .str s, .str t => .ok (s == t)
    | .listV xs, .listV ys => valEqList xs.toList ys.toList
    | .tuple xs, .tuple ys => valEqList xs.toList ys.toList
    -- namedtuples compare as plain tuples (CPython: tuple.__eq__ — the
    -- class is IGNORED, even across two different namedtuple classes)
    | .ntuple _ _ xs, .ntuple _ _ ys => valEqList xs.toList ys.toList
    | .ntuple _ _ xs, .tuple ys => valEqList xs.toList ys.toList
    | .tuple xs, .ntuple _ _ ys => valEqList xs.toList ys.toList
    | .ref _, _ => .unsupported
        "'==' on a heap object lives in the heap (`heapEq` decides it; this pure helper is the proof-layer vocabulary)"
    | _, .ref _ => .unsupported
        "'==' on a heap object lives in the heap (`heapEq` decides it; this pure helper is the proof-layer vocabulary)"
    | _, _ => .ok false

  /-- Elementwise `valEq`, short-circuiting on the first mismatch;
  `false` on length mismatch. -/
  def valEqList : List RVal → List RVal → Res Bool
    | [], [] => .ok true
    | a :: as, b :: bs => do
        let e ← valEq a b
        if e then valEqList as bs else return false
    | _, _ => .ok false
end

/-- Ordering comparison on `Int` (only called with `.lt/.ltE/.gt/.gtE`;
the equality and identity cases are handled by `valEq`/`RVal.isNone` in
`evalCompareOp` and never reach here, but are given a by-value meaning
(`is` on identical-valued ints would be `True` under CPython's small-int
cache; the arms exist for totality only). -/
def intCmp : CmpOp → Int → Int → Bool
  | .eq, x, y => x == y
  | .notEq, x, y => x != y
  | .lt, x, y => x < y
  | .ltE, x, y => x ≤ y
  | .gt, x, y => y < x
  | .gtE, x, y => y ≤ x
  | .is, x, y => x == y
  | .isNot, x, y => x != y
  | .inOp, _, _ => false   -- unreachable: membership never reaches intCmp
  | .notIn, _, _ => false  -- (evalCompareOp handles it first; totality arm)

/-- Ordering comparison on `String` (lexicographic by Unicode code points,
which is Lean's `String` `<`). See `intCmp` for the equality/identity cases. -/
def strCmp : CmpOp → String → String → Bool
  | .eq, s, t => s == t
  | .notEq, s, t => s != t
  | .lt, s, t => s < t
  | .ltE, s, t => s < t || s == t
  | .gt, s, t => t < s
  | .gtE, s, t => t < s || s == t
  | .is, s, t => s == t
  | .isNot, s, t => s != t
  | .inOp, _, _ => false   -- unreachable: membership never reaches strCmp
  | .notIn, _, _ => false  -- (evalCompareOp handles it first; totality arm)

mutual
  /-- CPython strict `<` on immediate values (H6 draining consumers,
  docs/memory-model.md §draining consumers): int/bool numeric, str
  code-point lexicographic, tuple/namedtuple/value-list lexicographic and
  CLASS-ERASED (`valEq` walks elementwise ties, `rvalLt` decides the
  first difference; exhaustion → the shorter is smaller — CPython's
  `tuple.__lt__`). Refs and mixed value kinds refuse LOUDLY, mirroring
  `evalCompareOp`'s ordering arm — never a guessed `TypeError`. This is
  THE ordering relation: the `<` operator and `sorted`/`max`/`min` all
  decide through it. A worker of the `sortInts` freeze family — OUT of
  the simp sets. -/
  def rvalLt : RVal → RVal → Res Bool
    | .bool a, .bool b => .ok ((if a then (1 : Int) else 0) < (if b then (1 : Int) else 0))
    | .bool a, .int m => .ok ((if a then (1 : Int) else 0) < m)
    | .int n, .bool b => .ok (n < (if b then (1 : Int) else 0))
    | .int n, .int m => .ok (n < m)
    | .str s, .str t => .ok (strCmp .lt s t)
    | .tuple xs, .tuple ys => rvalLtList xs.toList ys.toList
    | .tuple xs, .ntuple _ _ ys => rvalLtList xs.toList ys.toList
    | .ntuple _ _ xs, .tuple ys => rvalLtList xs.toList ys.toList
    | .ntuple _ _ xs, .ntuple _ _ ys => rvalLtList xs.toList ys.toList
    | .listV xs, .listV ys => rvalLtList xs.toList ys.toList
    | .ref _, b =>
        .unsupported s!"ordering comparison '<' on a heap object is outside the tier ({b.typeName} rhs; docs/memory-model.md)"
    | a, .ref _ =>
        .unsupported s!"ordering comparison '<' on a heap object is outside the tier ({a.typeName} lhs; docs/memory-model.md)"
    | a, b =>
        .unsupported s!"comparison '<' between '{a.typeName}' and '{b.typeName}' is outside the tier"

  /-- Elementwise lexicographic `<`: `valEq` walks the common prefix,
  `rvalLt` decides the first difference, length breaks ties. -/
  def rvalLtList : List RVal → List RVal → Res Bool
    | [], [] => .ok false
    | [], _ :: _ => .ok true
    | _ :: _, [] => .ok false
    | a :: as, b :: bs => do
        let e ← valEq a b
        if e then rvalLtList as bs else rvalLt a b
end

/-- The four ordering operators derived from strict `<` — exact within
the tier: on comparable pairs the order is total, so `a <= b` is
`¬(b < a)`; incomparable pairs refuse inside `rvalLt` before the
negation can lie. -/
def ordFromLt (op : CmpOp) (a b : RVal) : Res Bool :=
  match op with
  | .lt => rvalLt a b
  | .gt => rvalLt b a
  | .ltE => do let g ← rvalLt b a; return !g
  | .gtE => do let l ← rvalLt a b; return !l
  | _ => .unsupported "ordFromLt: non-ordering operator (report this)"

/-- One comparison step. `==`/`!=` are `valEq` (`Res`-valued since H1 — see
there). `is`/`is not` (F2): the extractor admits these ONLY when one side of
the link is the literal `None`, whose runtime value is always `RVal.none` —
so identity here is against the `None` singleton and IS value-determined:
`x is None ⟺ x = RVal.none` (a heap `.ref` is faithfully not `None`). When
at least one operand is `.none` the result is `a.isNone && b.isNone`; if
NEITHER side is `.none` — unreachable through the extractor, but reachable
by hand-built ASTs — identity between two non-None values is
CPython-implementation-defined (small-int caching, str interning) and
refused loudly (H1-proper adds the faithful two-ref address equality).
Ordering: int/bool by value (bool→int coercion), str lexicographic;
ordering any other type combination is outside the tier. -/
def evalCompareOp (op : CmpOp) (a b : RVal) : Res Bool :=
  match op with
  | .eq => valEq a b
  | .notEq => do let e ← valEq a b; return !e
  | .is =>
    if a.isNone || b.isNone then .ok (a.isNone && b.isNone)
    else
      .unsupported
        s!"'is' between '{a.typeName}' and '{b.typeName}' (identity is not value-determined) is outside the v0 tier"
  | .isNot =>
    if a.isNone || b.isNone then .ok (!(a.isNone && b.isNone))
    else
      .unsupported
        s!"'is not' between '{a.typeName}' and '{b.typeName}' (identity is not value-determined) is outside the v0 tier"
  | .inOp =>
      .unsupported
        s!"'in' on '{b.typeName}' is outside this tier (dict membership lands with H1-proper, docs/memory-model.md)"
  | .notIn =>
      .unsupported
        s!"'not in' on '{b.typeName}' is outside this tier (dict membership lands with H1-proper, docs/memory-model.md)"
  | op =>
    match asInt a, asInt b with
    | some x, some y => .ok (intCmp op x y)
    | _, _ =>
      match a, b with
      | .str s, .str t => .ok (strCmp op s t)
      -- H6: tuple/namedtuple ordering, class-erased and lexicographic —
      -- ONE relation with `sorted` (`rvalLt`, via `ordFromLt`)
      | .tuple _, .tuple _ => ordFromLt op a b
      | .tuple _, .ntuple _ _ _ => ordFromLt op a b
      | .ntuple _ _ _, .tuple _ => ordFromLt op a b
      | .ntuple _ _ _, .ntuple _ _ _ => ordFromLt op a b
      | .ref _, b =>
        .unsupported
          s!"ordering comparison '{op.symbol}' on a heap object is outside the H1 tier ({b.typeName} rhs; docs/memory-model.md)"
      | a, .ref _ =>
        .unsupported
          s!"ordering comparison '{op.symbol}' on a heap object is outside the H1 tier ({a.typeName} lhs; docs/memory-model.md)"
      | a, b =>
        .unsupported
          s!"comparison '{op.symbol}' between '{a.typeName}' and '{b.typeName}' is outside the v0 tier"

/-- Binary operator on already-evaluated operands. int/bool operands are
coerced to `Int`; arithmetic results are always `int`, never `bool`.
`//`/`%` floor (`Int.fdiv`/`Int.fmod`); divisor 0 → `ZeroDivisionError`.
`**` requires a nonnegative exponent (float result otherwise → unsupported).
`+` concatenates matching sequence types. Python-valid combinations outside
the tier (sequence repetition, `%` formatting) → unsupported; Python-invalid
combinations → `TypeError`. A `.ref` operand is refused loudly BEFORE the
`TypeError` fallback (its type name lives in the heap). -/
def evalBinOp (op : BinOp) (a b : RVal) : Res RVal :=
  match asInt a, asInt b with
  | some x, some y =>
    match op with
    | .add => .ok (.int (x + y))
    | .sub => .ok (.int (x - y))
    | .mult => .ok (.int (x * y))
    | .floorDiv =>
        if y = 0 then .exn .zeroDivisionError else .ok (.int (Int.fdiv x y))
    | .mod =>
        if y = 0 then .exn .zeroDivisionError else .ok (.int (Int.fmod x y))
    | .pow =>
        if y < 0 then
          -- CPython: 0 ** -1 raises (no float involved); other negative
          -- exponents produce floats, which are outside the v0 tier.
          if x = 0 then .exn .zeroDivisionError
          else .unsupported "'**' with a negative exponent (float result) is outside the v0 tier"
        else .ok (.int (x ^ y.toNat))
  | _, _ =>
    match op, a, b with
    | .add, .str s, .str t => .ok (.str (s ++ t))
    | .add, .listV xs, .listV ys => .ok (.listV (xs ++ ys))
    | .add, .tuple xs, .tuple ys => .ok (.tuple (xs ++ ys))
    -- namedtuple `+` concatenates as tuples and yields a PLAIN tuple
    -- (CPython: tuple.__add__ — the class does not survive concatenation)
    | .add, .ntuple _ _ xs, .tuple ys => .ok (.tuple (xs ++ ys))
    | .add, .tuple xs, .ntuple _ _ ys => .ok (.tuple (xs ++ ys))
    | .add, .ntuple _ _ xs, .ntuple _ _ ys => .ok (.tuple (xs ++ ys))
    | op, .ref _, _ =>
        .unsupported
          s!"binary '{op.symbol}' on a heap object is outside the H1 tier (dict operators beyond the inventory; docs/memory-model.md)"
    | op, _, .ref _ =>
        .unsupported
          s!"binary '{op.symbol}' on a heap object is outside the H1 tier (dict operators beyond the inventory; docs/memory-model.md)"
    | .mult, a, b =>
        if (a.isSeq && (asInt b).isSome) || ((asInt a).isSome && b.isSeq) then
          .unsupported
            s!"sequence repetition ('{a.typeName}' * '{b.typeName}') is outside the v0 tier"
        else
          .exn (.typeError s!"unsupported operand type(s) for *: '{a.typeName}' and '{b.typeName}'")
    | .mod, .str _, _ =>
        .unsupported "'%' string formatting is outside the v0 tier"
    | op, a, b =>
        .exn (.typeError
          s!"unsupported operand type(s) for {op.symbol}: '{a.typeName}' and '{b.typeName}'")

/-- Unary operator: `not` is truthiness negation (`Res`-valued through
`truthy` since H1); unary `-` needs an int/bool operand (`-True == -1`);
a `.ref` operand is refused loudly (its `__neg__` lives in the heap). -/
def evalUnaryOp (op : UnaryOp) (v : RVal) : Res RVal :=
  match op with
  | .not => do let b ← truthy v; return .bool (!b)
  | .usub =>
    match v with
    | .ref _ =>
        .unsupported "unary '-' on a heap object is outside the H1 tier (docs/memory-model.md)"
    | v =>
      match asInt v with
      | some n => .ok (.int (-n))
      | Option.none => .exn (.typeError s!"bad operand type for unary -: '{v.typeName}'")

/-- First match wins (shadowing is by position in the list). Polymorphic in
the value type: runtime envs bind `RVal`, the G1 accumulator binds `Val`. -/
def Env.lookup : List (String × α) → String → Option α
  | [], _ => Option.none
  | (k, v) :: rest, name => if k == name then some v else Env.lookup rest name

/-- Replace an existing binding in place, else append at the end. -/
def Env.set : List (String × α) → String → α → List (String × α)
  | [], name, v => [(name, v)]
  | (k, w) :: rest, name, v =>
    if k == name then (name, v) :: rest else (k, w) :: Env.set rest name v

/-- Constant literal → boundary value (G1 freeze side). -/
def Const.toVal : Const → Val
  | .none => .none
  | .bool b => .bool b
  | .int n => .int n
  | .str s => .str s

/-- Constant literal → runtime value (constants are scalars — no
allocation). -/
def Const.toRVal : Const → RVal
  | .none => .none
  | .bool b => .bool b
  | .int n => .int n
  | .str s => .str s

/-- `len(v)` for `str`/`listV`/`tuple` (str counts code points), else
`TypeError`; `len` of a `.ref` is a heap read (dicts) — loud until
H1-proper. -/
def lenVal : RVal → Res RVal
  | .str s => .ok (.int s.length)
  | .listV xs => .ok (.int xs.size)
  | .tuple xs => .ok (.int xs.size)
  | .ntuple _ _ xs => .ok (.int xs.size)
  | .ref _ =>
      .unsupported "len() of a heap object lives in the heap (`heapLen` via `lenValH` decides it)"
  | v => .exn (.typeError s!"object of type '{v.typeName}' has no len()")

/-- Insert `x` into an (ascending) list — the step function of `sortInts`.
Structural recursion on purpose: the kernel reduces it, which `#py_check` /
`py_check` / `py_vcgen`'s captured runs need. (Core's `List.mergeSort` is
well-founded recursion and does NOT kernel-reduce — verified on this
toolchain; `by rfl` on a concrete `mergeSort` run fails.) -/
def insertLe (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertLe x ys

/-- Ascending insertion sort on `Int` — the value-level meaning of the
builtin `sorted` (tier: all-int lists only, see `sortedVal`). Stability
is vacuous at this type: `.int`s have no identity, so equal elements are
interchangeable. The proof layer bridges to Mathlib's `List.insertionSort`
(`sortInts_eq` in `Examples/python/bench_statistics/proof.lean`) to harvest
`Pairwise`/`Perm` lemmas; only the Mathlib-free `sortInts_length` lives
in-tree (Logic.lean), because symbolic execution needs it. -/
def sortInts : List Int → List Int
  | [] => []
  | x :: xs => insertLe x (sortInts xs)

/-- The elements a `for` loop sees when iterating a str: one 1-character
str per CODE POINT, in order. CPython's `str_iterator` is an index cursor
over an IMMUTABLE object, so this snapshot IS the live semantics — no
mutation, growth, or shrinkage is expressible (unlike `execForList`'s
live list cursor, which is why that one re-reads the heap per step).
A frozen VALUE worker like `strSlice`. -/
def strCharVals (s : String) : List RVal :=
  s.toList.map (fun c => .str (String.ofList [c]))

/-- Stable insertion under `rvalLt` (H6 general-order `sorted`):
ascending sinks `x` below every strictly-smaller prefix element
(insert-before iff `¬(y < x)` — equals keep first-encountered order);
descending mirrors (insert-before iff `¬(x < y)`). Structural recursion
(kernel-reducible, the `insertLe` discipline). -/
def insertByLt (desc : Bool) (x : RVal) : List RVal → Res (List RVal)
  | [] => .ok [x]
  | y :: ys => do
    let after ← if desc then rvalLt x y else rvalLt y x
    if after then do return y :: (← insertByLt desc x ys)
    else .ok (x :: y :: ys)

/-- Insertion sort by `rvalLt`, STABLE in both directions. `reverse=True`
is descending stable insertion, NOT sort-then-reverse:
`sorted([1, True], reverse=True)` must keep `[1, True]` — a reversal
would forge `[True, 1]` (docs/memory-model.md §draining consumers).
Within the tier every total order agrees with CPython's timsort, and a
comparison refusal is the whole sort's loud refusal. -/
def sortByLt (desc : Bool) : List RVal → Res (List RVal)
  | [] => .ok []
  | x :: xs => do insertByLt desc x (← sortByLt desc xs)

/-- All-int extraction: `some ns` iff every element is `.int`. `.bool`s
deliberately do NOT coerce here — CPython sorts `[True, 0, 2]` keeping the
`True` object in the result, which the identity-free `.int` cannot
reproduce faithfully; such lists take `sortedVal`'s general `rvalLt`
path (which keeps the values themselves). -/
def asIntList : List RVal → Option (List Int)
  | [] => some []
  | .int n :: vs => (asIntList vs).map (n :: ·)
  | _ => Option.none

/-- `sorted(v)`: a NEW sorted value-list (H6 general-order tier).
Honesty discipline (same as `lenVal`): fake exceptions never, `unsupported`
for anything CPython would handle differently.
* `.listV` of `.int`s, ascending → the ORIGINAL `sortInts` computation
  (kept byte-for-byte: the proof layer's `sortInts_eq` bridge and every
  captured run depend on that term); every other element mix, and
  `desc = true`, take the general stable `rvalLt` path (`sortByLt`) —
  strs, tuples of `(value, move)` pairs, bools kept AS bools.
* `.str` → its code points, sorted (CPython: a list of 1-char strs);
  `.tuple`/`.ntuple` → their elements (class-erased).
* `.int`/`.bool`/`.none` → `TypeError` with CPython 3.9's exact class and
  message shape (`'int' object is not iterable`).
* A `.ref` argument decides in `sortedValH` (heap lists sort, dicts stay
  loud, GENERATORS drain in the dispatch arm — never here).
* `key=` never reaches here (loud in the H6 keyword tier — it gates on
  first-class callable values); `reverse=` arrives as `desc`. -/
def sortedVal (v : RVal) (desc : Bool := false) : Res RVal :=
  match v with
  | .listV xs =>
    if desc then do return .listV (← sortByLt true xs.toList).toArray
    else
      match asIntList xs.toList with
      | some ns => .ok (.listV (((sortInts ns).map RVal.int).toArray))
      | Option.none => do return .listV (← sortByLt false xs.toList).toArray
  | .str s => do return .listV (← sortByLt desc (strCharVals s)).toArray
  | .tuple xs => do return .listV (← sortByLt desc xs.toList).toArray
  | .ntuple _ _ xs => do return .listV (← sortByLt desc xs.toList).toArray
  | .ref _ =>
      .unsupported "sorted() on a heap object is outside the H1 tier (docs/memory-model.md)"
  | v => .exn (.typeError s!"'{v.typeName}' object is not iterable")

/-- Left fold of `max`/`min` over ints (structural — kernel-reducible). -/
def foldExtremum (isMax : Bool) (acc : Int) : List Int → Int
  | [] => acc
  | n :: rest => foldExtremum isMax (if isMax then max acc n else min acc n) rest

/-- Left fold of `max`/`min` under `rvalLt` (H6 general-order tier):
CPython keeps the FIRST maximal/minimal element (replacement only on a
STRICT win), so ties preserve the earliest value — observable when bools
and ints mix (`max(True, 1)` is `True`). -/
def foldExtremumLt (isMax : Bool) (acc : RVal) : List RVal → Res RVal
  | [] => .ok acc
  | v :: rest => do
    let repl ← if isMax then rvalLt acc v else rvalLt v acc
    foldExtremumLt isMax (if repl then v else acc) rest

/-- General-path extremum over a nonempty element snapshot (`rvalLt`;
empty → the faithful `ValueError`). -/
def extremumOf (isMax : Bool) (name : String) : List RVal → Res RVal
  | [] => .exn (.valueError s!"{name}() arg is an empty sequence")
  | v :: rest => foldExtremumLt isMax v rest

/-- The `max`/`min` builtins (H6 general-order tier): ≥ 2 arguments, or
one nonempty sequence. All-int inputs keep the ORIGINAL `foldExtremum`
computation (proof-layer captured runs depend on the term); every other
in-tier element mix folds through `rvalLt` (`extremumOf`) — strs by code
point, tuples/namedtuples lexicographic, first-win ties. `key=`/
`default=` stay loud (H6 keyword tier). Python-invalid argument shapes
raise the faithful CPython error class; a `.ref` argument decides in
`extremumValH` (heap lists fold, dicts loud, generators drain in the
dispatch arm). -/
def extremumVal (isMax : Bool) (vs : List RVal) : Res RVal :=
  let name := if isMax then "max" else "min"
  match vs with
  | [] => .exn (.typeError s!"{name} expected at least 1 argument, got 0")
  | [v] =>
    match v with
    | .listV xs =>
      match asIntList xs.toList with
      | some (n :: rest) => .ok (.int (foldExtremum isMax n rest))
      | some [] => .exn (.valueError s!"{name}() arg is an empty sequence")
      | Option.none => extremumOf isMax name xs.toList
    | .tuple xs =>
      match asIntList xs.toList with
      | some (n :: rest) => .ok (.int (foldExtremum isMax n rest))
      | some [] => .exn (.valueError s!"{name}() arg is an empty sequence")
      | Option.none => extremumOf isMax name xs.toList
    | .ntuple _ _ xs =>
      -- namedtuples iterate as tuples (CPython: `max(Entry(1,2))` is 2)
      match asIntList xs.toList with
      | some (n :: rest) => .ok (.int (foldExtremum isMax n rest))
      | some [] => .exn (.valueError s!"{name}() arg is an empty sequence")
      | Option.none => extremumOf isMax name xs.toList
    | .str t => extremumOf isMax name (strCharVals t)
    | .ref _ =>
        .unsupported s!"{name}() over a heap object is outside the H1 tier (docs/memory-model.md)"
    | v => .exn (.typeError s!"'{v.typeName}' object is not iterable")
  | vs =>
    match asIntList vs with
    | some (n :: rest) => .ok (.int (foldExtremum isMax n rest))
    | _ => extremumOf isMax name vs

/-- The `abs` builtin (B1): int/bool argument; a `.ref` is refused loudly
before the `TypeError` fallback. -/
def absVal : RVal → Res RVal
  | .int n => .ok (.int (if n < 0 then -n else n))
  | .bool b => .ok (.int (if b then 1 else 0))
  | .ref _ =>
      .unsupported "abs() of a heap object is outside the H1 tier (docs/memory-model.md)"
  | v => .exn (.typeError s!"bad operand type for abs(): '{v.typeName}'")

/-- The `int` constructor builtin (B1): identity on ints, bool coercion.
`int(str)` (parsing) and floats are out of tier; a `.ref` is refused loudly
before the `TypeError` fallback. -/
def intCastVal : RVal → Res RVal
  | .int n => .ok (.int n)
  | .bool b => .ok (.int (if b then 1 else 0))
  | .str _ => .unsupported "int() of a str is outside the v0 tier"
  | .ref _ =>
      .unsupported "int() of a heap object is outside the H1 tier (docs/memory-model.md)"
  | v => .exn (.typeError s!"int() argument must be a string, a bytes-like object or a real number, not '{v.typeName}'")

/-- The `ord` builtin: the CODE POINT of a one-character str. CPython
measures the length in code points and names the found length in its
message; a non-str argument is the faithful `TypeError` (a `.ref` is
refused loudly first, the `absVal`/`intCastVal` house shape — the
message would have to name the referent's type). -/
def ordVal : RVal → Res RVal
  | .str s =>
    match s.toList with
    | [c] => .ok (.int c.toNat)
    | cs => .exn (.typeError s!"ord() expected a character, but string of length {cs.length} found")
  | .ref _ =>
      .unsupported "ord() of a heap object is outside the tier (docs/memory-model.md §string semantics)"
  | v => .exn (.typeError s!"ord() expected string of length 1, but {v.typeName} found")

/-- The `chr` builtin: the one-character str of a code point (`bool`
coerces — Python's `bool` is an `int`). Out of `range(0x110000)` is the
faithful `ValueError`. SURROGATES (`0xD800…0xDFFF`) are refused LOUDLY:
CPython's `chr` builds a lone-surrogate str, which Lean's `Char` (and
hence every string in this model) cannot represent — a silent
substitution would be wrong. -/
def chrVal : RVal → Res RVal
  | .ref _ =>
      .unsupported "chr() of a heap object is outside the tier (docs/memory-model.md §string semantics)"
  | v =>
    match asInt v with
    | some n =>
      if n < 0 || 0x10FFFF < n then .exn (.valueError "chr() arg not in range(0x110000)")
      else if 0xD800 ≤ n && n ≤ 0xDFFF then
        .unsupported
          "chr() of a surrogate code point is outside the tier (Lean's Char excludes surrogates; docs/memory-model.md §string semantics)"
      else .ok (.str (String.ofList [Char.ofNat n.toNat]))
    | Option.none =>
      .exn (.typeError s!"an integer is required (got type {v.typeName})")

/-- Builtin names the interpreter implements (resolution: shadowable by
locals, module globals, and module `def`s, exactly like CPython builtins). -/
def isBuiltinName (id : String) : Bool :=
  id == "len" || id == "sorted" || id == "max" || id == "min" ||
  id == "abs" || id == "int" || id == "print" ||
  id == "ord" || id == "chr" || id == "next" ||
  id == "enumerate" || id == "count" ||
  id == "any" || id == "all"

/-- Names the IMPORT MACHINERY binds in every module's globals, without
any statement doing it. They are absent from the G1 table but present in
CPython, so a miss on one is `unsupported`, NEVER a `NameError` — the G1
`analysable` flag reasons about statements and cannot see them. -/
def isModuleDunder (id : String) : Bool :=
  id == "__name__" || id == "__doc__" || id == "__file__" ||
  id == "__package__" || id == "__loader__" || id == "__spec__" ||
  id == "__builtins__" || id == "__debug__"

/-- Normalize a Python index into `[0, len)`: negative indices count from the
end (`len + i`). `none` = out of range. -/
def normIndex (i : Int) (len : Nat) : Option Nat :=
  let j := if i < 0 then i + (len : Int) else i
  if 0 ≤ j ∧ j < (len : Int) then some j.toNat else Option.none

/-- `container[index]` for `listV`/`tuple`/`str` (str yields a 1-char str).
Index must be int/bool (bool coerces: `"ab"[True] == "b"`), else `TypeError`;
out of range → `IndexError`; non-subscriptable container → `TypeError`.
A `.ref` on either side is loud: a `.ref` container is a dict read (in tier
at H1-proper, with `KeyError` faithful); a `.ref` index would name its type
from the heap in the `TypeError` message. -/
def indexVal (container index : RVal) : Res RVal :=
  match container, index with
  | _, .ref _ =>
      .unsupported "a heap object as a subscript index is outside this pure helper (`indexValH` decides it faithfully)"
  | .ref _, _ =>
      .unsupported "subscripting a heap object is outside this pure helper (`heapIndex` via `indexValH` decides it)"
  | .listV xs, index =>
    match asInt index with
    | some i =>
      match normIndex i xs.size with
      | some n => .ok (xs.getD n .none)
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"list indices must be integers, not {index.typeName}")
  | .tuple xs, index =>
    match asInt index with
    | some i =>
      match normIndex i xs.size with
      | some n => .ok (xs.getD n .none)
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"tuple indices must be integers, not {index.typeName}")
  | .ntuple _ _ xs, index =>
    -- namedtuple subscripting IS tuple subscripting (tuple.__getitem__ —
    -- the error message names 'tuple', exactly as CPython's does)
    match asInt index with
    | some i =>
      match normIndex i xs.size with
      | some n => .ok (xs.getD n .none)
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"tuple indices must be integers, not {index.typeName}")
  | .str s, index =>
    match asInt index with
    | some i =>
      match normIndex i s.length with
      | some n => .ok (.str (String.singleton (s.toList.getD n ' ')))
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"string indices must be integers, not {index.typeName}")
  | v, _ => .exn (.typeError s!"'{v.typeName}' object is not subscriptable")

/-! ## The string tier (H5 strings, docs/memory-model.md §string semantics)

Pure, fuel-free helpers: strings are immutable values, so the whole tier
has VALUE semantics — no heap, no aliasing, `worldInv`-trivial. The
case-mapping methods (`swapcase`/`isupper`) are in tier for ASCII
strings only: Lean core's `Char.isUpper`/`toLower`/… are exactly the
ASCII maps, which agree with CPython there; a non-ASCII string is
refused loudly (CPython consults the full Unicode tables — guessing
would be silently wrong). `index` and slicing are code-point-exact for
every string.

Simp-set doctrine (the `sortInts`/`heapEq` freeze family): the DISPATCH
layers (`sliceVal`, `strCallPlan`) are in `py_simp`/`interpUnfolds`, the
VALUE workers (`strSlice`, `strSwapcase`, `strIsUpper`, `strIndex` and
their helpers) are deliberately OUT — symbolic goals keep the compact
`strSlice s l u st` handle, and concrete proofs rewrite through one
kernel-checked `have … := by rfl` fact per worker application instead of
thousands of character-level simp steps (concrete runs — `#py_check`,
the differential harness — reduce through the kernel/evaluator and never
consult simp sets). -/

/-- ASCII-only guard for the case-mapping methods. -/
def strAscii (s : String) : Bool :=
  s.toList.all (fun c => c.toNat < 128)

/-- `swapcase` on one ASCII char: `a-z` ↔ `A-Z`, everything else fixed
(Lean core's `Char.toUpper`/`toLower` are the ASCII maps). -/
def swapChar (c : Char) : Char :=
  if c.isUpper then c.toLower else if c.isLower then c.toUpper else c

/-- `s.swapcase()` (ASCII in tier — the section comment). -/
def strSwapcase (s : String) : Res RVal :=
  if strAscii s then .ok (.str (String.ofList (s.toList.map swapChar)))
  else .unsupported
    "swapcase() on a non-ASCII string is outside the tier (Unicode case tables; docs/memory-model.md §string semantics)"

/-- `s.isupper()`: at least one cased character and no lowercase one
(CPython's definition; ASCII cased = alphabetic). -/
def strIsUpper (s : String) : Res RVal :=
  if strAscii s then
    .ok (.bool (s.toList.any (fun c => c.isAlpha) &&
                s.toList.all (fun c => !c.isAlpha || c.isUpper)))
  else .unsupported
    "isupper() on a non-ASCII string is outside the tier (Unicode case tables; docs/memory-model.md §string semantics)"

/-- `s.islower()` (ASCII in tier, `strIsUpper`'s mirror — H6: sunfish's
`value()` capture check `q.islower()`). -/
def strIsLower (s : String) : Res RVal :=
  if strAscii s then
    .ok (.bool (s.toList.any (fun c => c.isAlpha) &&
                s.toList.all (fun c => !c.isAlpha || c.isLower)))
  else .unsupported
    "islower() on a non-ASCII string is outside the tier (Unicode case tables; docs/memory-model.md §string semantics)"

/-- `s.upper()` (ASCII in tier — H6: sunfish's `value()` capture lookup
`pst[q.upper()]`; Lean core's `Char.toUpper` is the ASCII map). -/
def strUpper (s : String) : Res RVal :=
  if strAscii s then
    .ok (.str (String.ofList (s.toList.map Char.toUpper)))
  else .unsupported
    "upper() on a non-ASCII string is outside the tier (Unicode case tables; docs/memory-model.md §string semantics)"

/-- First index where `needle` occurs in `hay` (code-point equality;
`"".index("")` is 0, as in CPython). Structural (kernel-reducible). -/
def strFindAux (hay needle : List Char) : Option Nat :=
  if needle.isPrefixOf hay then some 0
  else
    match hay with
    | [] => Option.none
    | _ :: rest => (strFindAux rest needle).map (· + 1)

/-- `s.index(sub)`: the lowest index where `sub` occurs, else the
faithful `ValueError` (`start`/`end` arguments are out of tier —
refused at dispatch). -/
def strIndex (s sub : String) : Res RVal :=
  match strFindAux s.toList sub.toList with
  | some i => .ok (.int i)
  | Option.none => .exn (.valueError "substring not found")

/-- `sub in s` on strings: SUBSTRING containment (never element
membership — CPython's `str.__contains__`), code-point-exact, with
`"" in s` true for every `s` (`strFindAux` returns 0 there). One of the
frozen VALUE workers (the section comment): concrete proofs rewrite it
through a single kernel-checked `rfl` fact. -/
def strContains (s sub : String) : Bool :=
  (strFindAux s.toList sub.toList).isSome

/-- Adjust one PRESENT slice bound for a sequence of length `len`
(CPython `PySlice_AdjustIndices`): negative indices count from the end;
the result is clamped into `[0, len]` for a positive step, `[-1, len-1]`
for a negative one (`-1` = "before the first element"). -/
def sliceAdj (i : Int) (len : Int) (pos : Bool) : Int :=
  let j := if i < 0 then i + len else i
  if pos then max 0 (min j len)
  else max (-1) (min j (len - 1))

/-- The number of elements a slice yields (CPython's slice-length
formula, both directions, never negative). The divisions are on
nonnegative operands, where every Lean `Int` division convention
agrees. -/
def sliceCount (start stop step : Int) : Nat :=
  if 0 < step then
    if start < stop then ((stop - start - 1) / step).toNat + 1 else 0
  else
    if stop < start then ((start - stop - 1) / (-step)).toNat + 1 else 0

/-- Collect `n` characters starting at index `i`, stepping by `step`.
Every visited index is in range by construction (`sliceAdj`/`sliceCount`
— see `strSlice`), so `getD`'s default is unreachable. Structural on
`n` (kernel-reducible). -/
def strSliceChars (cs : List Char) : Nat → Int → Int → List Char
  | 0, _, _ => []
  | n + 1, i, step => cs.getD i.toNat ' ' :: strSliceChars cs n (i + step) step

/-- Classify one slice component VALUE: `some (some i)` an int index
(bool coerces), `some none` omitted (`None` — ingestion normalizes
absent bounds to the `None` constant, CPython's own compilation),
`none` invalid — the faithful `TypeError` (CPython's message names no
type, and no in-tier value or heap referent can carry `__index__` — the
dunder guard included — so the arm is faithful for refs too). -/
def asSliceIdx : RVal → Option (Option Int)
  | .none => some Option.none
  | v => (asInt v).map some

/-- `s[lower:upper:step]` on a str — CPython slice semantics, value
exact for EVERY string. The components validate in CPython's own order
(`PySlice_Unpack`): `step` first (`TypeError` for a non-index,
`ValueError` for 0), then `lower`, then `upper`. -/
def strSlice (s : String) (lv uv sv : RVal) : Res RVal :=
  match asSliceIdx sv with
  | Option.none =>
    .exn (.typeError "slice indices must be integers or None or have an __index__ method")
  | some st =>
    let step := st.getD 1
    if step == 0 then .exn (.valueError "slice step cannot be zero")
    else
      match asSliceIdx lv with
      | Option.none =>
        .exn (.typeError "slice indices must be integers or None or have an __index__ method")
      | some l =>
        match asSliceIdx uv with
        | Option.none =>
          .exn (.typeError "slice indices must be integers or None or have an __index__ method")
        | some u =>
          let len : Int := s.length
          let pos := 0 < step
          let start := match l with
            | some i => sliceAdj i len pos
            | Option.none => if pos then 0 else len - 1
          let stop := match u with
            | some i => sliceAdj i len pos
            | Option.none => if pos then len else -1
          .ok (.str (String.ofList
            (strSliceChars s.toList (sliceCount start stop step) start step)))

/-- `container[l:u:st]` — the slice RECEIVER dispatch (the components
have already evaluated: CPython builds the slice object before
`BINARY_SUBSCR` looks at the receiver). STRINGS are the tier (value
semantics); slicing a heap list — or a value list/tuple/namedtuple —
succeeds in CPython and ALLOCATES, so those stay loudly out (H5 keeps
list slices with the allocation-aware story — docs/memory-model.md
§list semantics); a non-subscriptable receiver is the faithful
`TypeError`. -/
def sliceVal (v lv uv sv : RVal) : Res RVal :=
  match v with
  | .str s => strSlice s lv uv sv
  | .ref _ =>
    .unsupported "slicing a heap object is outside the tier (str slices only — a list slice allocates; docs/memory-model.md §string semantics)"
  | .listV _ =>
    .unsupported "slicing a list is outside the tier (str slices only; docs/memory-model.md §string semantics)"
  | .tuple _ =>
    .unsupported "slicing a tuple is outside the tier (str slices only; docs/memory-model.md §string semantics)"
  | .ntuple _ _ _ =>
    .unsupported "slicing a namedtuple is outside the tier (str slices only; docs/memory-model.md §string semantics)"
  | v => .exn (.typeError s!"'{v.typeName}' object is not subscriptable")

/-- The decision of a method CALL on a str receiver (H5 strings) — the
`ntupleCallPlan` discipline: a PURE plan decided from the attribute name
alone, BEFORE argument evaluation. Everything outside the tier trio
refuses loudly — never a fake `AttributeError`: CPython's str carries
~45 real methods (`upper`/`split`/`join`/…) plus the dunder protocol,
and guessing which names exist would be silently wrong. -/
inductive StrPlan where
  | swapcase | isupper | islower | upper | index
  | refuse (msg : String)
deriving Repr, Inhabited, BEq

/-- Resolve `s.attr(…)` for a str receiver (see `StrPlan`). -/
def strCallPlan (attr : String) : StrPlan :=
  if attr == "swapcase" then .swapcase
  else if attr == "isupper" then .isupper
  else if attr == "islower" then .islower
  else if attr == "upper" then .upper
  else if attr == "index" then .index
  else .refuse
    s!"method call '.{attr}' on a str is outside the tier ('swapcase'/'isupper'/'islower'/'upper'/'index' only; docs/memory-model.md §string semantics)"

/-! ## The dict tier (H1-proper, docs/memory-model.md)

Fuel-free heap helpers over the bounds-checked access primitives
(`Heap.get?`/`Heap.update`, Runtime.lean). A dangling address is an
interpreter invariant violation — unreachable from well-formed worlds —
and reports loudly (`danglingMsg`), never a silent fallback. -/

/-- The loud report for a dangling address (unreachable from WF worlds). -/
def danglingMsg : String :=
  "internal: dangling heap address (heap well-formedness violation — report this)"

mutual
  /-- Is this runtime value usable as a dict key? Hashability, not
  immutability (docs/memory-model.md §dict semantics): scalars are
  hashable; a tuple iff its elements are; lists are unhashable; a ref's
  hashability depends on its referent — every H1 heap object is a dict,
  which is unhashable (H3 instances revisit this arm, heap parameter and
  all). -/
  def hashableKey : RVal → Bool
    | .none | .bool _ | .int _ | .str _ => true
    | .tuple xs => hashableKeyList xs.toList
    -- a namedtuple hashes as a tuple (tuple.__hash__): hashable iff its
    -- elements are — sunfish's `(pos, depth, root)` keys stay in tier
    | .ntuple _ _ xs => hashableKeyList xs.toList
    | .listV _ => false
    | .ref _ => false

  /-- Elementwise `hashableKey`. -/
  def hashableKeyList : List RVal → Bool
    | [] => true
    | v :: vs => hashableKey v && hashableKeyList vs
end

/-- CPython's type name in `unhashable type: '…'` messages. A `.ref` names
its referent's type — every H1 heap object is a dict. (H2: superseded by
the heap-resolving `RVal.typeNameH` in every reachable message position;
retained as pure vocabulary.) -/
def RVal.unhashName : RVal → String
  | .ref _ => "dict"
  | v => v.typeName

/-- Heap-resolving type name (H2): a `.ref` names its referent's type.
The `"object"` fallback is the dangling arm — unreachable from WF worlds,
and never part of a decided outcome that isn't already loud.

Deliberately OUT of `py_simp`/`interpUnfolds` (recorded H2 finding, the
`sortInts`/`heapEq` freeze family): it occurs only inside error-message
interpolations of undecided helper arms, so as a simp member it buys
nothing — and with it in the set a plain symbolic run whnf-storms
(≈740k `List.rec` / 1.5M `Array.toList` unfoldings on `sf_bound_rec`'s
exit lemma before timing out; message-position `String.append` chains
keep re-offering the pattern). A raise-theorem that needs a heap-named
message passes it explicitly. -/
def RVal.typeNameH (h : Heap) : RVal → String
  | .ref a =>
    match Heap.get? h a with
    | some (.dict _ _) => "dict"
    | some (.list _) => "list"
    -- H3: the class NAME lives in the module, not the heap — "object" is
    -- the message-only placeholder (the harness compares exception CLASS
    -- names, never messages).
    | some (.instance _ _) => "object"
    | some (.generator ..) => "generator"
    | some (.closure ..) => "function"
    | Option.none => "object"
  | v => v.typeName

/-! (`RVal.refFree`/`refFreeList` moved to Runtime.lean at H2: the public
wrapper's freeze fast path — `Run.toPublic` — tests it.) -/

mutual
  /-- Key equality: Python `==` restricted to HASHABLE (hence ref-free)
  values — bool/int coercion (`d[True]` is `d[1]`), tuples elementwise.
  Pure (`Bool`, not `Res`): callers have checked `hashableKey` on the
  probe, and stored keys were checked at insertion. -/
  def keyEq : RVal → RVal → Bool
    | .none, .none => true
    | .bool a, .bool b => a == b
    | .bool a, .int m => (if a then (1 : Int) else 0) == m
    | .int n, .bool b => n == (if b then (1 : Int) else 0)
    | .int n, .int m => n == m
    | .str s, .str t => s == t
    | .tuple xs, .tuple ys => keyEqList xs.toList ys.toList
    -- namedtuple keys ARE tuple keys (hash and `==` erase the class):
    -- `d[Move(1,2,"")]` and `d[(1,2,"")]` address one entry, as in CPython
    | .ntuple _ _ xs, .ntuple _ _ ys => keyEqList xs.toList ys.toList
    | .ntuple _ _ xs, .tuple ys => keyEqList xs.toList ys.toList
    | .tuple xs, .ntuple _ _ ys => keyEqList xs.toList ys.toList
    | _, _ => false

  /-- Elementwise `keyEq`; `false` on length mismatch. -/
  def keyEqList : List RVal → List RVal → Bool
    | [], [] => true
    | a :: as, b :: bs => keyEq a b && keyEqList as bs
    | _, _ => false
end

mutual
  /-- Does the (hashability-failing) key contain a ref to a class
  INSTANCE (tuples searched recursively)? Instances ARE hashable in
  CPython (identity hash) — `keyRefusal` refuses them loudly instead of
  raising a fake `TypeError`. -/
  def keyHasInstanceRef (h : Heap) : RVal → Bool
    | .ref a =>
      match Heap.get? h a with
      | some (.instance _ _) => true
      | some (.generator ..) => true
      | some (.closure ..) => true  -- identity hash, like instances: refuse
      | _ => false
    | .tuple xs => keyHasInstanceRefList h xs.toList
    | .ntuple _ _ xs => keyHasInstanceRefList h xs.toList
    | _ => false

  /-- Elementwise `keyHasInstanceRef`. -/
  def keyHasInstanceRefList (h : Heap) : List RVal → Bool
    | [] => false
    | v :: vs => keyHasInstanceRef h v || keyHasInstanceRefList h vs
end

/-- The outcome when a probe/key fails `hashableKey`: a dict/list
referent (or a value-list) is CPython's faithful `TypeError`; a key
containing an INSTANCE ref is hashable in CPython (identity hash +
identity `__eq__`) but instance dict keys are outside the H3 tier —
loud, never a fake `TypeError`. -/
def keyRefusal (h : Heap) (k : RVal) : Res α :=
  if keyHasInstanceRef h k then
    .unsupported "a class instance or generator as a dict key (identity hash) is outside the tier (docs/memory-model.md)"
  else
    .exn (.typeError s!"unhashable type: '{RVal.typeNameH h k}'")

/-- First entry whose stored key equals `k` (insertion order). -/
def dictFind : List (RVal × RVal) → RVal → Option RVal
  | [], _ => Option.none
  | (k', v') :: rest, k => if keyEq k' k then some v' else dictFind rest k

/-- Store `k ↦ v`: an equal key present replaces ONLY THE VALUE (stored key
and insertion position retained — `{True: _}` updated through `1` still
lists `[True]`); an absent key appends. The `Bool` reports growth (the
shape change `shapeVersion` counts — iterator invalidation). -/
def dictStore : List (RVal × RVal) → RVal → RVal → List (RVal × RVal) × Bool
  | [], k, v => ([(k, v)], true)
  | (k', v') :: rest, k, v =>
    if keyEq k' k then ((k', v) :: rest, false)
    else
      match dictStore rest k v with
      | (rest', grew) => ((k', v') :: rest', grew)

/-- Build a dict literal's entries: inserts left to right (duplicate equal
keys: first key/position, last value), each key hashability-checked at its
insertion — CPython's `BUILD_MAP` order (every element expression was
already evaluated by the caller). The heap parameter serves only the
error message (H2: an unhashable `.ref` key names its referent's type —
`{[1]: 0}` is `unhashable type: 'list'`). -/
def dictBuild (h : Heap) (acc : List (RVal × RVal)) : List (RVal × RVal) → Res (List (RVal × RVal))
  | [] => .ok acc
  | (k, v) :: rest =>
    if hashableKey k then dictBuild h (dictStore acc k v).1 rest
    else keyRefusal h k

/-- `o[k]` on a heap object. Dicts: unhashable keys raise BEFORE any scan
(even on an empty dict); a missing key is a faithful `KeyError`. Lists
(H2): int/bool index, negative indices from the end, out of range a
faithful `IndexError`, non-int index a faithful `TypeError`. -/
def heapIndex (h : Heap) (a : Addr) (k : RVal) : Res RVal :=
  match Heap.get? h a with
  | some (.dict es _) =>
    if hashableKey k then
      match dictFind es.toList k with
      | some v => .ok v
      | Option.none => .exn .keyError
    else keyRefusal h k
  | some (.list xs) =>
    match asInt k with
    | some i =>
      match normIndex i xs.size with
      | some n => .ok (xs.getD n .none)
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"list indices must be integers, not {RVal.typeNameH h k}")
  -- H3: no `__getitem__` can exist (dunder guard), so the default
  -- protocol's refusal is the faithful outcome.
  | some (.instance _ _) => .exn (.typeError "'object' object is not subscriptable")
  | some (.generator ..) => .exn (.typeError "'generator' object is not subscriptable")
  | some (.closure ..) => .exn (.typeError "'function' object is not subscriptable")
  | Option.none => .unsupported danglingMsg

/-- `o[k] = v` on a heap object. Dicts: value replacement keeps the shape
version; insertion increments it (`dictStore`'s growth bit). Lists (H2):
in-place element replacement (aliasing-visible); out of range a faithful
`IndexError` (CPython: assignment never extends a list); the `List.set`
route keeps the write kernel-reducible with no dead bounds arm. -/
def heapStore (h : Heap) (a : Addr) (k v : RVal) : Res Heap :=
  match Heap.get? h a with
  | some (.dict es ver) =>
    if hashableKey k then
      match dictStore es.toList k v with
      | (es', grew) =>
        match Heap.update h a (.dict es'.toArray (if grew then ver + 1 else ver)) with
        | some h' => .ok h'
        | Option.none => .unsupported danglingMsg
    else keyRefusal h k
  | some (.list xs) =>
    match asInt k with
    | some i =>
      match normIndex i xs.size with
      | some n =>
        match Heap.update h a (.list ((xs.toList.set n v).toArray)) with
        | some h' => .ok h'
        | Option.none => .unsupported danglingMsg
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"list indices must be integers, not {RVal.typeNameH h k}")
  -- H3: no `__setitem__` can exist (dunder guard) — faithful refusal.
  | some (.instance _ _) =>
    .exn (.typeError "'object' object does not support item assignment")
  | some (.generator ..) =>
    .exn (.typeError "'generator' object does not support item assignment")
  | some (.closure ..) =>
    .exn (.typeError "'function' object does not support item assignment")
  | Option.none => .unsupported danglingMsg

/-- `len(o)` on a heap object: dict entry count / list length; an
instance has no `__len__` (dunder guard) — the faithful `TypeError`. -/
def heapLen (h : Heap) (a : Addr) : Res RVal :=
  match Heap.get? h a with
  | some (.dict es _) => .ok (.int es.size)
  | some (.list xs) => .ok (.int xs.size)
  | some (.instance _ _) => .exn (.typeError "object of type 'object' has no len()")
  | some (.generator ..) => .exn (.typeError "object of type 'generator' has no len()")
  | some (.closure ..) => .exn (.typeError "object of type 'function' has no len()")
  | Option.none => .unsupported danglingMsg

/-- `d.get(k)` / `d.get(k, default)` (the H1 method tier): absent keys
yield the default, never `KeyError`; unhashable probes still raise.
`.get` on a list is a faithful `AttributeError` — loud until `PyErr`
carries that class. -/
def heapGet (h : Heap) (a : Addr) (k dflt : RVal) : Res RVal :=
  match Heap.get? h a with
  | some (.dict es _) =>
    if hashableKey k then .ok ((dictFind es.toList k).getD dflt)
    else keyRefusal h k
  | some (.list _) => .exn .attributeError   -- 'list' object has no attribute 'get'
  | some (.instance _ _) =>
    .unsupported "internal: '.get' dispatch reached an instance receiver (method dispatch owns instances — report this)"
  | some (.generator ..) => .exn .attributeError
  | some (.closure ..) => .exn .attributeError  -- functions have no .get
  | Option.none => .unsupported danglingMsg

/-- `lst.append(x)` (H2): push in place — the mutation is visible through
every alias. The call's value is `None` (`evalExpr`'s method arm).
`.append` on a dict is a faithful `AttributeError` — loud until `PyErr`
carries that class. -/
def heapAppend (h : Heap) (a : Addr) (v : RVal) : Res Heap :=
  match Heap.get? h a with
  | some (.list xs) =>
    match Heap.update h a (.list (xs.push v)) with
    | some h' => .ok h'
    | Option.none => .unsupported danglingMsg
  | some (.dict _ _) => .exn .attributeError  -- 'dict' object has no attribute 'append'
  | some (.instance _ _) =>
    .unsupported "internal: '.append' dispatch reached an instance receiver (method dispatch owns instances — report this)"
  | some (.generator ..) => .exn .attributeError
  | some (.closure ..) => .exn .attributeError
  | Option.none => .unsupported danglingMsg

/-- `lst.pop()` / `lst.pop(i)` (H2): remove and return the element at `i`
(default `-1`, the last; negatives from the end); an out-of-range or
empty pop is a faithful `IndexError`. `dict.pop` is a REAL CPython method
(with different semantics) — loud, not an `AttributeError`. -/
def heapPop (h : Heap) (a : Addr) (i : Option Int) : Res (Heap × RVal) :=
  match Heap.get? h a with
  | some (.list xs) =>
    match normIndex (i.getD (-1)) xs.size with
    | some n =>
      match Heap.update h a (.list ((xs.toList.eraseIdx n).toArray)) with
      | some h' => .ok (h', xs.getD n .none)
      | Option.none => .unsupported danglingMsg
    | Option.none => .exn .indexError
  | some (.dict _ _) =>
    .unsupported "'.pop' on a dict is outside the tier (dict.pop lands with the dict-method tier)"
  | some (.instance _ _) =>
    .unsupported "internal: '.pop' dispatch reached an instance receiver (method dispatch owns instances — report this)"
  | some (.generator ..) => .exn .attributeError
  | some (.closure ..) => .exn .attributeError
  | Option.none => .unsupported danglingMsg

/-- `o.attr = v` on a heap object (H3: mutable self — the attribute
store). Instances update their attribute table in place (`Env.set`
semantics: replace-in-place or append — CPython `__dict__` insertion
order); a dict/list has no writable attributes — the faithful
`AttributeError` (no `__slots__`/instance dict on builtins). -/
def heapAttrStore (h : Heap) (a : Addr) (attr : String) (v : RVal) : Res Heap :=
  match Heap.get? h a with
  | some (.instance ci attrs) =>
    match Heap.update h a (.instance ci (Env.set attrs.toList attr v).toArray) with
    | some h' => .ok h'
    | Option.none => .unsupported danglingMsg
  | some (.dict _ _) => .exn .attributeError
  | some (.list _) => .exn .attributeError
  -- a generator's attributes (`gi_frame`, …) are all read-only
  | some (.generator ..) => .exn .attributeError
  | some (.closure ..) =>
      .unsupported "attribute stores on a function object are outside the tier (CPython allows them; a fake AttributeError would be wrong)"
  | Option.none => .unsupported danglingMsg

/-- Truthiness including heap objects: `bool(d)`/`bool(lst)` is
`len != 0`; an instance is `True` (default object protocol — no
`__bool__`/`__len__` can exist, the dunder guard). Non-ref values decide
exactly as the pure `truthy` (the proof layer's vocabulary —
`truthyH_of_truthy` lifts pure facts, so VC rule hypotheses never mention
the heap). -/
def truthyH (h : Heap) : RVal → Res Bool
  | .ref a =>
    match Heap.get? h a with
    | some (.dict es _) => .ok (es.size != 0)
    | some (.list xs) => .ok (xs.size != 0)
    | some (.instance _ _) => .ok true
    -- a generator object is always truthy (no `__bool__`/`__len__`)
    | some (.generator ..) => .ok true
    | some (.closure ..) => .ok true
    | Option.none => .unsupported danglingMsg
  | v => truthy v

/-- A decided pure truthiness lifts to every heap (`truthy`'s only `.ref`
arm is `unsupported`, which never decides). -/
theorem truthyH_of_truthy {h : Heap} {v : RVal} {b : Bool}
    (ht : truthy v = .ok b) : truthyH h v = .ok b := by
  cases v <;> simp_all [truthy, truthyH]

mutual
  /-- Python `==` over the heap (docs/memory-model.md §identity) — the
  H1-complete equality. Ref/ref: (1) identity shortcut (`d == d` holds
  even for self-cyclic `d`); (2) re-entering an ACTIVE distinct pair is a
  faithful `RecursionError` (two separate self-cyclic dicts do NOT compare
  equal — Python does not equate bisimilar cycles); (3) size check;
  (4) the LEFT dict traversed in insertion order, keys looked up in the
  right dict, values compared recursively with the pair pushed onto the
  active list (an early mismatch returns `False` before a later cyclic
  value would raise). Ref vs non-ref is a faithful `False`. Tuples/lists
  recurse HERE (refs may hide inside); scalar pairs decide as `valEq`.
  Fueled: exhaustion is `.timeout`, never a semantic answer; cycle
  detection is fuel-INDEPENDENT. -/
  def heapEq (h : Heap) (fuel : Nat) (active : List (Addr × Addr))
      (a b : RVal) : Res Bool :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      match a, b with
      | .ref x, .ref y =>
        if x == y then .ok true
        else if active.contains (x, y) then .exn .recursionError
        else
          match Heap.get? h x, Heap.get? h y with
          | some (.dict es _), some (.dict fs _) =>
            if es.size == fs.size then
              heapEqEntries h fuel ((x, y) :: active) es.toList fs.toList
            else .ok false
          | some (.list xs), some (.list ys) =>
            if xs.size == ys.size then
              heapEqList h fuel ((x, y) :: active) xs.toList ys.toList
            else .ok false
          | some _, some _ => .ok false   -- dict vs list: cross-type `==`
          | _, _ => .unsupported danglingMsg
      | .ref _, _ => .ok false
      | _, .ref _ => .ok false
      | .tuple xs, .tuple ys => heapEqList h fuel active xs.toList ys.toList
      | .listV xs, .listV ys => heapEqList h fuel active xs.toList ys.toList
      -- namedtuples compare as tuples through the heap too (elements may
      -- carry refs — a namedtuple holding a list is comparable)
      | .ntuple _ _ xs, .ntuple _ _ ys => heapEqList h fuel active xs.toList ys.toList
      | .ntuple _ _ xs, .tuple ys => heapEqList h fuel active xs.toList ys.toList
      | .tuple xs, .ntuple _ _ ys => heapEqList h fuel active xs.toList ys.toList
      | a, b => valEq a b

  /-- Elementwise `heapEq` (tuple/list contents may contain refs); `false`
  on length mismatch. -/
  def heapEqList (h : Heap) (fuel : Nat) (active : List (Addr × Addr))
      (as bs : List RVal) : Res Bool :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      match as, bs with
      | [], [] => .ok true
      | a :: as, b :: bs => do
        let e ← heapEq h fuel active a b
        if e then heapEqList h fuel active as bs else return false
      | _, _ => .ok false

  /-- Left-dict traversal of the ref/ref case: each stored key looked up in
  the right entry list. -/
  def heapEqEntries (h : Heap) (fuel : Nat) (active : List (Addr × Addr))
      (left right : List (RVal × RVal)) : Res Bool :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      match left with
      | [] => .ok true
      | (k, v) :: rest =>
        match dictFind right k with
        | Option.none => .ok false
        | some w => do
          let e ← heapEq h fuel active v w
          if e then heapEqEntries h fuel active rest right else return false
end

/-- One `x in lst` scan step (H2): CPython's `list.__contains__` compares
`element == probe` (element on the LEFT) per element, first hit wins —
elements may be refs, so each comparison is the fueled `heapEq`
(exhaustion `.timeout`; the scan itself is list-structural). -/
def heapContainsScan (h : Heap) (fuel : Nat) (x : RVal) : List RVal → Res Bool
  | [] => .ok false
  | v :: vs => do
    let e ← heapEq h fuel [] v x
    if e then return true else heapContainsScan h fuel x vs

/-- `k in o` on a heap object. Dicts: key membership (unhashable probes
raise, empty dict included — pure `keyEq`, keys are hashable). Lists
(H2): the fueled `==` scan (`heapContainsScan`). -/
def heapContains (h : Heap) (fuel : Nat) (a : Addr) (k : RVal) : Res Bool :=
  match Heap.get? h a with
  | some (.dict es _) =>
    if hashableKey k then .ok (dictFind es.toList k).isSome
    else keyRefusal h k
  | some (.list xs) => heapContainsScan h fuel k xs.toList
  -- H3: no `__contains__`/`__iter__`/`__getitem__` (dunder guard) —
  -- the faithful `TypeError`.
  | some (.instance _ _) =>
    .exn (.typeError "argument of type 'object' is not iterable")
  | some (.generator ..) =>
    -- `x in gen` CONSUMES the generator in CPython: a membership test
    -- with a side effect, which this pure helper cannot express — loud,
    -- never a wrong answer (docs/memory-model.md §generator semantics)
    .unsupported "'in' on a generator CONSUMES it (a stateful membership test) — outside the tier"
  | some (.closure ..) =>
    .exn (.typeError "argument of type 'function' is not iterable")
  | Option.none => .unsupported danglingMsg

/-- `x in c` for EVERY in-tier container (H5 iteration): a heap referent
delegates to `heapContains` (dict keys / the H2 list scan); a str is
CPython's SUBSTRING test with the faithful left-operand `TypeError`
(`'in <string>' requires string as left operand, not …` — the only
container whose `in` is not element membership); value tuples, boundary
value-lists and namedtuples scan their elements with the same
`element == probe` convention as lists (`heapContainsScan`: elements may
be refs, so each step is the fueled `heapEq`). Namedtuples scan
class-erased, like every other tuple observation. Anything else is the
faithful "not iterable" `TypeError`. -/
def valContains (h : Heap) (fuel : Nat) (a b : RVal) : Res Bool :=
  match b with
  | .ref d => heapContains h fuel d a
  | .str s =>
    match a with
    | .str sub => .ok (strContains s sub)
    | a => .exn (.typeError
        s!"'in <string>' requires string as left operand, not {RVal.typeNameH h a}")
  | .listV xs => heapContainsScan h fuel a xs.toList
  | .tuple xs => heapContainsScan h fuel a xs.toList
  | .ntuple _ _ xs => heapContainsScan h fuel a xs.toList
  | b => .exn (.typeError s!"argument of type '{b.typeName}' is not iterable")

/-- The heap-aware comparison step (`evalCompareChain` consumes this since
H1-proper). `==`/`!=` go through `heapEq`; `is`/`is not` decide the `None`
link (as before), ref/ref address identity, and ref-vs-immediate `False`
faithfully — refusing only identity between two non-`None` immediates
(implementation-defined); `in`/`not in` are `valContains` (H5 iteration: dict keys, the H2 list
scan, str substrings, and value tuple/namedtuple element scans);
ordering delegates to the pure `evalCompareOp`. -/
def evalCompareOpH (h : Heap) (fuel : Nat) (op : CmpOp) (a b : RVal) : Res Bool :=
  match op with
  | .eq =>
    -- ref-free pairs decide by the pure `valEq` (the fast path keeps
    -- `heapEq` — a frozen recursion point — out of ordinary comparisons)
    if RVal.refFree a && RVal.refFree b then valEq a b
    else heapEq h fuel [] a b
  | .notEq => do
    let e ← if RVal.refFree a && RVal.refFree b then valEq a b
            else heapEq h fuel [] a b
    return !e
  | .is =>
    if a.isNone || b.isNone then .ok (a.isNone && b.isNone)
    else
      match a, b with
      | .ref x, .ref y => .ok (x == y)
      | .ref _, _ => .ok false
      | _, .ref _ => .ok false
      | a, b =>
        .unsupported
          s!"'is' between '{a.typeName}' and '{b.typeName}' (identity is not value-determined) is outside the tier"
  | .isNot =>
    if a.isNone || b.isNone then .ok (!(a.isNone && b.isNone))
    else
      match a, b with
      | .ref x, .ref y => .ok (x != y)
      | .ref _, _ => .ok true
      | _, .ref _ => .ok true
      | a, b =>
        .unsupported
          s!"'is not' between '{a.typeName}' and '{b.typeName}' (identity is not value-determined) is outside the tier"
  | .inOp => valContains h fuel a b
  | .notIn => do let e ← valContains h fuel a b; return !e
  | op => evalCompareOp op a b

/-- Unary operators over the heap: `not d` is dict truthiness; `-` stays
pure (a `.ref` operand is refused there). -/
def evalUnaryOpH (h : Heap) (op : UnaryOp) (v : RVal) : Res RVal :=
  match op with
  | .not => do let b ← truthyH h v; return .bool (!b)
  | .usub => evalUnaryOp .usub v

/-- `len` over the heap: dicts count entries; non-refs decide as `lenVal`. -/
def lenValH (h : Heap) : RVal → Res RVal
  | .ref a => heapLen h a
  | v => lenVal v

/-- Subscript read over the heap: a `.ref` container is a dict read
(`KeyError` faithful); a `.ref` INDEX into a value container is a faithful
`TypeError` (every H1 heap object is a dict — `lst[d]`); everything else
decides as the pure `indexVal`. -/
def indexValH (h : Heap) (container index : RVal) : Res RVal :=
  match container, index with
  | .ref a, k => heapIndex h a k
  | .listV _, .ref b => .exn (.typeError s!"list indices must be integers, not {RVal.typeNameH h (.ref b)}")
  | .tuple _, .ref b => .exn (.typeError s!"tuple indices must be integers, not {RVal.typeNameH h (.ref b)}")
  | .ntuple _ _ _, .ref b => .exn (.typeError s!"tuple indices must be integers, not {RVal.typeNameH h (.ref b)}")
  | .str _, .ref b => .exn (.typeError s!"string indices must be integers, not {RVal.typeNameH h (.ref b)}")
  | c, i => indexVal c i

/-- `sorted(v)` over the heap (H2/H6): a heap-list argument reads its
elements and ALLOCATES the fresh result list — `sorted` always returns a
NEW list; all-int ascending keeps the original `sortInts` term, the rest
sorts stably by `rvalLt` (`sortByLt`). Non-ref values decide as the pure
`sortedVal` (heap unchanged). `sorted` over a dict iterates its KEYS in
CPython — loud (live dict iteration). A GENERATOR argument never reaches
here: the dispatch arm drains it through `drainIter` first (the guard
below is the loud hand-built-module defense). -/
def sortedValH (h : Heap) (v : RVal) (desc : Bool := false) : Res (Heap × RVal)
 := match v with
  | .ref a =>
    match Heap.get? h a with
    | some (.list xs) =>
      (match (if desc then Option.none else asIntList xs.toList) with
       | some ns =>
          .ok (h.push (.list (((sortInts ns).map RVal.int).toArray)), .ref h.size)
       | Option.none => do
          return (h.push (.list (← sortByLt desc xs.toList).toArray), .ref h.size))
    | some (.dict _ _) =>
        .unsupported "sorted() over dict keys is outside the tier (live dict iteration; docs/memory-model.md)"
    | some (.instance _ _) =>
        .exn (.typeError "'object' object is not iterable")
    | some (.generator ..) =>
        .unsupported "sorted() over a generator DRAINS it (a stateful read) — outside the tier (docs/memory-model.md §generator semantics)"
    | some (.closure ..) => .exn (.typeError "'function' object is not iterable")
    | Option.none => .unsupported danglingMsg
  | v => do let r ← sortedVal v desc; return (h, r)

/-- `max`/`min` over the heap (H2): a single heap-list argument reads its
elements (all-int tier); `max`/`min` over a dict ranges over its KEYS in
CPython — loud (live dict iteration). Everything else decides as the
pure `extremumVal`. -/
def extremumValH (h : Heap) (isMax : Bool) (vs : List RVal) : Res RVal :=
  match vs with
  | [v] =>
    (match v with
     | .ref a =>
       (match Heap.get? h a with
        | some (.list xs) =>
          (match asIntList xs.toList with
           | some (n :: rest) => .ok (.int (foldExtremum isMax n rest))
           | some [] =>
               .exn (.valueError s!"{if isMax then "max" else "min"}() arg is an empty sequence")
           | Option.none =>
               extremumOf isMax (if isMax then "max" else "min") xs.toList)
        | some (.dict _ _) =>
            .unsupported s!"{if isMax then "max" else "min"}() over dict keys is outside the tier (live dict iteration; docs/memory-model.md)"
        | some (.instance _ _) =>
            .exn (.typeError "'object' object is not iterable")
        | some (.generator ..) =>
            .unsupported s!"{if isMax then "max" else "min"}() over a generator DRAINS it (a stateful read) — outside the tier"
        | some (.closure ..) =>
            .exn (.typeError "'function' object is not iterable")
        | Option.none => .unsupported danglingMsg)
     | v => extremumVal isMax [v])
  | vs => extremumVal isMax vs

/-- Snapshot the captured names from a frame (H7 nested defs,
docs/memory-model.md §nested defs and closures): `none` iff any name is
unbound — unreachable through the extractor's admission (every capture
is pre-def-bound), kept loud for hand-built modules. -/
def capturesSnapshot (env : Env) : List String → Option REnv
  | [] => some []
  | c :: cs => do
    let v ← Env.lookup env c
    let rest ← capturesSnapshot env cs
    return (c, v) :: rest

/-- Is the value a ref to a live generator object? (H6 draining
consumers — the dispatch arms fork on this BEFORE the pure heap
workers, because draining needs the stepper.) -/
def isGeneratorRef (h : Heap) : RVal → Bool
  | .ref a =>
    match Heap.get? h a with
    | some (.generator ..) => true
    | _ => false
  | _ => false

/-- Short-circuit truthiness scan for `any`/`all` over a SNAPSHOT (value
sequences and heap lists): stop at the first truthy (`any`,
`isAll = false`) or falsy (`all`) element. No user code can run
mid-scan in tier, so the snapshot IS the live semantics; generators
never come here — they step through `anyAllIter`, which is what makes
the partial drain observable. -/
def anyAllScan (h : Heap) (isAll : Bool) : List RVal → Res Bool
  | [] => .ok isAll
  | v :: vs => do
    let b ← truthyH h v
    if b != isAll then .ok b else anyAllScan h isAll vs

/-- The names of an unpacking target's elements; `none` if any element is not
a plain `Name` (nested or starred patterns are outside the v0 tier). -/
def targetNames (elts : Array Expr) : Option (List String) :=
  elts.foldr (init := some []) fun e acc =>
    match e, acc with
    | .name id _, some ids => some (id :: ids)
    | _, _ => Option.none

/-- Bind names to values pairwise, left to right (arity already checked). -/
def bindAll (env : Env) : List String → List RVal → Env
  | n :: ns, v :: vs => bindAll (Env.set env n v) ns vs
  | _, _ => env

/-- Assign an already-evaluated value to a single assignment target:
a `Name`, or a `Tuple`/`List` of `Name`s (tuple unpacking — the unpacked
value must be a `listV`/`tuple`; arity mismatch → `ValueError`;
non-iterable → `TypeError`; `str` unpacking is Python-valid but outside the
tier; unpacking a `.ref` iterates the heap object — loud until the live
iterator lands). Environment-only BY DESIGN: subscript stores
(`d[k] = v`, a heap write) are `execStmt`'s subscript-target arm since
H1-proper — the `.subscript` arm here is the loud residue reachable only
through `for`-loop targets and similar rarities. -/
def assignTo (env : Env) (target : Expr) (v : RVal) : Res Env :=
  match target with
  | .name id _ => .ok (Env.set env id v)
  | .tuple elts _ | .list elts _ =>
    match targetNames elts with
    | Option.none =>
      .unsupported "unpacking targets other than plain names are outside the v0 tier"
    | some names =>
      match v with
      | .listV xs | .tuple xs =>
        if xs.size = names.length then .ok (bindAll env names xs.toList)
        else if names.length < xs.size then
          .exn (.valueError s!"too many values to unpack (expected {names.length})")
        else
          .exn (.valueError
            s!"not enough values to unpack (expected {names.length}, got {xs.size})")
      | .ntuple _ _ xs =>
        -- namedtuples unpack as tuples (`i, j, prom = move`)
        if xs.size = names.length then .ok (bindAll env names xs.toList)
        else if names.length < xs.size then
          .exn (.valueError s!"too many values to unpack (expected {names.length})")
        else
          .exn (.valueError
            s!"not enough values to unpack (expected {names.length}, got {xs.size})")
      | .str _ => .unsupported "unpacking a str is outside the v0 tier"
      | .ref _ =>
          .unsupported "unpacking a heap object is outside the H1 tier (dict unpacking iterates keys — with the live iterator; docs/memory-model.md)"
      | v => .exn (.typeError s!"cannot unpack non-iterable {v.typeName} object")
  | .subscript .. => .unsupported "assignment to a subscript is outside the v0 tier"
  | t => .unsupported s!"assignment target '{t.kindName}' is outside the v0 tier"

/-- Heap-aware assignment dispatch (H2): unpacking FROM a heap list reads
its elements (CPython unpacks eagerly — a snapshot read; the heap is
untouched); dict unpacking iterates keys — loud (live dict iteration);
every other case is the pure `assignTo` (name targets bind refs as
values, faithfully). The `.listV` re-wrap reuses `assignTo`'s unpack
logic verbatim — arity `ValueError`s included. -/
def assignToH (h : Heap) (env : Env) (target : Expr) (v : RVal) : Res Env :=
  match target with
  | .tuple _ _ | .list _ _ =>
    (match v with
     | .ref a =>
       match Heap.get? h a with
       | some (.list xs) => assignTo env target (.listV xs)
       | some (.dict _ _) =>
         .unsupported "unpacking a dict iterates its keys — outside the tier (live dict iteration; docs/memory-model.md)"
       | some (.instance _ _) =>
         -- no `__iter__` can exist (dunder guard) — faithful
         .exn (.typeError "cannot unpack non-iterable object object")
       | some (.generator ..) =>
         .unsupported "unpacking a generator DRAINS it (a stateful read) — outside the tier (docs/memory-model.md §generator semantics)"
       | some (.closure ..) =>
         .exn (.typeError "cannot unpack non-iterable function object")
       | Option.none => .unsupported danglingMsg
     | v => assignTo env target v)
  | t => assignTo env t v

/-- A decided pure assignment lifts to every heap: `assignToH` diverts
only (tuple/list target, `.ref` value) pairs, on which the pure
`assignTo` never decides `.ok` (its ref-unpack arm is loud). What keeps
the VC assign rule's `assignTo` hypothesis sufficient at H2. -/
theorem assignToH_of_assignTo {h : Heap} {env : Env} {target : Expr}
    {v : RVal} {env' : Env} (ha : assignTo env target v = .ok env') :
    assignToH h env target v = .ok env' := by
  cases target <;> try (simpa [assignToH] using ha)
  case tuple elts sp =>
    cases v <;> try (simpa [assignToH] using ha)
    case ref a =>
      simp only [assignTo] at ha
      cases htn : targetNames elts with
      | none => simp [htn] at ha
      | some names => simp [htn] at ha
  case list elts sp =>
    cases v <;> try (simpa [assignToH] using ha)
    case ref a =>
      simp only [assignTo] at ha
      cases htn : targetNames elts with
      | none => simp [htn] at ha
      | some names => simp [htn] at ha

/-- Module function table lookup. Each `def` rebinds the module-level name, so
with duplicate definitions the LAST one wins, exactly as in CPython. Class
METHODS also live here, flattened under `"<class>.<method>"` qualified names
(see `ClassDefn`): a plain identifier can never contain `.`, so plain-name
resolution never sees them; `callIn` resolves them exactly like functions,
which is what lets method calls reuse `callIn`/`CallsIn` verbatim. -/
def findFunction (m : Module) (fname : String) : Option FunctionDefn :=
  m.functions.findRev? (fun f => f.name == fname)

/-! ## The class table (H3, docs/memory-model.md §H3) -/

/-- Scan for the LAST class with this name, tracking indices (the
recursion prefers the tail match — CPython's last-binding-wins).
List-structural: kernel-reducible. -/
def findClassAux : List ClassDefn → String → Nat → Option (Nat × ClassDefn)
  | [], _, _ => Option.none
  | c :: rest, cname, i =>
    match findClassAux rest cname (i + 1) with
    | some r => some r
    | Option.none => if c.name == cname then some (i, c) else Option.none

/-- Resolve a class NAME to its canonical `ClassId` (the index into
`Module.classes`) and its record. Last definition wins, so instances
always carry the canonical id — an instance of a shadowed earlier
same-named class is unconstructible (see `ClassDefn`). -/
def findClass (m : Module) (cname : String) : Option (Nat × ClassDefn) :=
  findClassAux m.classes.toList cname 0

/-- Positional class-record lookup (instance method dispatch: the
instance's `ClassId` is the index). List-structural, never `getD`. -/
def classAt : List ClassDefn → Nat → Option ClassDefn
  | [], _ => Option.none
  | c :: _, 0 => some c
  | _ :: rest, n + 1 => classAt rest n

/-- The class record of a `ClassId`. A `none` is an interpreter invariant
violation (ids are minted by `findClass`) and every caller reports it
loudly (`danglingMsg` style). -/
def getClass? (m : Module) (i : ClassId) : Option ClassDefn :=
  classAt m.classes.toList i

/-- Does the character list end in `__`? (helper of `dunderShaped`;
list-structural). -/
def endsWithUU : List Char → Bool
  | [] => false
  | ['_', '_'] => true
  | [_] => false
  | _ :: rest => endsWithUU rest

/-- Is this a dunder name (`__…__`)? Structural on the string's character
list (`String.startsWith`/`endsWith` are `USize` loops the kernel cannot
reduce — the `sortInts` constraint). -/
def dunderShaped (n : String) : Bool :=
  match n.toList with
  | '_' :: '_' :: rest => endsWithUU rest
  | _ => false

/-- Does the class define any dunder method besides `__init__`? Such a
class is UNINSTANTIABLE in tier (loud at `ClassName(…)`): every
implicit-protocol site the tier decides (equality, truthiness, attribute
lookup, `is`, iteration refusals, …) assumes DEFAULT object semantics,
which a user dunder would silently override. Because instantiation guards
this, every instance that EXISTS has default protocol — which is what
makes the instance arms of `heapEq` (identity), `truthyH` (`True`), and
the faithful `TypeError`/`AttributeError` arms below correct. -/
def hasExtraDunder (c : ClassDefn) : Bool :=
  c.methods.toList.any fun n => dunderShaped n && n != "__init__"

/-- The decision of an attribute READ (`x.attr` as a value) on a heap
receiver, computed PURELY from the referent — the interpreter arm and its
meta-theorems (`fuelMono`/`worldInv`) fork on this one scrutinee instead
of a match nested under the receiver binder. -/
inductive AttrReadPlan where
  | value (v : RVal)      -- instance attribute (heap read)
  | boundMethod           -- class method referenced as a value (loud)
  | missing               -- faithful AttributeError (default protocol)
  | refuse (msg : String) -- out-of-tier receiver (loud)
  | dangling              -- invariant violation (loud)
deriving Repr, Inhabited, BEq

/-- Resolve `x.attr` (read position) against the heap: instance attrs
first (CPython instance `__dict__` precedes the class for plain
attributes), then the class's methods (a bound-method VALUE — loud),
then the faithful `AttributeError` (no `__getattr__` can exist — the
dunder guard). Dict/list attributes are their built-in methods — loud in
read position. -/
def attrReadPlan (m : Module) (h : Heap) (a : Addr) (attr : String) :
    AttrReadPlan :=
  match Heap.get? h a with
  | some (.instance ci attrs) =>
    (match Env.lookup attrs.toList attr with
     | some v => .value v
     | Option.none =>
       match getClass? m ci with
       | Option.none => .dangling
       | some c =>
         if c.methods.toList.contains attr then .boundMethod else .missing)
  | some _ =>
    .refuse "attribute access on a dict/list/generator value is outside the tier (their methods are called, not referenced; docs/memory-model.md)"
  | Option.none => .dangling

/-- The attribute-READ outcome (fuel-free: reads decide immediately) —
the `Run`-typed rendering of `attrReadPlan`, factored out so meta-proofs
(`worldInv`) speak about one named application. -/
def attrReadResult (m : Module) (st : FrameState) (a : Addr)
    (attr : String) : Run FrameState RVal :=
  match attrReadPlan m st.world.heap a attr with
  | .value v => .ok st v
  | .boundMethod =>
    .unsupported s!"referencing bound method '.{attr}' as a value is outside the H3 tier (methods are called, not passed)"
  | .missing => .exn st .attributeError
  | .refuse msg => .unsupported msg
  | .dangling => .unsupported danglingMsg

/-- Every decided `.ok` of an attribute read carries the receiver's own
frame state (reads never move the world). -/
theorem attrReadResult_ok {m : Module} {st : FrameState} {a : Addr}
    {attr : String} {s' : FrameState} {v : RVal}
    (h : attrReadResult m st a attr = .ok s' v) : s' = st := by
  unfold attrReadResult at h
  split at h <;> cases h <;> rfl

/-- The decision of an attribute CALL (`x.attr(…)`) on a heap receiver —
same pure-scrutinee discipline as `attrReadPlan`. The plan is decided
BEFORE argument evaluation (CPython: receiver and attribute lookup
precede the arguments — a missing attribute raises before any argument
runs). -/
inductive AttrPlan where
  | instMethod (qname : String) -- class method: `callIn` with self bound
  | instAttrValue               -- data attribute in call position (loud)
  | attrMissing                 -- faithful AttributeError (pre-args)
  | dictGet | listAppend | listPop
  | refuse (msg : String)
  | dangling
deriving Repr, Inhabited, BEq

/-- Resolve `x.attr(…)` against the heap: instances dispatch through
their CLASS (any attr — user methods; instance data attributes in call
position are loud; missing is the faithful pre-args `AttributeError`);
dicts admit `.get`, lists `.append`/`.pop` (the builtin method tier). -/
def attrCallPlan (m : Module) (h : Heap) (a : Addr) (attr : String) :
    AttrPlan :=
  match Heap.get? h a with
  | some (.instance ci attrs) =>
    (match Env.lookup attrs.toList attr with
     | some _ => .instAttrValue
     | Option.none =>
       match getClass? m ci with
       | Option.none => .dangling
       | some c =>
         if c.methods.toList.contains attr then
           .instMethod (c.name ++ "." ++ attr)
         else .attrMissing)
  | some (.dict _ _) =>
    if attr == "get" then .dictGet
    else .refuse s!"method call '.{attr}' on a dict is outside the tier (dict '.get' only; docs/memory-model.md)"
  | some (.list _) =>
    if attr == "append" then .listAppend
    else if attr == "pop" then .listPop
    else .refuse s!"method call '.{attr}' on a list is outside the tier (list '.append'/'.pop' only; docs/memory-model.md)"
  | some (.generator ..) =>
    -- `send`/`throw`/`close` are REAL generator methods with
    -- resumption/finalization semantics the tier does not model, and
    -- guessing which other names exist would be silently wrong: loud,
    -- never a fake `AttributeError`
    .refuse s!"method call '.{attr}' on a generator is outside the tier (send/throw/close and finalization are deliberately out; docs/memory-model.md §generator semantics)"
  | some (.closure ..) =>
    .refuse s!"method call '.{attr}' on a function object is outside the tier (docs/memory-model.md §nested defs and closures)"
  | Option.none => .dangling

/-! ## The namedtuple table (H3+, docs/memory-model.md §class semantics —
the recorded VALUE-like decision, implemented)

`X = namedtuple("T", "f1 f2")` under the benign import is recognized at
ingestion into `Module.namedtuples` (the recognized assign leaves
`topLevel` as `pass`, so G1 neither binds nor poisons `X`). A constructor
call builds an IMMEDIATE `RVal.ntuple` value — no allocation, no heap
identity; field access is tuple indexing by declared position; equality,
hashing, iteration, unpacking, `len`, and subscripting are the value-tuple
semantics (arms above). `_replace`/`_asdict`/`_make`/`_fields` and the
tuple methods `count`/`index` EXIST in CPython — loud, never a fake
`AttributeError`; an unknown non-protocol attribute IS the faithful
`AttributeError`. -/

/-- Scan for the LAST namedtuple with this bound name (the `findClassAux`
discipline — last binding wins; ingestion refuses duplicate binds, so the
arm matters only for hand-built modules). List-structural. -/
def findNamedTupleAux : List NamedTupleDefn → String → Option NamedTupleDefn
  | [], _ => Option.none
  | nt :: rest, name =>
    match findNamedTupleAux rest name with
    | some r => some r
    | Option.none => if nt.name == name then some nt else Option.none

/-- Resolve a module-level name to its namedtuple class (constructor
resolution; also the loud name-as-value and collision guards). -/
def findNamedTuple (m : Module) (name : String) : Option NamedTupleDefn :=
  findNamedTupleAux m.namedtuples.toList name

/-- Position of a field name in the declaration order (list-structural,
kernel-reducible — the `Array.idxOf` USize loop would break `#py_check`). -/
def fieldIndex : List String → String → Option Nat
  | [], _ => Option.none
  | f :: fs, attr =>
    if f == attr then some 0 else (fieldIndex fs attr).map (· + 1)

/-- Non-field attributes that EXIST on every CPython namedtuple (the
namedtuple protocol plus the tuple methods): referencing or calling them
is out of tier — loud, never a fake `AttributeError`. -/
def ntupleProtoName (attr : String) : Bool :=
  attr == "_replace" || attr == "_asdict" || attr == "_make" ||
  attr == "_fields" || attr == "_field_defaults" ||
  attr == "count" || attr == "index"

/-- Is `attr` a METHOD of the namedtuple SUBCLASS the value's `tname`
names (`class Position(namedtuple(…))`, H5)? The value carries the
SUBCLASS name (construction uses the class name, not the typename), so
`findClass`-by-`tname` with the `ntBase` guard is the dispatch: a PLAIN
namedtuple whose TYPENAME merely coincides with an unrelated `ntBase`
class also answers `true` — the consumers are LOUD refusals, never
decided values, so a coincidence over-refuses and is sound (recorded;
the method-CALL tier must resolve identity properly). -/
def ntupleMethodName (m : Module) (tname attr : String) : Bool :=
  match findClass m tname with
  | some (_, c) => c.ntBase.isSome && c.methods.toList.contains attr
  | Option.none => false

/-- Attribute READ on a namedtuple value: a declared field desugars to
tuple indexing (the VALUE-like decision); a SUBCLASS method name is a
bound-method value — loud (methods are called, not passed; H5); the
namedtuple/tuple protocol names and dunders exist in CPython — loud;
anything else is the faithful `AttributeError`. The size guard is
defensive (constructor calls always build `fields.size` elements; a
hand-built mismatch reports loudly). -/
def ntupleAttr (m : Module) (tname : String) (fields : Array String)
    (xs : Array RVal) (attr : String) : Res RVal :=
  -- CPython MRO: SUBCLASS methods shadow the anonymous base's field
  -- properties — the method check comes FIRST
  if ntupleMethodName m tname attr then
    .unsupported s!"referencing bound method '.{attr}' of a namedtuple subclass as a value is outside the tier (methods are called, not passed)"
  else
    match fieldIndex fields.toList attr with
    | some i =>
      if i < xs.size then .ok (xs.getD i .none)
      else .unsupported
        "internal: namedtuple field/value arity mismatch (unconstructible through the interpreter — report this)"
    | Option.none =>
      if ntupleProtoName attr || dunderShaped attr then
        .unsupported s!"namedtuple attribute '.{attr}' is outside the tier (field access only; '_replace'/'_asdict'/'count'/… are loud — docs/memory-model.md §class semantics)"
      else .exn .attributeError

/-- The decision of a method CALL on a namedtuple VALUE (H5): the
subclass methods first (identity — the ingestion census refuses
plain-candidate typenames colliding with `ntBase` class names, so in a
recognized module the value's `tname` names exactly its defining class;
hand-built modules keep the loud-only `ntupleMethodName` caveat), then a
FIELD in call position (CPython calls the field value — loud), then the
protocol/dunders (exist — loud), then the faithful pre-args
`AttributeError`. Reuses `AttrPlan` (the heap dispatch's vocabulary);
decided BEFORE argument evaluation, CPython order. -/
def ntupleCallPlan (m : Module) (tname : String) (fields : Array String)
    (attr : String) : AttrPlan :=
  if ntupleMethodName m tname attr then .instMethod (tname ++ "." ++ attr)
  else if (fieldIndex fields.toList attr).isSome then
    .refuse s!"calling field '.{attr}' of a namedtuple (the field value in call position) is outside the tier"
  else if ntupleProtoName attr || dunderShaped attr then
    .refuse s!"namedtuple method '.{attr}' is outside the tier ('_replace'/'_asdict'/'count'/… are loud — docs/memory-model.md §class semantics)"
  else .attrMissing

/-! ## Module-level constants (globals, G1 — world-init since H1-proper)

CPython executes a module's top-level statements once, at import time, in
source order; function bodies then resolve non-local names against the
resulting module globals. The G1 tier admits the *constant* fragment of
that: top-level `NAME = <expr>` and `N1, N2, … = <expr>` bindings whose
right-hand side evaluates **call-free** (constants, earlier globals,
arithmetic, list/tuple/DICT literals, subscript reads) —
`MATE_LOWER = piece["K"] - 10 * piece["Q"]`, sunfish's `piece`/`pst`
tables, `A1, H1, A8, H8 = 91, 98, 21, 28`.

Since H1-proper the pass is HEAP-THREADING: dict literals allocate into
the module-init heap, the accumulator stores runtime values (`RVal`,
possibly refs into that heap), and `initWorld` carries both into every
public call's fresh world (docs/memory-model.md §module initialization).
Name resolution stays on the STATIC table (`moduleGlobals`): bindings are
immutable in tier (no `global` statement), so a static read of a
module-global returns the same value — the same `.ref` — as a
world-globals read would, while MUTATIONS of the referenced dict live in
the threaded world's heap: shared across nested calls within one public
call, fresh across two (regression case 15). `World.globals` is
initialized for observation and for the future `global`-statement tier,
which must switch reads to it; until then the interpreter never reads it
(recorded invariant).

Address stability: allocation appends and mutation preserves addresses,
so the accumulator's refs (into the init heap) stay valid in every world
that EXTENDS it — which every reachable world does.

Honesty discipline (loud, never wrong):
* a top-level binding whose RHS is out of tier binds its name to `none` —
  function-body references to it are `unsupported`, never a fake value
  and never a fake `NameError`; a failed RHS also discards its partial
  allocations (no refs escape a refusal);
* an out-of-tier top-level statement (`for`, `if`, an unwhitelisted
  `import`, a subscript-target assignment, …) POISONS the names it may
  have changed rather than everything after it: the names it BINDS
  (`Stmt.g1Binds`, nested scopes included) and the primaries it STORES
  into (`Stmt.g1Stores` — `pst[k] = …` poisons `pst`). Poisoning is
  ordinary rebinding to `none` in the accumulator, so a read refuses
  loudly and a later RHS that reads the name fails with it. A statement
  whose binding set is UNKNOWN (`g1Binds = none`) poisons every name
  bound so far and marks the module UNANALYSABLE;
* the two facts are INDEPENDENT and both are needed. *Poisoned* is
  per-name and answers "is this value trustworthy"; *analysable* is
  per-module and answers "could CPython have bound a name we never
  saw". Only a module in which every top-level statement's binding set
  was determined may report a missing name as a faithful `NameError` —
  everywhere else the miss is `unsupported`. (`isModuleDunder` is the
  standing exception: `__name__`/`__doc__`/… are bound by the import
  machinery, not by a statement, so a miss on one is never a
  `NameError`.)
* module init is evaluated at the fixed fuel `globalFuel` — independent of
  the caller's fuel, so results never vary across call sites and fuel
  monotonicity is untouched. A hypothetical constant needing deeper
  evaluation times out into the `none` (out-of-tier) marking, loudly.

RECORDED GAP (owner-visible, PRE-EXISTING and now more exposed — see
docs/backlog.md): the poisoning above is syntactic, so it does not see a
mutation performed by CODE THE STATEMENT CALLS. A top-level `foo()` whose
body runs `tbl["k"] = 1` mutates a module table that stays clean here,
and an alias (`y = tbl` in a callee, then `y["k"] = 1`) escapes the store
scan the same way. This hazard is not introduced by the dirty-name pass —
the old single `complete` flag never guarded mutation either, only later
BINDINGS — but the pass resolves more names, so more of them ride on it.
Closing it wants two named pieces, both designed and neither built: G1 is
IMPORT semantics, so an `if __name__ == "__main__":` guard is statically
dead and need not be analysed at all; and a purity whitelist for the
calls that remain (`dict`/`sum`/`tuple`/`range`, namedtuple construction)
would let any other call poison every ref-carrying name soundly. -/

/-- Fixed evaluation fuel for module-level right-hand sides. -/
def globalFuel : Nat := 512

mutual

/-- Call-free expression evaluator for module-level right-hand sides,
heap-threading (dict literals allocate). `gs` is the runtime globals
resolved so far (source order). Everything callable or effectful is out
of tier here — including calls themselves, because globals are resolved
from inside the interpreter and module init must not re-enter it. -/
def evalGlobalExpr (h : Heap) (gs : REnv) (fuel : Nat) (e : Expr) :
    Res (Heap × RVal) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match e with
    | .constant c _ => .ok (h, Const.toRVal c)
    | .name id _ =>
      match Env.lookup gs id with
      | some v => .ok (h, v)
      | Option.none => .unsupported s!"module-level reference '{id}' is outside the G1 tier"
    | .binOp l op r _ => do
        let (h, a) ← evalGlobalExpr h gs fuel l
        let (h, b) ← evalGlobalExpr h gs fuel r
        let v ← evalBinOp op a b
        return (h, v)
    | .unaryOp op operand _ => do
        let (h, v) ← evalGlobalExpr h gs fuel operand
        let r ← evalUnaryOpH h op v
        return (h, r)
    | .list elts _ => do
        -- H2: module-level list displays allocate into the init heap
        -- (module tables — shared across nested calls within one public
        -- call, fresh across two; regression case 15's list analog).
        let (h, vs) ← evalGlobalExprs h gs fuel elts.toList
        return (h.push (.list vs.toArray), .ref h.size)
    | .tuple elts _ => do
        let (h, vs) ← evalGlobalExprs h gs fuel elts.toList
        return (h, .tuple vs.toArray)
    | .subscript v idx _ => do
        let (h, c) ← evalGlobalExpr h gs fuel v
        let (h, i) ← evalGlobalExpr h gs fuel idx
        let r ← indexValH h c i
        return (h, r)
    | .dict keys values _ => do
        let (h, items) ← evalGlobalDictItems h gs fuel keys.toList values.toList
        let entries ← dictBuild h [] items
        return (h.push (.dict entries.toArray 0), .ref h.size)
    | e => .unsupported s!"module-level expression '{e.kindName}' is outside the G1 tier"

/-- List version of `evalGlobalExpr` (left to right, each once). -/
def evalGlobalExprs (h : Heap) (gs : REnv) (fuel : Nat) (es : List Expr) :
    Res (Heap × List RVal) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match es with
    | [] => .ok (h, [])
    | e :: rest => do
        let (h, v) ← evalGlobalExpr h gs fuel e
        let (h, vs) ← evalGlobalExprs h gs fuel rest
        return (h, v :: vs)

/-- Dict-literal items at module level (`k₁, v₁, k₂, v₂, …` — the
`evalDictItems` twin at the G1 signature). -/
def evalGlobalDictItems (h : Heap) (gs : REnv) (fuel : Nat)
    (keys values : List Expr) : Res (Heap × List (RVal × RVal)) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match keys, values with
    | [], [] => .ok (h, [])
    | k :: ks, v :: vs => do
        let (h, kv) ← evalGlobalExpr h gs fuel k
        let (h, vv) ← evalGlobalExpr h gs fuel v
        let (h, rest) ← evalGlobalDictItems h gs fuel ks vs
        return (h, (kv, vv) :: rest)
    | _, _ => .unsupported "Dict with mismatched keys/values"

end

/-- The globals accumulator: bindings in reverse source order (`lookupG`
takes the first match, so the LATEST binding wins, as in CPython) — `none`
marks a name bound at module level to an out-of-tier value. Stores RUNTIME
values since H1-proper (refs point into the module-init heap). -/
abbrev GlobalsAcc := List (String × Option RVal)

/-- First-match lookup in the accumulator. -/
def lookupG : GlobalsAcc → String → Option (Option RVal)
  | [], _ => Option.none
  | (k, v) :: rest, id => if k == id then some v else lookupG rest id

/-- The resolved (in-tier) globals as a runtime env, keeping only the
LATEST binding of each name (`seen` accumulates the names already
decided). Dropping the out-of-tier markers alone would be WRONG: a
poisoned rebinding (`pst = {…}` then the loop that mutates `pst`) sits in
FRONT of the value it invalidates, so a filter that removed only the
marker would resurface the stale value — `lookupG`'s first-match rule
already shadows it, and this must agree. -/
def resolvedGAux (seen : List String) : GlobalsAcc → REnv
  | [] => []
  | (k, v) :: rest =>
    if seen.contains k then resolvedGAux seen rest
    else
      match v with
      | some x => (k, x) :: resolvedGAux (k :: seen) rest
      | Option.none => resolvedGAux (k :: seen) rest

/-- The resolved (in-tier) globals as a runtime env — see `resolvedGAux`. -/
def resolvedG (acc : GlobalsAcc) : REnv := resolvedGAux [] acc

/-- All-names view of a tuple target's elements. -/
def targetNamesG : List Expr → Option (List String)
  | [] => some []
  | .name id _ :: rest => (targetNamesG rest).map (id :: ·)
  | _ => Option.none

/-! ### What an out-of-tier top-level statement may have changed

Two syntactic scans over the statement's whole subtree. `g1Binds` is the
set of names it can REBIND (`none` = the shape is unanalysable, so the set
is unknown); `g1Stores` is the set of module-level primaries it can MUTATE
through a subscript/attribute target. Their union is what `globalsStep`
poisons. Both are overapproximations of CPython — poisoning a name that
was never touched only costs a loud refusal. -/

/-- Names an assignment-like TARGET binds; `none` = unanalysable shape.
A subscript/attribute target binds no name (it MUTATES — `g1Stores`). -/
def targetBindsG : Expr → Option (List String)
  | .name id _ => some [id]
  | .tuple es _ | .list es _ => targetNamesG es.toList
  | .subscript .. => some []
  | .attribute .. => some []
  | _ => Option.none

/-- Elementwise `targetBindsG` over an assignment's target list. -/
def targetBindsListG : List Expr → Option (List String)
  | [] => some []
  | t :: rest =>
    match targetBindsG t, targetBindsListG rest with
    | some a, some b => some (a ++ b)
    | _, _ => Option.none

/-- The PRIMARY name a store target reaches through (`a.b[k]` → `a`);
`[]` when the chain does not bottom out in a name. -/
def Expr.g1Primary : Expr → List String
  | .name id _ => [id]
  | .subscript v _ _ => v.g1Primary
  | .attribute v _ _ => v.g1Primary
  | _ => []

mutual
  /-- Primaries a single assignment TARGET stores into (a plain-name target
  rebinds instead — `targetBindsG` covers that). -/
  def Expr.g1TargetStores : Expr → List String
    | .name _ _ => []
    | .subscript v _ _ => v.g1Primary
    | .attribute v _ _ => v.g1Primary
    | .tuple es _ | .list es _ => Expr.g1TargetStoresList es.toList
    | _ => []

  /-- Elementwise `Expr.g1TargetStores`. -/
  def Expr.g1TargetStoresList : List Expr → List String
    | [] => []
    | e :: es => e.g1TargetStores ++ Expr.g1TargetStoresList es
end

mutual
  /-- Module-level primaries the statement's subtree STORES into. -/
  def Stmt.g1Stores : Stmt → List String
    | .assign tgts _ _ => Expr.g1TargetStoresList tgts.toList
    | .augAssign t _ _ _ => t.g1TargetStores
    | .whileLoop _ b o _ | .ifStmt _ b o _ =>
      Stmt.g1StoresList b.toList ++ Stmt.g1StoresList o.toList
    | .forStmt t _ b o _ =>
      t.g1TargetStores ++ Stmt.g1StoresList b.toList ++ Stmt.g1StoresList o.toList
    | _ => []

  /-- Elementwise `Stmt.g1Stores`. -/
  def Stmt.g1StoresList : List Stmt → List String
    | [] => []
    | s :: ss => s.g1Stores ++ Stmt.g1StoresList ss
end

mutual
  /-- Names the statement's subtree can REBIND at module level; `none` =
  the shape is unanalysable, so the set is unknown. Imports are decided by
  the exact-text whitelist (`benignImportBinds`, Ast.lean) — anything else
  is unknown, because an import runs arbitrary code. -/
  def Stmt.g1Binds : Stmt → Option (List String)
    | .assign tgts _ _ => targetBindsListG tgts.toList
    | .augAssign t _ _ _ => targetBindsG t
    -- H7: a nested def binds its NAME (its body is its own scope)
    | .defStmt name _ _ _ _ _ _ _ _ => some [name]
    | .forStmt t _ b o _ =>
      match targetBindsG t, Stmt.g1BindsList b.toList, Stmt.g1BindsList o.toList with
      | some a, some c, some d => some (a ++ c ++ d)
      | _, _, _ => Option.none
    | .whileLoop _ b o _ | .ifStmt _ b o _ =>
      match Stmt.g1BindsList b.toList, Stmt.g1BindsList o.toList with
      | some c, some d => some (c ++ d)
      | _, _ => Option.none
    | .ret .. | .exprStmt .. | .yieldStmt .. => some []
    | .pass _ | .brk _ | .cont _ => some []
    | .unsupported "Import" text _ | .unsupported "ImportFrom" text _ =>
      match benignImportBinds text with
      -- a MODELLED name (`count` is `itertools.count`) must stay
      -- unbound here, so resolution falls through to the model's
      -- builtin; an unmodelled one is bound POISONED below
      | some (n, modelled) => some (if modelled then [] else [n])
      | Option.none => Option.none
    | .unsupported .. => Option.none

  /-- Elementwise `Stmt.g1Binds`. -/
  def Stmt.g1BindsList : List Stmt → Option (List String)
    | [] => some []
    | s :: ss =>
      match s.g1Binds, Stmt.g1BindsList ss with
      | some a, some b => some (a ++ b)
      | _, _ => Option.none
end

/-- Everything an out-of-tier top-level statement may have changed;
`none` = unknown (it poisons the whole accumulator). -/
def Stmt.g1Dirty (s : Stmt) : Option (List String) :=
  (s.g1Binds).map (· ++ s.g1Stores)

/-- An out-of-tier top-level statement's effect on the globals: POISON
every name it may have changed (`Stmt.g1Dirty` — binds ∪ store
primaries), which is an ordinary rebinding to `none`, so `lookupG` refuses
the read and `resolvedG` shadows the stale value it replaces.

`g1Dirty = none` — the statement's binding set is UNKNOWN — poisons every
name bound so far and clears `analysable`, today's blunt behaviour, which
is the only state where a missing name may not be reported as a
`NameError`. Later bindings still evaluate: a constant RHS reads nothing,
so nothing an earlier statement did can make it stale. -/
def globalsDirty (h : Heap) (acc : GlobalsAcc) (analysable : Bool)
    (s : Stmt) : Heap × GlobalsAcc × Bool :=
  match s.g1Dirty with
  | some ns => (h, ns.map (fun n => (n, (Option.none : Option RVal))) ++ acc, analysable)
  | Option.none => (h, acc.map (fun p => (p.1, (Option.none : Option RVal))), false)

/-- One module-level statement's effect on the init heap and the globals.
`(h, acc, analysable)`: `analysable = false` once a statement's binding
set could not be determined. A failed RHS binds its names out-of-tier AND
discards its partial allocations (the original heap rides through — no
refs escape a refusal); everything out of tier goes to `globalsDirty`. -/
def globalsStep (h : Heap) (acc : GlobalsAcc) (analysable : Bool)
    (s : Stmt) : Heap × GlobalsAcc × Bool :=
  match s with
  | .assign tgts rhs _ =>
    match tgts.toList with
    | [.name id _] =>
      match evalGlobalExpr h (resolvedG acc) globalFuel rhs with
      | .ok (h', v) => (h', (id, some v) :: acc, analysable)
      | _ => (h, (id, Option.none) :: acc, analysable)
    | [.tuple es _] =>
      match targetNamesG es.toList with
      | some ids =>
        match evalGlobalExpr h (resolvedG acc) globalFuel rhs with
        | .ok (h', .tuple vs) =>
          if ids.length == vs.size then
            (h', (ids.zip (vs.toList.map some)).reverse ++ acc, analysable)
          else (h, ids.map (·, Option.none) ++ acc, analysable)
        | .ok (h', .listV vs) =>
          if ids.length == vs.size then
            (h', (ids.zip (vs.toList.map some)).reverse ++ acc, analysable)
          else (h, ids.map (·, Option.none) ++ acc, analysable)
        | _ => (h, ids.map (·, Option.none) ++ acc, analysable)
      | Option.none => globalsDirty h acc analysable s
    | _ => globalsDirty h acc analysable s
  | .pass _ => (h, acc, analysable)
  -- a bare expression binds nothing; `globalsDirty` records that it can
  -- still STORE (and the recorded call-mutation gap in the section
  -- comment above)
  | s => globalsDirty h acc analysable s

/-- Fold `globalsStep` over the top-level statements (source order). -/
def globalsFold (h : Heap) (acc : GlobalsAcc) (analysable : Bool) :
    List Stmt → Heap × GlobalsAcc × Bool
  | [] => (h, acc, analysable)
  | s :: rest =>
    match globalsStep h acc analysable s with
    | (h', acc', analysable') => globalsFold h' acc' analysable' rest

/-- The whole module-init result: the init heap, the accumulator, and the
ANALYSABLE flag — a pure function of the module (fixed `globalFuel`). -/
def moduleInit (m : Module) : Heap × GlobalsAcc × Bool :=
  globalsFold #[] [] true m.topLevel.toList

/-- The module's constant globals: `(bindings, analysable)` — the static
name-resolution table (see the section comment for why static reads are
faithful, and for what the two independent facts mean). -/
def moduleGlobals (m : Module) : GlobalsAcc × Bool :=
  (moduleInit m).2

/-- Does a call supplying `n` positional arguments fit `params`? Python's
rule with defaults (F1): at most one argument per parameter, and every
parameter beyond the supplied ones carries a default —
`nparams - ndefaults ≤ n ≤ nparams`. For a default-free function this is
exactly the old `n = params.size`. Violations raise the canonical arity
`TypeError` (`callIn`); CPython's message wording differs per case
(`missing … required` vs `takes … but … were given`) but the harness
compares exception *class names*, so one canonical message serves both. -/
def arityOk (params : Array Param) (n : Nat) : Bool :=
  n ≤ params.size && (params.toList.drop n).all fun p => p.default.isSome

/-- Exact arity always fits: with every parameter supplied there is nothing
left to default — the old `n = params.size` rule embeds into `arityOk`
(what lets the exact-arity bridge theorems keep their statements). -/
theorem arityOk_full (params : Array Param) : arityOk params params.size = true := by
  simp [arityOk, ← Array.length_toList, List.drop_length]

/-- Bindings for parameters left unsupplied by a call: each takes its
literal default. A defaultless parameter contributes no binding — dead code
behind `arityOk`, which refuses such calls before any body runs. -/
def defaultBindings : List Param → Env
  | [] => []
  | p :: ps =>
    match p.default with
    | some c => (p.arg, Const.toRVal c) :: defaultBindings ps
    | Option.none => defaultBindings ps

/-- Fresh local environment of a call: parameters bound to arguments
pairwise, parameters beyond the supplied arguments bound to their literal
defaults (F1; `arityOk` has already ensured those defaults exist).

Def-time-vs-call-time (normative reasoning): Python evaluates default
expressions ONCE, at `def` time, in the defining scope. The tier admits
only LITERAL defaults (int/bool/str/None — `Const`), for which filling at
call time is observationally identical: a literal's value cannot be
mutated, rebound, or depend on evaluation order or scope. The classic
mutable-default footgun (`def f(x=[])` sharing one list across calls) is
unrepresentable by construction — `[]` is not a literal `Const`, so the
extractor keeps such functions at `argsOk = false`. -/
def mkCallEnv (params : Array Param) (args : Array RVal) : Env :=
  (params.toList.map Param.arg).zip args.toList
    ++ defaultBindings (params.toList.drop args.size)

/-- First keyword name bound twice, if any. CPython rejects a repeated
literal keyword (`f(a=1, a=2)`) at COMPILE time, so ingestion never ships
one — the guard keeps hand-built modules loud, never guessing an error
class CPython would not have reached. -/
def kwFindDup : List (String × RVal) → Option String
  | [] => Option.none
  | (k, _) :: rest => if rest.any (·.1 == k) then some k else kwFindDup rest

/-- Fill the parameter slots AFTER the positional prefix (H6 keyword
merge): the keyword's value if given, else the literal default — a slot
with neither is CPython's faithful missing-argument `TypeError`.
Structural recursion (kernel-reducible, the `sortInts` discipline). -/
def fillKwSlots (fname : String) (kws : List (String × RVal)) :
    List Param → Res (List RVal)
  | [] => .ok []
  | p :: ps =>
    match kws.find? (·.1 == p.arg) with
    | some (_, v) => do return v :: (← fillKwSlots fname kws ps)
    | Option.none =>
      match p.default with
      | some c => do return Const.toRVal c :: (← fillKwSlots fname kws ps)
      | Option.none =>
        .exn (.typeError
          s!"{fname}() missing 1 required positional argument: '{p.arg}'")

/-- H6 keyword merge (docs/memory-model.md §call-site keyword arguments):
resolve already-evaluated positional + keyword arguments against `params`
into ONE complete positional array, so `callIn`'s covenant signature never
changes. Faithful `TypeError`s: too many positionals, an unexpected
keyword, multiple values for one parameter, a missing required parameter
(CPython's message WORDING differs per case; the harness compares error
classes). Callers must have checked `argsOk` first — on a parameter list
the model does not fully understand, the loud refusal wins, never a
binding `TypeError` computed from an untrusted table. -/
def mergeKwArgs (fname : String) (params : Array Param)
    (pos : List RVal) (kws : List (String × RVal)) : Res (Array RVal) :=
  let names := params.toList.map Param.arg
  match kwFindDup kws with
  | some k =>
    .unsupported s!"duplicate keyword argument '{k}' (unreachable through ingestion — CPython rejects it at compile time)"
  | Option.none =>
  if pos.length > params.size then
    .exn (.typeError
      s!"{fname}() takes {params.size} positional arguments but {pos.length} were given")
  else match kws.find? (fun kv => !names.contains kv.1) with
  | some (k, _) =>
    .exn (.typeError s!"{fname}() got an unexpected keyword argument '{k}'")
  | Option.none =>
  match kws.find? (fun kv => (names.take pos.length).contains kv.1) with
  | some (k, _) =>
    .exn (.typeError s!"{fname}() got multiple values for argument '{k}'")
  | Option.none => do
    return (pos ++ (← fillKwSlots fname kws (params.toList.drop pos.length))).toArray

/-- `enumerate`'s optional `start` argument: `none` = the argument list
is not an in-tier `enumerate(x)` / `enumerate(x, i)` shape. -/
def enumStart : List RVal → Option Int
  | [] => some 0
  | [v] => asInt v
  | _ => Option.none

/-- The initial frame of `enumerate(v, i)`: value sequences snapshot
(all immutable in tier), a heap LIST gets the live cursor, and every
other receiver is the faithful `TypeError` — except a generator, whose
enumeration would need a second stepper inside this one (recorded gap,
docs/backlog.md). -/
def enumFrame (h : Heap) (i : Int) : RVal → Res GenFrame
  | .str s => .ok (.enumSeq i (strCharVals s))
  | .tuple xs => .ok (.enumSeq i xs.toList)
  | .listV xs => .ok (.enumSeq i xs.toList)
  | .ntuple _ _ xs => .ok (.enumSeq i xs.toList)
  | .ref a =>
    (match Heap.get? h a with
     | some (.list _) => .ok (.enumList i a 0)
     | some (.dict _ _) =>
         .unsupported "enumerate() over a dict iterates its keys — outside the tier (live dict iteration; docs/memory-model.md)"
     | some (.generator ..) =>
         .unsupported "enumerate() over a generator is outside the tier (it would need a stepper inside the stepper; docs/backlog.md)"
     | some (.instance _ _) => .exn (.typeError "'object' object is not iterable")
     | some (.closure ..) => .exn (.typeError "'function' object is not iterable")
     | Option.none => .unsupported danglingMsg)
  | v => .exn (.typeError s!"'{v.typeName}' object is not iterable")

/-- `itertools.count()` / `count(start)` / `count(start, step)`. -/
def countArgs : List RVal → Option (Int × Int)
  | [] => some (0, 1)
  | [s] => (asInt s).map (fun a => (a, 1))
  | [s, d] =>
    (match asInt s, asInt d with
     | some a, some b => some (a, b)
     | _, _ => Option.none)
  | _ => Option.none

/-! ## Generator continuations (H4, docs/memory-model.md §generator
semantics)

Two PURE unwinders over the defunctionalized continuation. They are what
makes `break`/`continue` inside a suspended generator ordinary data
manipulation instead of a second control-flow mechanism: `break` pops
frames up to AND INCLUDING the nearest loop frame (the frames below are
exactly "after the loop"), `continue` pops up to BUT NOT including it (so
re-entering the loop frame advances the cursor — the loop frames carry no
"rest of block" precisely so these two agree). `none` means the flow
escaped every loop, which `callIn` reports as `'break' outside loop` —
unreachable through a well-formed body, loud if ever reached. -/

/-- `break`: drop the pending blocks and the enclosing loop frame. -/
def genBreak : GenCont → Option GenCont
  | [] => Option.none
  | .block _ :: k => genBreak k
  | .forSeq .. :: k => some k
  | .forList .. :: k => some k
  | .forGen .. :: k => some k
  | .whileLoop .. :: k => some k
  -- a builtin-iterator frame is never a LOOP frame: it is the body of a
  -- generator object, so `break`/`continue` can never reach one (they
  -- unwind inside a body, and these frames have no body). Loud, not a
  -- silent pop.
  | .enumSeq .. :: _ | .enumList .. :: _ | .countFrom .. :: _ => Option.none

/-- `continue`: drop the pending blocks, KEEP the enclosing loop frame
(re-entering it takes the next element / re-tests). -/
def genContinue : GenCont → Option GenCont
  | [] => Option.none
  | .block _ :: k => genContinue k
  | k@(.forSeq ..  :: _) => some k
  | k@(.forList .. :: _) => some k
  | k@(.forGen ..  :: _) => some k
  | k@(.whileLoop .. :: _) => some k
  | .enumSeq .. :: _ | .enumList .. :: _ | .countFrom .. :: _ => Option.none

mutual
  /-- Does this statement contain a `yield` in its own scope? The
  continuation walker delegates every yield-FREE statement to the
  ordinary `execStmt` (one source of truth for their semantics) and only
  opens the control constructs that can suspend. Structural, kernel
  computable. -/
  def Stmt.hasYield : Stmt → Bool
    | .yieldStmt .. => true
    | .whileLoop _ body orelse _ =>
        Stmt.hasYieldList body.toList || Stmt.hasYieldList orelse.toList
    | .forStmt _ _ body orelse _ =>
        Stmt.hasYieldList body.toList || Stmt.hasYieldList orelse.toList
    | .ifStmt _ body orelse _ =>
        Stmt.hasYieldList body.toList || Stmt.hasYieldList orelse.toList
    | _ => false

  /-- Elementwise `Stmt.hasYield`. -/
  def Stmt.hasYieldList : List Stmt → Bool
    | [] => false
    | s :: ss => s.hasYield || Stmt.hasYieldList ss
end

/-- What the continuation walker does with the next statement of a
generator body — the H3 free-scrutinee discipline (`attrCallPlan`,
`strCallPlan`), and here it is not merely convenient but REQUIRED: with
the statement match written inline, Lean's equation compiler splits
`execGen`'s block arm per `Stmt` constructor, so its equations never fire
at a symbolic statement and `fuelMono`/`worldInv` cannot step the walker
at all. Forking on this pure plan restores one equation. -/
inductive GenPlan where
  /-- Yield-free: run it through the ordinary `execStmt` (one source of
  truth for its semantics) and route the resulting flow. -/
  | delegate
  | yieldHere (value : Expr)
  | branch (test : Expr) (body orelse : List Stmt)
  | whileHere (test : Expr) (body orelse : List Stmt)
  | forHere (target : Expr) (iter : Expr) (body : List Stmt)
  | refuse (msg : String)
deriving Repr, Inhabited, BEq

/-- Classify the next statement of a generator body (see `GenPlan`). A
`yield` anywhere but statement position is the `send` channel and stays
loud. -/
def genPlan (s : Stmt) : GenPlan :=
  if !s.hasYield then .delegate
  else
    match s with
    | .yieldStmt e _ => .yieldHere e
    | .ifStmt t b o _ => .branch t b.toList o.toList
    | .whileLoop t b o _ => .whileHere t b.toList o.toList
    | .forStmt tg it b o _ =>
      (match o.toList with
       | [] => .forHere tg it b.toList
       | _ :: _ => .refuse "'for … else' is outside the v0 tier")
    | s =>
      .refuse s!"'yield' inside a '{s.kindName}' statement (yield in expression position) is outside the tier"

/-! ## The heap-free fragment (conditional world invariance)

Once dict literals allocate and subscript stores mutate, unconditional
world invariance is FALSE. What survives is the heap-free fragment: an
expression/statement whose every subterm neither allocates nor mutates
returns its input world on `.ok` (`worldInv`, Obs.lean). The predicates
are SYNTACTIC and kernel-computable (list-structural, like `valEq`), so
concrete modules discharge them by `rfl` — which is how pure `CallsTo`
specs lift into the stateful `CallsIn` world (`CallsTo.callsIn_frame`,
Surface.lean).

Soundness rule for every future tier: any construct whose `.ok` outcome
can carry a CHANGED world must be `false` here. Today: dict literals
(allocation) and subscript-target assignment (mutation). Reads (`d[k]`,
`k in d`, `len(d)`, `d.get(k)`, `==`, truthiness) preserve the world; loud
and raising arms are vacuous for `.ok`-invariance. -/

mutual
  /-- Does evaluating this expression provably preserve the world? -/
  def Expr.heapFree : Expr → Bool
    | .constant .. => true
    | .name .. => true
    | .binOp l _ r _ => l.heapFree && r.heapFree
    | .unaryOp _ e _ => e.heapFree
    | .boolOp _ vs _ => Expr.heapFreeList vs.toList
    | .compare l _ cs _ => l.heapFree && Expr.heapFreeList cs.toList
    -- H2 soundness carve-outs: `sorted` ALLOCATES its result when the
    -- argument is a heap list (syntax cannot tell, so every `sorted`
    -- call leaves the fragment — even shadowed ones, conservatively);
    -- method calls beyond `.get` MUTATE (`.append`/`.pop`).
    -- H4 adds `next`: it STEPS a generator (arbitrary body effects), and
    -- syntax cannot tell `next(g)` from a shadowing user `def next`.
    -- H6: a call carrying KEYWORDS leaves the fragment conservatively
    -- (docs/memory-model.md §call-site keyword arguments).
    | .call (.name id _) args kwargs _ _ =>
      kwargs.isEmpty && (id != "sorted") && (id != "next") && (id != "enumerate")
        && (id != "count") && (id != "any") && (id != "all")
        && Expr.heapFreeList args.toList
    | .call (.attribute recv attr _) args kwargs _ _ =>
      kwargs.isEmpty && attr == "get" && recv.heapFree && Expr.heapFreeList args.toList
    | .call f args kwargs _ _ =>
      kwargs.isEmpty && f.heapFree && Expr.heapFreeList args.toList
    | .list .. => false                 -- ALLOCATES (H2)
    | .tuple es _ => Expr.heapFreeList es.toList
    | .subscript v i _ => v.heapFree && i.heapFree
    | .dict .. => false                 -- ALLOCATES
    | .attribute v _ _ => v.heapFree    -- as a bare value: loud, never `.ok`
    | .ifExp t b o _ => t.heapFree && b.heapFree && o.heapFree
    -- H5 strings: slices decide only on strs (pure) — every allocating
    -- receiver (heap lists) refuses loudly, so the node stays in the
    -- fragment
    | .slice v l u st _ => v.heapFree && l.heapFree && u.heapFree && st.heapFree
    | .genExp .. => false               -- ALLOCATES a generator (H4)
    | .unsupported .. => true           -- loud, never decides `.ok`

  /-- Elementwise `Expr.heapFree`. -/
  def Expr.heapFreeList : List Expr → Bool
    | [] => true
    | e :: es => e.heapFree && Expr.heapFreeList es
end

mutual
  /-- Does executing this statement provably preserve the world? -/
  def Stmt.heapFree : Stmt → Bool
    | .defStmt .. => false              -- ALLOCATES a closure (H7)
    | .ret Option.none _ => true
    | .ret (some e) _ => e.heapFree
    | .assign tgts v _ =>
      (match tgts.toList with
       | [.subscript ..] => false       -- MUTATES (`d[k] = v`)
       | [.attribute ..] => false       -- MUTATES (H3 `self.x = v`)
       | _ => true) && v.heapFree
    | .augAssign _ _ v _ => v.heapFree
    | .whileLoop t body orelse _ =>
      t.heapFree && Stmt.heapFreeList body.toList && Stmt.heapFreeList orelse.toList
    | .forStmt _ iter body orelse _ =>
      iter.heapFree && Stmt.heapFreeList body.toList && Stmt.heapFreeList orelse.toList
    | .ifStmt t body orelse _ =>
      t.heapFree && Stmt.heapFreeList body.toList && Stmt.heapFreeList orelse.toList
    | .exprStmt e _ => e.heapFree
    -- `yield` outside a generator body is loud, and inside one it never
    -- runs through `execStmt` at all (the continuation walker owns it)
    | .yieldStmt _ _ => true
    | .pass _ => true
    | .brk _ => true
    | .cont _ => true
    | .unsupported .. => true

  /-- Elementwise `Stmt.heapFree`. -/
  def Stmt.heapFreeList : List Stmt → Bool
    | [] => true
    | s :: ss => s.heapFree && Stmt.heapFreeList ss
end

/-- Function-level heap freedom: its body's. -/
def FunctionDefn.heapFree (f : FunctionDefn) : Bool :=
  Stmt.heapFreeList f.body.toList

/-- Elementwise function heap freedom. -/
def funsHeapFree : List FunctionDefn → Bool
  | [] => true
  | f :: fs => f.heapFree && funsHeapFree fs

mutual
/-- Does the statement subtree contain a GENERATOR nested def? (H7: a
closure's `isGenerator` def allocates the H4 object when called, so the
generator-freedom census must see through function bodies.) -/
def Stmt.hasGenDef : Stmt → Bool
  | .defStmt _ _ _ _ _ ig body _ _ => ig || Stmt.hasGenDefList body.toList
  | .whileLoop _ b o _ | .ifStmt _ b o _ | .forStmt _ _ b o _ =>
      Stmt.hasGenDefList b.toList || Stmt.hasGenDefList o.toList
  | _ => false

/-- Elementwise `Stmt.hasGenDef`. -/
def Stmt.hasGenDefList : List Stmt → Bool
  | [] => false
  | s :: ss => s.hasGenDef || Stmt.hasGenDefList ss
end

/-- Does the function list contain a GENERATOR def — direct, or a nested
generator def in some body (H7)? (H4: calling one ALLOCATES a suspended
frame, and syntax cannot tell a generator call from an ordinary call —
the H3 `classes = #[]` carve-out, again.) -/
def funsAnyGen : List FunctionDefn → Bool
  | [] => false
  | f :: fs => f.isGenerator || Stmt.hasGenDefList f.body.toList || funsAnyGen fs

/-- Has this module NO generator definitions? Then no `Obj.generator` can
exist in any world of any run of it: `callIn` is the only allocator, the
boundary thaw cannot build one, and G1 module init evaluates constants
only. The generator entry points test this and refuse LOUDLY when it
holds, which is what keeps `worldInv` free of a heap-side invariant —
the arm is unreachable, and reaching it would be an interpreter bug, not
a silent wrong answer. -/
def moduleGenFree (m : Module) : Bool :=
  !funsAnyGen m.functions.toList

/-- Module-level heap freedom: every function body (nested calls then stay
inside the fragment), no classes (H3: instantiation ALLOCATES and
syntax cannot tell a class call from a function call, so any class evicts
the whole module from the fragment — conservative, sound; class-using
modules live on `CallsIn`), and no GENERATOR defs (H4: the same argument —
`gen_moves()` allocates a suspended frame). Top-level statements are NOT
constrained — they run only at module init, before any public run begins. -/
def Module.heapFree (m : Module) : Bool :=
  funsHeapFree m.functions.toList && m.classes.toList.isEmpty && moduleGenFree m

/-- The three conjuncts of `Module.heapFree`, projected (H4 made it a
three-way `&&`, so the `Bool.and_eq_true ▸` idiom no longer lines up
positionally — these are the names to cite instead). -/
theorem Module.heapFree_funs {m : Module} (hm : m.heapFree = true) :
    funsHeapFree m.functions.toList = true := by
  simp only [Module.heapFree, Bool.and_eq_true] at hm; exact hm.1.1

@[inherit_doc Module.heapFree_funs]
theorem Module.heapFree_classes {m : Module} (hm : m.heapFree = true) :
    m.classes.toList.isEmpty = true := by
  simp only [Module.heapFree, Bool.and_eq_true] at hm; exact hm.1.2

@[inherit_doc Module.heapFree_funs]
theorem Module.heapFree_genFree {m : Module} (hm : m.heapFree = true) :
    moduleGenFree m = true := by
  simp only [Module.heapFree, Bool.and_eq_true] at hm; exact hm.2

/-- A member of a heap-free function list is heap-free. -/
theorem funsHeapFree_mem {fs : List FunctionDefn} (hm : funsHeapFree fs = true)
    {f : FunctionDefn} (hf : f ∈ fs) : f.heapFree = true := by
  induction fs with
  | nil => cases hf
  | cons g gs ih =>
    simp only [funsHeapFree, Bool.and_eq_true] at hm
    cases hf with
    | head => exact hm.1
    | tail _ h => exact ih hm.2 h

/-- The function `findFunction` resolves in a heap-free module is heap-free
(the extraction step of `worldInv`'s `callIn` case). -/
theorem findFunction_heapFree {m : Module} {fname : String} {f : FunctionDefn}
    (hm : m.heapFree = true) (hf : findFunction m fname = some f) :
    Stmt.heapFreeList f.body.toList = true := by
  have hmem : f ∈ m.functions.toList := by
    unfold findFunction at hf
    rw [Array.findRev?_eq_find?_reverse] at hf
    have h1 : f ∈ m.functions.reverse := Array.mem_of_find?_eq_some hf
    rw [Array.mem_reverse] at h1
    exact Array.mem_def.mp h1
  have hm1 : funsHeapFree m.functions.toList = true := Module.heapFree_funs hm
  exact funsHeapFree_mem hm1 hmem

/-- A member of a generator-free function list is not a generator. -/
theorem funsAnyGen_mem {fs : List FunctionDefn} (hg : funsAnyGen fs = false)
    {f : FunctionDefn} (hf : f ∈ fs) : f.isGenerator = false := by
  induction fs with
  | nil => cases hf
  | cons g gs ih =>
    simp only [funsAnyGen, Bool.or_eq_false_iff] at hg
    cases hf with
    | head => exact hg.1.1
    | tail _ h => exact ih hg.2 h

/-- The function `findFunction` resolves in a heap-free module is NOT a
generator (`Module.heapFree`'s third conjunct) — what keeps `worldInv`'s
generator-CREATION branch (which allocates) vacuous. -/
theorem findFunction_notGen {m : Module} {fname : String} {f : FunctionDefn}
    (hm : m.heapFree = true) (hf : findFunction m fname = some f) :
    f.isGenerator = false := by
  have hmem : f ∈ m.functions.toList := by
    unfold findFunction at hf
    rw [Array.findRev?_eq_find?_reverse] at hf
    have h1 : f ∈ m.functions.reverse := Array.mem_of_find?_eq_some hf
    rw [Array.mem_reverse] at h1
    exact Array.mem_def.mp h1
  have hg : funsAnyGen m.functions.toList = false := by
    have := Module.heapFree_genFree hm
    simpa [moduleGenFree] using this
  exact funsAnyGen_mem hg hmem

/-- A heap-free module has no classes at all (`Module.heapFree`'s second
conjunct), so class-name resolution always misses — what keeps `worldInv`'s
instantiation and method-dispatch branches vacuous. -/
theorem findClass_heapFree {m : Module} (hm : m.heapFree = true)
    (cname : String) : findClass m cname = Option.none := by
  have h2 : m.classes.toList.isEmpty = true := Module.heapFree_classes hm
  unfold findClass
  rw [List.isEmpty_iff.mp h2]
  rfl

/-- A heap-free module resolves no `ClassId` either (see
`findClass_heapFree`). -/
theorem getClass?_heapFree {m : Module} (hm : m.heapFree = true)
    (i : ClassId) : getClass? m i = Option.none := by
  have h2 : m.classes.toList.isEmpty = true := Module.heapFree_classes hm
  unfold getClass?
  rw [List.isEmpty_iff.mp h2]
  cases i <;> rfl

/-- In a heap-free module, `.get`-attribute call dispatch never reaches a
class method or a mutating list arm: the plan is `dictGet` (a heap READ)
or a decided refusal — `worldInv`'s attribute-call case forks on this.
(`attr = "get"` is what the heap-free fragment pins; the two list arms
die on the literal comparisons, the instance method arm on `getClass?`.) -/
theorem attrCallPlan_get_heapFree {m : Module} (hm : m.heapFree = true)
    (h : Heap) (a : Addr) :
    attrCallPlan m h a "get" = .dictGet ∨
    attrCallPlan m h a "get" = .instAttrValue ∨
    attrCallPlan m h a "get" = .dangling ∨
    (∃ msg, attrCallPlan m h a "get" = .refuse msg) := by
  unfold attrCallPlan
  cases Heap.get? h a with
  | none => right; right; left; rfl
  | some o =>
    cases o with
    | dict es ver =>
      rw [if_pos (by decide : ((("get" : String) == "get") = true))]
      left; rfl
    | list xs =>
      rw [if_neg (by decide : ¬ ((("get" : String) == "append") = true)),
          if_neg (by decide : ¬ ((("get" : String) == "pop") = true))]
      right; right; right; exact ⟨_, rfl⟩
    | generator qn lo k st => right; right; right; exact ⟨_, rfl⟩
    | closure nm ps ao lo' hg ig bd cap => right; right; right; exact ⟨_, rfl⟩
    | «instance» ci attrs =>
      cases hv : Env.lookup attrs.toList "get" with
      | some v => simp [hv]
      | none => simp [hv, getClass?_heapFree hm ci]

/-- In a heap-free module the namedtuple call plan never dispatches (no
classes ⇒ no methods): it is a decided refusal or the faithful
`AttributeError` — `worldInv`'s value-receiver branch forks on this. -/
theorem ntupleCallPlan_heapFree {m : Module} (hm : m.heapFree = true)
    (tname : String) (fields : Array String) (attr : String) :
    ntupleCallPlan m tname fields attr = .attrMissing ∨
    (∃ msg, ntupleCallPlan m tname fields attr = .refuse msg) := by
  unfold ntupleCallPlan ntupleMethodName
  rw [findClass_heapFree hm]
  by_cases hf : (fieldIndex fields.toList attr).isSome
  · rw [if_neg (by simp), if_pos hf]; right; exact ⟨_, rfl⟩
  · rw [if_neg (by simp), if_neg hf]
    by_cases hp : (ntupleProtoName attr || dunderShaped attr) = true
    · rw [if_pos hp]; right; exact ⟨_, rfl⟩
    · rw [if_neg hp]; left; rfl

/-! ## The interpreter (mutual block, normative signatures)

Every function matches fuel first (`0 => .timeout`) and passes the
decremented fuel to every recursive call. State threading is explicit
`Run.bind` (`⤳`): the continuation receives the successor state and the
value; `.exn` retains its state and short-circuits; `.timeout`/
`.unsupported` short-circuit stateless (docs/memory-model.md v2).

`callIn` is the mutual-recursion point AND the frozen recursion point of
the proof doctrine (with `execWhile`/`execFor`): nested calls share the
caller's `World` — aliasing across calls, callee mutations visible to the
caller. The public `callFunction` wrapper below the block is thaw ∘
fresh-world ∘ `callIn` ∘ deep-freeze, signature unchanged. -/

open scoped Run in
mutual

/-- Evaluate an expression. Since H1 expressions thread the frame state
(calls mutate the shared world once the dict tier lands; in stage H1-1 the
state rides through unchanged but the TYPE already tells the truth).
Evaluation order is left to right, each operand evaluated once. -/
def evalExpr (m : Module) (fuel : Nat) (st : FrameState) (e : Expr) :
    Run FrameState RVal :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match e with
    | .constant c _ => .ok st (Const.toRVal c)
    | .name id _ =>
      -- Resolution order: local env → module globals (G1, thawed on read;
      -- a later `X = …` rebinding a `def` name wins, as in CPython) →
      -- module function table → builtins `len`/`sorted`/… → NameError —
      -- the last only when the globals are COMPLETE (no invisible
      -- top-level binder), else loudly unsupported.
      match Env.lookup st.locals id with
      | some v => .ok st v
      | Option.none =>
        match lookupG (moduleGlobals m).1 id with
        | some (some v) => .ok st v
        | some Option.none =>
          .unsupported s!"module-level value of '{id}' is outside the G1 tier"
        | Option.none =>
          if (findFunction m id).isSome then
            .unsupported s!"referencing function '{id}' as a value is outside the v0 tier"
          else if (findClass m id).isSome then
            .unsupported s!"referencing class '{id}' as a value is outside the H3 tier (classes are called, not passed)"
          else if (findNamedTuple m id).isSome then
            .unsupported s!"referencing namedtuple class '{id}' as a value is outside the tier (namedtuple classes are called, not passed)"
          else if isBuiltinName id then
            .unsupported s!"referencing builtin '{id}' as a value is outside the v0 tier"
          else if isModuleDunder id then
            .unsupported s!"module attribute '{id}' is bound by the import machinery, not by a statement — outside the G1 tier"
          else if (moduleGlobals m).2 then
            .exn st (.nameError id)
          else
            .unsupported s!"name '{id}' may be bound by an out-of-tier module-level statement"
    | .binOp l op r _ =>
        evalExpr m fuel st l ⤳ fun st a =>
        evalExpr m fuel st r ⤳ fun st b =>
        Run.liftRes st (evalBinOp op a b)
    | .unaryOp op operand _ =>
        evalExpr m fuel st operand ⤳ fun st v =>
        Run.liftRes st (evalUnaryOpH st.world.heap op v)
    | .boolOp op values _ =>
      match values.toList with
      | [] => .unsupported "BoolOp with no operands"
      | e :: es => evalBoolChain m fuel st op e es
    | .compare l ops comparators _ =>
        evalExpr m fuel st l ⤳ fun st a =>
        evalCompareChain m fuel st a ops.toList comparators.toList
    | .call f args kwargs callUnsupported _ =>
      match callUnsupported with
      | some reason => .unsupported s!"call uses unsupported features: {reason}"
      | Option.none =>
        if kwargs.isEmpty then
        match f with
        | .name fname _ =>
          -- The callee NAME is resolved before the arguments (an unbound name
          -- is a NameError without evaluating args, CPython order), but the
          -- callable CHECK happens at call time, AFTER argument evaluation:
          -- `x(1//0)` with `x = 5` raises ZeroDivisionError, not TypeError.
          match Env.lookup st.locals fname with
          | some (.ref a) =>
              -- H7: a local name may hold a CLOSURE. The call is guarded
              -- on the fragment's own function-body walk (`funsHeapFree`
              -- is false the moment any body contains a nested def), so
              -- heap-free modules keep the faithful TypeError below and
              -- worldInv never meets a closure call. Arguments evaluate
              -- BEFORE the callable check, CPython's order.
              evalExprs m fuel st args.toList ⤳ fun st vs =>
              if funsHeapFree m.functions.toList then
                .exn st (.typeError "'dict' object is not callable")
              else
                match Heap.get? st.world.heap a with
                | some (.closure nm ps ao lo _ ig bd cap) =>
                  Run.withLocals st.locals
                    (callClosure m fuel st.world nm ps ao lo ig bd cap vs.toArray)
                | _ =>
                  -- constant message on purpose: `typeNameH` here whnf-storms
                  -- symbolic proofs (the recorded H2 finding); the CLASS is
                  -- what the harness compares
                  .exn st (.typeError "'dict' object is not callable")
          | some v =>
              evalExprs m fuel st args.toList ⤳ fun st _ =>
              .exn st (.typeError s!"'{v.typeName}' object is not callable")
          | Option.none =>
            match lookupG (moduleGlobals m).1 fname with
            | some (some (.ref _)) =>
                evalExprs m fuel st args.toList ⤳ fun st _ =>
                .exn st (.typeError "'dict' object is not callable")
            | some (some v) =>
                evalExprs m fuel st args.toList ⤳ fun st _ =>
                .exn st (.typeError s!"'{v.typeName}' object is not callable")
            | some Option.none =>
              .unsupported s!"calling module-level '{fname}' (out-of-G1-tier value) is outside the tier"
            | Option.none =>
            if (findFunction m fname).isSome then
              if (findClass m fname).isSome || (findNamedTuple m fname).isSome then
                -- `def X` and `class X` (or a namedtuple bind `X = …`) in
                -- one module: the split representation loses source order,
                -- so last-binding-wins is undecidable here — loud, never a
                -- guess. (Ingestion refuses recognizing such namedtuples;
                -- the guard also covers hand-built modules.)
                .unsupported s!"name '{fname}' is bound by both 'def' and 'class'/namedtuple at module level — source-order resolution is outside the tier (ordered ModuleItem representation is the recorded fix)"
              else
                evalExprs m fuel st args.toList ⤳ fun st vs =>
                -- The frozen recursion point: the callee shares this frame's
                -- world; the caller's locals ride around the call.
                Run.withLocals st.locals (callIn m fuel st.world fname vs.toArray)
            else
              match findClass m fname with
              | some (ci, c) =>
                -- INSTANTIATION (H3): allocate the instance in the shared
                -- world, then run `__init__` (if any) through `callIn` with
                -- `self` as the first argument — methods are functions.
                if (findNamedTuple m fname).isSome then
                  -- `class X` and a namedtuple bind `X = …`: source order
                  -- lost by the split — loud (unconstructible through
                  -- ingestion; hand-built defense).
                  .unsupported s!"name '{fname}' is bound by both 'class' and a namedtuple assignment at module level — source-order resolution is outside the tier"
                else match c.ntBase with
                | some nt =>
                  -- VALUE-LIKE SUBCLASS instantiation (H5, sunfish's
                  -- `class Position(namedtuple(…))`): construction IS
                  -- namedtuple construction — an IMMEDIATE value carrying
                  -- the SUBCLASS name, no allocation, no `__init__` run
                  -- (one on the immutable self is loud, never wrong).
                  if !c.ok then
                    .unsupported s!"class '{fname}' uses unsupported features besides its namedtuple base — instantiation is outside the tier"
                  else if hasExtraDunder c then
                    .unsupported s!"class '{fname}' defines dunder methods beyond __init__ — implicit-protocol dispatch is outside the H3 tier"
                  else if (findFunction m (fname ++ ".__init__")).isSome then
                    .unsupported s!"'__init__' on the namedtuple subclass '{fname}' (immutable self) is outside the tier"
                  else
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    if vs.length == nt.fields.size then
                      .ok st (.ntuple nt.name nt.fields vs.toArray)
                    else
                      .exn st (.typeError
                        s!"{fname}() takes {nt.fields.size} positional arguments but {vs.length} were given")
                | Option.none =>
                  if !c.ok then
                    .unsupported s!"class '{fname}' uses unsupported features (bases/metaclass/decorators/class-level statements) — instantiation is outside the H3 tier"
                  else if hasExtraDunder c then
                    .unsupported s!"class '{fname}' defines dunder methods beyond __init__ — implicit-protocol dispatch is outside the H3 tier"
                  else
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    let a := st.world.heap.size
                    let st' := { st with world :=
                      { st.world with heap := st.world.heap.push (.instance ci #[]) } }
                    if (findFunction m (fname ++ ".__init__")).isSome then
                      Run.withLocals st'.locals
                        (callIn m fuel st'.world (fname ++ ".__init__")
                          ((RVal.ref a :: vs).toArray)) ⤳ fun st'' r =>
                      match r with
                      | .none => .ok st'' (.ref a)
                      | r =>
                        -- CPython checks __init__'s result: non-None raises
                        .exn st'' (.typeError s!"__init__() should return None, not '{r.typeName}'")
                    else
                      match vs with
                      | [] => .ok st' (.ref a)
                      | _ => .exn st (.typeError s!"{fname}() takes no arguments")
              | Option.none =>
                match findNamedTuple m fname with
                | some nt =>
                  -- namedtuple CONSTRUCTION (the VALUE-like decision): an
                  -- immediate value, no allocation — the world is exactly
                  -- the arguments'. Wrong arity is the faithful TypeError
                  -- (CPython raises through tuple.__new__; the harness
                  -- compares exception classes). Keyword construction
                  -- never reaches here (`call_unsupported: "keywords"`).
                  evalExprs m fuel st args.toList ⤳ fun st vs =>
                  if vs.length == nt.fields.size then
                    .ok st (.ntuple nt.tname nt.fields vs.toArray)
                  else
                    .exn st (.typeError
                      s!"{fname}() takes {nt.fields.size} positional arguments but {vs.length} were given")
                | Option.none =>
                  if fname == "len" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [v] => Run.liftRes st (lenValH st.world.heap v)
                    | _ => .exn st (.typeError s!"len() takes exactly one argument ({vs.length} given)")
                  else if fname == "sorted" then
                    -- After `findFunction`, so a module-level `def sorted` shadows
                    -- the builtin, exactly as CPython's module globals do. H2:
                    -- `sorted` of a heap list ALLOCATES its fresh result
                    -- (`sortedValH`); value arguments stay on the pure path.
                    -- H6: a GENERATOR argument drains through `drainIter`
                    -- (`sorted` is outside `heapFree`, so worldInv never
                    -- sees this arm).
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [v] =>
                      (match v with
                       | .ref a =>
                         (match Heap.get? st.world.heap a with
                          | some (.generator ..) =>
                            Run.withLocals st.locals (drainIter m fuel st.world a) ⤳ fun st vals =>
                            Run.liftRes st (sortByLt false vals) ⤳ fun st sorted_ =>
                            .ok { st with world :=
                                    { st.world with heap := st.world.heap.push (.list sorted_.toArray) } }
                              (.ref st.world.heap.size)
                          | _ =>
                            Run.liftRes st (sortedValH st.world.heap (.ref a)) ⤳ fun st hr =>
                            match hr with
                            | (h', r) => .ok { st with world := { st.world with heap := h' } } r)
                       | v =>
                         Run.liftRes st (sortedValH st.world.heap v) ⤳ fun st hr =>
                         match hr with
                         | (h', r) => .ok { st with world := { st.world with heap := h' } } r)
                    | _ => .exn st (.typeError s!"sorted expected 1 argument, got {vs.length}")
                  else if fname == "max" then
                    -- H6: a single GENERATOR argument drains — GUARDED on
                    -- the module owning generator defs (`moduleGenFree`
                    -- modules keep the loud refusal: `max` stays in the
                    -- `heapFree` fragment, and worldInv's argument kills
                    -- this branch through the guard)
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [.ref a] =>
                       (match Heap.get? st.world.heap a with
                        | some (.generator ..) =>
                          if moduleGenFree m then
                            .unsupported "max() over a generator DRAINS it (a stateful read) — outside the tier"
                          else
                            Run.withLocals st.locals (drainIter m fuel st.world a) ⤳ fun st vals =>
                            Run.liftRes st (extremumVal true [.listV vals.toArray])
                        | _ => Run.liftRes st (extremumValH st.world.heap true [.ref a]))
                     | vs => Run.liftRes st (extremumValH st.world.heap true vs))
                  else if fname == "min" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [.ref a] =>
                       (match Heap.get? st.world.heap a with
                        | some (.generator ..) =>
                          if moduleGenFree m then
                            .unsupported "min() over a generator DRAINS it (a stateful read) — outside the tier"
                          else
                            Run.withLocals st.locals (drainIter m fuel st.world a) ⤳ fun st vals =>
                            Run.liftRes st (extremumVal false [.listV vals.toArray])
                        | _ => Run.liftRes st (extremumValH st.world.heap false [.ref a]))
                     | vs => Run.liftRes st (extremumValH st.world.heap false vs))
                  else if fname == "any" || fname == "all" then
                    -- H6 draining consumers: value sequences and heap
                    -- lists scan a snapshot (`anyAllScan`); a generator
                    -- steps only until the answer DECIDES and stays
                    -- suspended (`anyAllIter` — the partial drain is
                    -- observable through a later `next`). Outside
                    -- `heapFree` (an unguarded drain mutates the world).
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [v] =>
                       (match v with
                        | .str t =>
                          Run.liftRes st
                            (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") (strCharVals t)))
                        | .tuple xs =>
                          Run.liftRes st
                            (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") xs.toList))
                        | .ntuple _ _ xs =>
                          Run.liftRes st
                            (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") xs.toList))
                        | .listV xs =>
                          Run.liftRes st
                            (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") xs.toList))
                        | .ref a =>
                          (match Heap.get? st.world.heap a with
                           | some (.list xs) =>
                             Run.liftRes st
                               (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") xs.toList))
                           | some (.dict _ _) =>
                             .unsupported s!"{fname}() over dict keys is outside the tier (live dict iteration; docs/memory-model.md)"
                           | some (.instance _ _) =>
                             .exn st (.typeError "'object' object is not iterable")
                           | some (.generator ..) =>
                             Run.withLocals st.locals (anyAllIter m fuel st.world a (fname == "all")) ⤳ fun st b =>
                             .ok st (.bool b)
                           | some (.closure ..) =>
                             .exn st (.typeError "'function' object is not iterable")
                           | Option.none => .unsupported danglingMsg)
                        | v => .exn st (.typeError s!"'{v.typeName}' object is not iterable"))
                     | vs => .exn st (.typeError s!"{fname}() takes exactly one argument ({vs.length} given)"))
                  else if fname == "abs" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [v] => Run.liftRes st (absVal v)
                    | _ => .exn st (.typeError s!"abs() takes exactly one argument ({vs.length} given)")
                  else if fname == "int" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [] => .ok st (.int 0)
                    | [v] => Run.liftRes st (intCastVal v)
                    | _ => .unsupported "int() with a base argument is outside the v0 tier"
                  else if fname == "enumerate" then
                    -- H4: a LAZY iterator object, not a materialized
                    -- list — `enumerate(self.board)` is stepped one pair
                    -- at a time, exactly as CPython's does.
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [] => .exn st (.typeError "enumerate expected at least 1 argument, got 0")
                     | v :: rest =>
                       (match enumStart rest with
                        | Option.none =>
                          if rest.length ≤ 1 then
                            .exn st (.typeError "'str' object cannot be interpreted as an integer")
                          else .exn st (.typeError s!"enumerate expected at most 2 arguments, got {vs.length}")
                        | some i0 =>
                          (match enumFrame st.world.heap i0 v with
                           | .ok fr =>
                             let g : Obj := .generator "<enumerate>" [] [fr] .suspended
                             .ok { st with world :=
                                     { st.world with heap := st.world.heap.push g } }
                               (.ref st.world.heap.size)
                           | .exn e => .exn st e
                           | .timeout => .timeout
                           | .unsupported msg => .unsupported msg)))
                  else if fname == "count" then
                    -- itertools.count — INFINITE by construction; a
                    -- consumer's `break` is what ends it (sunfish's ray
                    -- loop `for j in count(i + d, d)`)
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match countArgs vs with
                     | Option.none =>
                       .exn st (.typeError "a number is required")
                     | some (start, step) =>
                       let g : Obj :=
                         .generator "<count>" [] [.countFrom start step] .suspended
                       .ok { st with world :=
                               { st.world with heap := st.world.heap.push g } }
                         (.ref st.world.heap.size))
                  else if fname == "next" then
                    -- H4: STEP an iterator. `next(g)` on an exhausted
                    -- generator is the faithful `StopIteration`;
                    -- `next(g, d)` consumes exhaustion and yields `d`
                    -- (sunfish's `king_capture` shape). A non-iterator
                    -- argument is the faithful `TypeError` (inside
                    -- `stepIter`, which owns the referent dispatch).
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [.ref a] =>
                       Run.withLocals st.locals (stepIter m fuel st.world a) ⤳ fun st r =>
                       (match r with
                        | some v => .ok st v
                        | Option.none => .exn st .stopIteration)
                     | [.ref a, d] =>
                       Run.withLocals st.locals (stepIter m fuel st.world a) ⤳ fun st r =>
                       (match r with
                        | some v => .ok st v
                        | Option.none => .ok st d)
                     | [] => .exn st (.typeError "next expected at least 1 argument, got 0")
                     | v :: _ =>
                       .exn st (.typeError s!"'{RVal.typeNameH st.world.heap v}' object is not an iterator"))
                  else if fname == "ord" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [v] => Run.liftRes st (ordVal v)
                    | vs => .exn st (.typeError s!"ord() takes exactly one argument ({vs.length} given)")
                  else if fname == "chr" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [v] => Run.liftRes st (chrVal v)
                    | vs => .exn st (.typeError s!"chr() takes exactly one argument ({vs.length} given)")
                  else if fname == "print" then
                    -- the effect must thread World.stdout through this block;
                    -- until then a wrong NameError would be silently unfaithful
                    .unsupported "print() inside a function body is outside the tier (leanpy v0 intercepts top-level print only; docs/memory-model.md §effects)"
                  else if isModuleDunder fname then
                    .unsupported s!"module attribute '{fname}' is bound by the import machinery, not by a statement — outside the G1 tier"
                  else if (moduleGlobals m).2 then
                    .exn st (.nameError fname)
                  else
                    .unsupported s!"name '{fname}' may be bound by an out-of-tier module-level statement"
        | .attribute recv attr _ =>
          -- Method calls (dict `.get`, H2 list `.append`/`.pop`, H3
          -- instance methods). CPython order: the receiver (and its
          -- attribute lookup) evaluates BEFORE the arguments — so the
          -- dispatch is by RECEIVER first, attribute second: an instance
          -- resolves `.get`/`.append`/… through its CLASS (user methods),
          -- never through the builtin method tier. A missing instance
          -- attribute raises `AttributeError` before any argument runs.
          -- Dispatch is `execAttrCall` over the PURE `attrCallPlan`
          -- (its own mutual function: the meta-theorems fork on the
          -- plan's free scrutinee — see its docstring).
          evalExpr m fuel st recv ⤳ fun st r =>
          match r with
          | .ref a => execAttrCall m fuel st a attr args.toList
          | .ntuple tn fs xs =>
            -- namedtuple SUBCLASS method dispatch (H5): methods ARE
            -- functions — `self` is the ntuple VALUE, bound as the first
            -- argument through `callIn` (no new judgment; the immutable
            -- self is a value, so callee "mutations" are impossible by
            -- construction). The plan is decided BEFORE the arguments.
            (match ntupleCallPlan m tn fs attr with
             | .instMethod qname =>
               evalExprs m fuel st args.toList ⤳ fun st vs =>
               Run.withLocals st.locals
                 (callIn m fuel st.world qname
                   ((RVal.ntuple tn fs xs :: vs).toArray))
             | .attrMissing => .exn st .attributeError
             | .refuse msg => .unsupported msg
             | _ => .unsupported "internal: namedtuple call plan out of range (report this)")
          | .str sv =>
            -- str METHOD dispatch (H5 strings): the plan is decided from
            -- the attribute name BEFORE the arguments (`strCallPlan` — a
            -- pure free-scrutinee plan, the recorded meta-proof
            -- discipline); the workers are pure (strings are immutable
            -- values), so each in-tier arm is args + `liftRes`.
            (match strCallPlan attr with
             | .swapcase =>
               evalExprs m fuel st args.toList ⤳ fun st vs =>
               match vs with
               | [] => Run.liftRes st (strSwapcase sv)
               | vs => .exn st (.typeError s!"swapcase() takes no arguments ({vs.length} given)")
             | .isupper =>
               evalExprs m fuel st args.toList ⤳ fun st vs =>
               match vs with
               | [] => Run.liftRes st (strIsUpper sv)
               | vs => .exn st (.typeError s!"isupper() takes no arguments ({vs.length} given)")
             | .islower =>
               evalExprs m fuel st args.toList ⤳ fun st vs =>
               match vs with
               | [] => Run.liftRes st (strIsLower sv)
               | vs => .exn st (.typeError s!"islower() takes no arguments ({vs.length} given)")
             | .upper =>
               evalExprs m fuel st args.toList ⤳ fun st vs =>
               match vs with
               | [] => Run.liftRes st (strUpper sv)
               | vs => .exn st (.typeError s!"upper() takes no arguments ({vs.length} given)")
             | .index =>
               evalExprs m fuel st args.toList ⤳ fun st vs =>
               match vs with
               | [] => .exn st (.typeError "index expected at least 1 argument, got 0")
               | [.str sub] => Run.liftRes st (strIndex sv sub)
               | [v] => .exn st (.typeError s!"must be str, not {RVal.typeNameH st.world.heap v}")
               | vs =>
                 if vs.length ≤ 3 then
                   .unsupported "str.index() with start/end arguments is outside the tier (docs/memory-model.md §string semantics)"
                 else .exn st (.typeError s!"index expected at most 3 arguments, got {vs.length}")
             | .refuse msg => .unsupported msg)
          | r =>
            .unsupported s!"method call '.{attr}' on '{r.typeName}' is outside the tier (heap receivers only; docs/memory-model.md)"
        | f => .unsupported s!"calling a non-name expression ('{f.kindName}') is outside the v0 tier"
        else
          -- ===== H6 KEYWORD TIER (docs/memory-model.md §call-site
          -- keyword arguments). Keywords resolve to a COMPLETE positional
          -- array at the call site (`mergeKwArgs`) — `callIn`'s covenant
          -- signature never changes. Positionals evaluate first, then
          -- keyword VALUES, left to right (source order: Python forbids a
          -- positional after a keyword). Coverage: module `def`s by name
          -- and namedtuple-subclass methods; `sorted`'s keywords land
          -- with the draining tier; everything else is LOUD. =====
          (match f with
           | .name fname _ =>
             (match Env.lookup st.locals fname with
              | some (.ref a) =>
                  evalExprs m fuel st args.toList ⤳ fun st _ =>
                  evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st _ =>
                  match Heap.get? st.world.heap a with
                  | some (.closure ..) =>
                    .unsupported "keyword arguments on a closure call are outside the tier (docs/memory-model.md §nested defs and closures)"
                  | _ => .exn st (.typeError "'dict' object is not callable")
              | some v =>
                  evalExprs m fuel st args.toList ⤳ fun st _ =>
                  evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st _ =>
                  .exn st (.typeError s!"'{v.typeName}' object is not callable")
              | Option.none =>
                match lookupG (moduleGlobals m).1 fname with
                | some (some (.ref _)) =>
                    evalExprs m fuel st args.toList ⤳ fun st _ =>
                    evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st _ =>
                    .exn st (.typeError "'dict' object is not callable")
                | some (some v) =>
                    evalExprs m fuel st args.toList ⤳ fun st _ =>
                    evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st _ =>
                    .exn st (.typeError s!"'{v.typeName}' object is not callable")
                | some Option.none =>
                  .unsupported s!"calling module-level '{fname}' (out-of-G1-tier value) is outside the tier"
                | Option.none =>
                  match findFunction m fname with
                  | some fdefn =>
                    if (findClass m fname).isSome || (findNamedTuple m fname).isSome then
                      .unsupported s!"name '{fname}' is bound by both 'def' and 'class'/namedtuple at module level — source-order resolution is outside the tier (ordered ModuleItem representation is the recorded fix)"
                    else if !fdefn.argsOk then
                      -- the merge would read an UNTRUSTED parameter table:
                      -- the loud refusal must win over any binding TypeError
                      .unsupported s!"function '{fname}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
                    else
                      evalExprs m fuel st args.toList ⤳ fun st vs =>
                      evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st kvs =>
                      Run.liftRes st
                        (mergeKwArgs fname fdefn.params vs
                          ((kwargs.toList.map (·.1)).zip kvs)) ⤳ fun st full =>
                      Run.withLocals st.locals (callIn m fuel st.world fname full)
                  | Option.none =>
                    if (findClass m fname).isSome then
                      .unsupported s!"instantiating class '{fname}' with keyword arguments is outside the H6 tier"
                    else if (findNamedTuple m fname).isSome then
                      .unsupported s!"constructing namedtuple '{fname}' with keyword arguments is outside the H6 tier (a wrong field-order guess would be silent corruption)"
                    else if fname == "sorted" then
                      -- reverse= accepted (truthiness decides the
                      -- direction); key= gates on FIRST-CLASS CALLABLE
                      -- values — loud; any other keyword is CPython's
                      -- faithful TypeError, raised AFTER the arguments
                      -- evaluate (CPython's order)
                      if kwargs.toList.any (·.1 == "key") then
                        .unsupported "sorted(key=…) is outside the tier — the key callable is a first-class function value (bound methods are loud under H3; docs/backlog.md)"
                      else
                        (match kwargs.toList.find? (fun kv => kv.1 != "reverse") with
                         | some (k, _) =>
                           evalExprs m fuel st args.toList ⤳ fun st _ =>
                           evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st _ =>
                           .exn st (.typeError s!"'{k}' is an invalid keyword argument for sorted()")
                         | Option.none =>
                           evalExprs m fuel st args.toList ⤳ fun st vs =>
                           evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st kvs =>
                           (match vs, kvs with
                            | [v], [rv] =>
                              Run.liftRes st (truthyH st.world.heap rv) ⤳ fun st desc =>
                              (match v with
                               | .ref a =>
                                 (match Heap.get? st.world.heap a with
                                  | some (.generator ..) =>
                                    Run.withLocals st.locals (drainIter m fuel st.world a) ⤳ fun st vals =>
                                    Run.liftRes st (sortByLt desc vals) ⤳ fun st sorted_ =>
                                    .ok { st with world :=
                                            { st.world with heap := st.world.heap.push (.list sorted_.toArray) } }
                                      (.ref st.world.heap.size)
                                  | _ =>
                                    Run.liftRes st (sortedValH st.world.heap (.ref a) desc) ⤳ fun st hr =>
                                    match hr with
                                    | (h', r) => .ok { st with world := { st.world with heap := h' } } r)
                               | v =>
                                 Run.liftRes st (sortedValH st.world.heap v desc) ⤳ fun st hr =>
                                 match hr with
                                 | (h', r) => .ok { st with world := { st.world with heap := h' } } r)
                            | [_], _ =>
                              .unsupported "duplicate keyword argument 'reverse' (unreachable through ingestion — CPython rejects it at compile time)"
                            | vs, _ => .exn st (.typeError s!"sorted expected 1 argument, got {vs.length}")))
                    else if isBuiltinName fname then
                      .unsupported s!"builtin '{fname}' with keyword arguments is outside the H6 tier"
                    else if isModuleDunder fname then
                      .unsupported s!"module attribute '{fname}' is bound by the import machinery, not by a statement — outside the G1 tier"
                    else if (moduleGlobals m).2 then
                      .exn st (.nameError fname)
                    else
                      .unsupported s!"name '{fname}' may be bound by an out-of-tier module-level statement")
           | .attribute recv attr _ =>
             evalExpr m fuel st recv ⤳ fun st r =>
             (match r with
              | .ref a =>
                -- H7+: INSTANCE-method keywords (`self.bound(…, root=True)`)
                -- — the same merge, `self` prepended; builtin methods with
                -- keywords stay loud
                (match attrCallPlan m st.world.heap a attr with
                 | .instMethod qname =>
                   (match findFunction m qname with
                    | some fdefn =>
                      if !fdefn.argsOk then
                        .unsupported s!"function '{qname}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
                      else
                        evalExprs m fuel st args.toList ⤳ fun st vs =>
                        evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st kvs =>
                        Run.liftRes st
                          (mergeKwArgs qname fdefn.params (RVal.ref a :: vs)
                            ((kwargs.toList.map (·.1)).zip kvs)) ⤳ fun st full =>
                        Run.withLocals st.locals (callIn m fuel st.world qname full)
                    | Option.none =>
                      .unsupported "internal: instance method plan without a definition (report this)")
                 | .instAttrValue =>
                   .unsupported s!"calling an instance ATTRIBUTE value ('.{attr}' is data on this instance, not a method) is outside the H3 tier"
                 | .attrMissing => .exn st .attributeError
                 | .dictGet =>
                   .unsupported "dict.get() with keyword arguments is outside the tier (get is positional-only in CPython)"
                 | .listAppend =>
                   .unsupported "list.append() with keyword arguments is outside the tier (append is positional-only in CPython)"
                 | .listPop =>
                   .unsupported "list.pop() with keyword arguments is outside the tier (pop is positional-only in CPython)"
                 | .refuse msg => .unsupported msg
                 | .dangling => .unsupported danglingMsg)
              | .ntuple tn fs xs =>
                (match ntupleCallPlan m tn fs attr with
                 | .instMethod qname =>
                   (match findFunction m qname with
                    | some fdefn =>
                      if !fdefn.argsOk then
                        .unsupported s!"function '{qname}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
                      else
                        evalExprs m fuel st args.toList ⤳ fun st vs =>
                        evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st kvs =>
                        Run.liftRes st
                          (mergeKwArgs qname fdefn.params
                            (RVal.ntuple tn fs xs :: vs)
                            ((kwargs.toList.map (·.1)).zip kvs)) ⤳ fun st full =>
                        Run.withLocals st.locals (callIn m fuel st.world qname full)
                    | Option.none =>
                      .unsupported "internal: namedtuple method plan without a definition (report this)")
                 | .attrMissing => .exn st .attributeError
                 | .refuse msg => .unsupported msg
                 | _ => .unsupported "internal: namedtuple call plan out of range (report this)")
              | r =>
                .unsupported s!"method call '.{attr}' with keyword arguments on '{RVal.typeNameH st.world.heap r}' is outside the H6 tier")
           | f => .unsupported s!"calling a non-name expression ('{f.kindName}') is outside the v0 tier")
    | .list elts _ =>
        -- H2: a list display ALLOCATES (`BUILD_LIST`) — the fresh address
        -- is the old heap size; every literal is a distinct object.
        evalExprs m fuel st elts.toList ⤳ fun st vs =>
        .ok { st with world :=
                { st.world with heap := st.world.heap.push (.list vs.toArray) } }
          (.ref st.world.heap.size)
    | .tuple elts _ =>
        evalExprs m fuel st elts.toList ⤳ fun st vs =>
        .ok st (.tuple vs.toArray)
    | .subscript v idx _ =>
        evalExpr m fuel st v ⤳ fun st c =>
        evalExpr m fuel st idx ⤳ fun st i =>
        Run.liftRes st (indexValH st.world.heap c i)
    | .dict keys values _ =>
        -- CPython `BUILD_MAP`: every key/value expression evaluates first
        -- (k₁, v₁, k₂, v₂, … left to right), then entries insert in order
        -- (hashability checked per insert; duplicate equal keys keep the
        -- first key/position, take the last value), then the ALLOCATION —
        -- the fresh address is the old heap size.
        evalDictItems m fuel st keys.toList values.toList ⤳ fun st items =>
        Run.liftRes st (dictBuild st.world.heap [] items) ⤳ fun st entries =>
        .ok { st with world :=
                { st.world with heap := st.world.heap.push (.dict entries.toArray 0) } }
          (.ref st.world.heap.size)
    | .attribute recv attr _ =>
      -- Attribute READ (H3): an instance resolves `attr` in its attribute
      -- table (`self.tp_score` — a heap read, world-preserving); a missing
      -- attribute that names a CLASS METHOD would be a bound-method value
      -- (loud — methods are called, not passed); otherwise the faithful
      -- `AttributeError` (no `__getattr__` can exist — the dunder guard).
      -- Dispatch is `attrReadResult` over the PURE `attrReadPlan`
      -- (meta-theorem discipline).
      evalExpr m fuel st recv ⤳ fun st r =>
      match r with
      | .ref a => attrReadResult m st a attr
      | .ntuple tn fields xs =>
        -- namedtuple FIELD access (the VALUE-like decision): tuple
        -- indexing by declared position — pure, world-preserving; a
        -- SUBCLASS method name is the loud bound-method refusal (H5)
        Run.liftRes st (ntupleAttr m tn fields xs attr)
      | r =>
        .unsupported s!"attribute access on '{r.typeName}' is outside the tier (heap receivers only; docs/memory-model.md)"
    | .ifExp t b o _ =>
        -- CPython: the test first, then EXACTLY ONE branch (lazy)
        evalExpr m fuel st t ⤳ fun st tv =>
        Run.liftRes st (truthyH st.world.heap tv) ⤳ fun st cond =>
        if cond then evalExpr m fuel st b else evalExpr m fuel st o
    | .slice v l u stp _ =>
        -- H5 strings: CPython order — the receiver, then the slice
        -- components lower/upper/step (`BUILD_SLICE`), then the subscript
        -- application (`sliceVal`, pure — the tier is str receivers)
        evalExpr m fuel st v ⤳ fun st cv =>
        evalExpr m fuel st l ⤳ fun st lv =>
        evalExpr m fuel st u ⤳ fun st uv =>
        evalExpr m fuel st stp ⤳ fun st sv =>
        Run.liftRes st (sliceVal cv lv uv sv)
    | .genExp .. =>
        -- Ingestion LOWERS every genexp it can into a generator function
        -- (`lowerGenExps`, Json.lean); one that survives to evaluation is
        -- a shape the lowering refused — loud, never a guess.
        .unsupported "this generator expression is outside the tier (ingestion could not lower it to a generator function; docs/memory-model.md §generator semantics)"
    | .unsupported pyKind _ _ => .unsupported s!"unsupported expression '{pyKind}'"
  termination_by structural fuel

/-- Evaluate a list of expressions left to right, each exactly once. -/
def evalExprs (m : Module) (fuel : Nat) (st : FrameState) (es : List Expr) :
    Run FrameState (List RVal) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match es with
    | [] => .ok st []
    | e :: rest =>
        evalExpr m fuel st e ⤳ fun st v =>
        evalExprs m fuel st rest ⤳ fun st vs =>
        .ok st (v :: vs)
  termination_by structural fuel

/-- Evaluate a dict literal's key/value expressions in CPython order:
`k₁, v₁, k₂, v₂, …`, left to right, each exactly once. Insertion (and its
hashability checks) happens AFTERWARDS, in `dictBuild` — `BUILD_MAP`
evaluates every element before constructing the map. -/
def evalDictItems (m : Module) (fuel : Nat) (st : FrameState)
    (keys values : List Expr) : Run FrameState (List (RVal × RVal)) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match keys, values with
    | [], [] => .ok st []
    | k :: ks, v :: vs =>
        evalExpr m fuel st k ⤳ fun st kv =>
        evalExpr m fuel st v ⤳ fun st vv =>
        evalDictItems m fuel st ks vs ⤳ fun st rest =>
        .ok st ((kv, vv) :: rest)
    | _, _ => .unsupported "Dict with mismatched keys/values"
  termination_by structural fuel

/-- Attribute-CALL dispatch on a heap receiver (H3) — a separate mutual
function so that `fuelMono`/`worldInv` fork on `attrCallPlan`'s FREE
scrutinee instead of a match nested under the receiver binder. The plan
is decided BEFORE argument evaluation (CPython: receiver and attribute
lookup precede the arguments — a missing attribute raises
`AttributeError` before any argument runs); an instance method runs
through `callIn` with `self` bound as the first argument. -/
def execAttrCall (m : Module) (fuel : Nat) (st : FrameState) (a : Addr)
    (attr : String) (args : List Expr) : Run FrameState RVal :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match attrCallPlan m st.world.heap a attr with
    | .instMethod qname =>
      -- the method IS a function (flattened under the qualified name):
      -- `self` is the first argument and the call threads the shared
      -- world through the frozen recursion point, exactly like any call
      evalExprs m fuel st args ⤳ fun st vs =>
      Run.withLocals st.locals
        (callIn m fuel st.world qname ((RVal.ref a :: vs).toArray))
    | .instAttrValue =>
      .unsupported s!"calling an instance ATTRIBUTE value ('.{attr}' is data on this instance, not a method) is outside the H3 tier"
    | .attrMissing => .exn st .attributeError
    | .dictGet =>
      evalExprs m fuel st args ⤳ fun st vs =>
      match vs with
      | [k] => Run.liftRes st (heapGet st.world.heap a k .none)
      | [k, d] => Run.liftRes st (heapGet st.world.heap a k d)
      | vs => .exn st (.typeError s!"get expected at most 2 arguments, got {vs.length}")
    | .listAppend =>
      evalExprs m fuel st args ⤳ fun st vs =>
      match vs with
      | [v] =>
        Run.liftRes st (heapAppend st.world.heap a v) ⤳ fun st h' =>
        .ok { st with world := { st.world with heap := h' } } .none
      | vs => .exn st (.typeError s!"append() takes exactly one argument ({vs.length} given)")
    | .listPop =>
      evalExprs m fuel st args ⤳ fun st vs =>
      match vs with
      | [] =>
        Run.liftRes st (heapPop st.world.heap a Option.none) ⤳ fun st hr =>
        match hr with
        | (h', v) => .ok { st with world := { st.world with heap := h' } } v
      | [i] =>
        (match asInt i with
         | some n =>
           Run.liftRes st (heapPop st.world.heap a (some n)) ⤳ fun st hr =>
           match hr with
           | (h', v) => .ok { st with world := { st.world with heap := h' } } v
         | Option.none =>
           .exn st (.typeError s!"'{i.typeName}' object cannot be interpreted as an integer"))
      | vs => .exn st (.typeError s!"pop expected at most 1 argument, got {vs.length}")
    | .refuse msg => .unsupported msg
    | .dangling => .unsupported danglingMsg
  termination_by structural fuel

/-- `and`/`or` chain: short-circuits and returns the deciding *operand value*
(not a bool): `0 or "x"` is `"x"`; the last operand is returned as-is. -/
def evalBoolChain (m : Module) (fuel : Nat) (st : FrameState) (op : BoolOp)
    (e : Expr) (rest : List Expr) : Run FrameState RVal :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    evalExpr m fuel st e ⤳ fun st v =>
    match rest with
    | [] => .ok st v
    | e' :: rest' =>
      Run.liftRes st (truthyH st.world.heap v) ⤳ fun st b =>
      match op with
      | .and => if b then evalBoolChain m fuel st .and e' rest' else .ok st v
      | .or => if b then .ok st v else evalBoolChain m fuel st .or e' rest'
  termination_by structural fuel

/-- Chained comparison `a < b < c …`: each operand is evaluated exactly once,
left to right; short-circuits to `False` on the first failing link (the
remaining comparators are not evaluated). `lhs` is the already-evaluated
value of the previous operand. -/
def evalCompareChain (m : Module) (fuel : Nat) (st : FrameState) (lhs : RVal)
    (ops : List CmpOp) (comparators : List Expr) : Run FrameState RVal :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match ops, comparators with
    | [], [] => .ok st (.bool true)
    | op :: ops', e :: rest =>
        evalExpr m fuel st e ⤳ fun st rhs =>
        Run.liftRes st (evalCompareOpH st.world.heap fuel op lhs rhs) ⤳ fun st b =>
        if b then evalCompareChain m fuel st rhs ops' rest
        else .ok st (.bool false)
    | _, _ => .unsupported "Compare with mismatched ops/comparators"
  termination_by structural fuel

/-- Execute one statement. The updated frame state lives in the `Run`
outcome (retained on `.ok` AND `.exn`); the value is how control continues
(`RFlow.next/ret/brk/cont`). -/
def execStmt (m : Module) (fuel : Nat) (st : FrameState) (s : Stmt) :
    Run FrameState RFlow :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match s with
    | .ret Option.none _ => .ok st (.ret .none)
    | .ret (some e) _ =>
        evalExpr m fuel st e ⤳ fun st v =>
        .ok st (.ret v)
    | .assign targets value _ =>
      match targets.toList with
      | [.subscript dE kE _] =>
          -- Subscript STORE (H1: dict mutation, aliasing-visible). CPython
          -- order (language reference; docs/memory-model.md): the RHS
          -- first, then the target primary, then the subscript, then the
          -- store. Value-list stores stay loud until H2; tuple/str stores
          -- are the faithful TypeError.
          evalExpr m fuel st value ⤳ fun st v =>
          evalExpr m fuel st dE ⤳ fun st c =>
          evalExpr m fuel st kE ⤳ fun st k =>
          match c with
          | .ref a =>
            Run.liftRes st (heapStore st.world.heap a k v) ⤳ fun st h' =>
            .ok { st with world := { st.world with heap := h' } } .next
          | .listV _ =>
            .unsupported "subscript assignment to a list ('xs[i] = v' mutates in place, visible through aliases) is outside the v0 tier (lists move to the heap at H2)"
          | c => .exn st (.typeError s!"'{c.typeName}' object does not support item assignment")
      | [.attribute recvE attr _] =>
          -- Attribute STORE (H3: mutable self — `self.x = v`, aliasing-
          -- visible). CPython order: the RHS first, then the target
          -- primary, then the store. A non-instance target is the faithful
          -- `AttributeError` (builtins take no new attributes; scalars
          -- likewise — no `__setattr__` can interfere, the dunder guard).
          evalExpr m fuel st value ⤳ fun st v =>
          evalExpr m fuel st recvE ⤳ fun st r =>
          match r with
          | .ref a =>
            Run.liftRes st (heapAttrStore st.world.heap a attr v) ⤳ fun st h' =>
            .ok { st with world := { st.world with heap := h' } } .next
          | _ => .exn st .attributeError
      | [t] =>
          -- CPython order: the value is evaluated before the store. H2:
          -- `assignToH` — unpacking from a heap list reads the heap.
          evalExpr m fuel st value ⤳ fun st v =>
          Run.liftRes st (assignToH st.world.heap st.locals t v) ⤳ fun st env' =>
          .ok { st with locals := env' } .next
      | _ => .unsupported "chained assignment (multiple targets) is outside the v0 tier"
    | .augAssign target op value _ =>
      match target with
      | .name id _ =>
        -- CPython order: the target is loaded before the value is evaluated.
        match Env.lookup st.locals id with
        | Option.none => .exn st (.nameError id)
        | some (.listV _) =>
            -- CPython `list += x` mutates the object IN PLACE (observable
            -- through aliases); the value semantics would silently rebind
            -- only this name. Loud, not wrong: refuse the construct.
            -- (str/tuple/int/bool are immutable, so rebinding is faithful.)
            .unsupported
              "augmented assignment to a list ('+=' mutates in place, visible through aliases) is outside the v0 tier"
        | some (.ref _) =>
            .unsupported
              "augmented assignment to a heap object is outside the H1 tier (docs/memory-model.md)"
        | some old =>
            evalExpr m fuel st value ⤳ fun st v =>
            Run.liftRes st (evalBinOp op old v) ⤳ fun st r =>
            .ok { st with locals := Env.set st.locals id r } .next
      | t => .unsupported s!"augmented assignment to '{t.kindName}' is outside the v0 tier"
    | .whileLoop test body orelse _ =>
      execWhile m fuel st test body.toList orelse.toList
    | .forStmt target iter body orelse _ =>
      -- (`orelse` inspected via `toList` pattern-match, the interpreter's
      -- standard idiom — a helper like `Array.isEmpty` would be outside the
      -- symbolic-execution simp sets and wedge every `for` at the guard.)
      match orelse.toList with
      | [] =>
        evalExpr m fuel st iter ⤳ fun st it =>
        match it with
        | .listV xs => execFor m fuel st target xs.toList body.toList
        | .tuple xs => execFor m fuel st target xs.toList body.toList
        | .ntuple _ _ xs => execFor m fuel st target xs.toList body.toList
        -- H5 iteration: a str iterates its CODE POINTS. The snapshot is
        -- the live semantics here — strs are immutable, so unlike a heap
        -- list there is nothing for a cursor to observe (`strCharVals`).
        | .str s => execFor m fuel st target (strCharVals s) body.toList
        | .ref a =>
          -- H2: `for` over a heap LIST is a LIVE INDEX CURSOR against the
          -- object (CPython's listiterator) — never a snapshot: mutation,
          -- growth, and shrinkage during iteration are all observable.
          -- The referent dispatch (dicts stay loudly out — live dict
          -- iteration; no snapshot shortcut) lives INSIDE `execForList`.
          execForList m fuel st target a 0 body.toList
        | v => .exn st (.typeError s!"'{v.typeName}' object is not iterable")
      | _ :: _ => .unsupported "'for … else' is outside the v0 tier"
    | .ifStmt test body orelse _ =>
        evalExpr m fuel st test ⤳ fun st t =>
        Run.liftRes st (truthyH st.world.heap t) ⤳ fun st b =>
        if b then execStmts m fuel st body.toList
        else execStmts m fuel st orelse.toList
    | .exprStmt e _ =>
        evalExpr m fuel st e ⤳ fun st _ =>
        .ok st .next
    | .yieldStmt _ _ =>
        -- Reaching `yield` through the ORDINARY statement executor means
        -- the enclosing def was not recognized as a generator (a
        -- hand-built module, or a `yield` at module level) — loud, never
        -- a silent no-op. Inside a generator the continuation walker
        -- (`execGen`) owns this node and `execStmt` never sees it.
        .unsupported "'yield' outside a generator body (the def is not marked `is_generator`) — outside the tier"
    | .defStmt name params argsOk localsOk hasGlobal isGenerator body captures _ =>
      -- H7 (docs/memory-model.md §nested defs and closures): SNAPSHOT
      -- the captures from the current frame, ALLOCATE the closure
      -- object, bind the name. Under the extractor's never-rebound
      -- admission the snapshot IS CPython's cell.
      (match capturesSnapshot st.locals captures.toList with
       | Option.none =>
         .unsupported s!"nested def '{name}': a captured name is unbound at def time (unreachable through ingestion — report this)"
       | some cap =>
         let a := st.world.heap.size
         let obj : Obj :=
           .closure name params argsOk localsOk hasGlobal isGenerator body cap
         .ok { st with
               world := { st.world with heap := st.world.heap.push obj },
               locals := Env.set st.locals name (.ref a) } .next)
    | .pass _ => .ok st .next
    | .brk _ => .ok st .brk
    | .cont _ => .ok st .cont
    | .unsupported pyKind _ _ => .unsupported s!"unsupported statement '{pyKind}'"
  termination_by structural fuel

/-- Execute statements in order; stop at the first non-`next` flow (or error). -/
def execStmts (m : Module) (fuel : Nat) (st : FrameState) (ss : List Stmt) :
    Run FrameState RFlow :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match ss with
    | [] => .ok st .next
    | s :: rest =>
        execStmt m fuel st s ⤳ fun st flow =>
        match flow with
        | .next => execStmts m fuel st rest
        | flow => .ok st flow
  termination_by structural fuel

/-- `for target in <evaluated list/tuple>: body` (no `orelse` — refused
loudly upstream). One element per step: bind `target` to the element
(`assignTo` — plain names and tuple-unpacking targets, same tier as
assignment), run the body; `break` exits, `continue` steps, `return`
propagates. The iterated values were captured BEFORE the loop began
(`evalExpr` on the iterable) — faithful for value-lists; the live dict
iterator (H1-proper) is a different construct and never reaches here. -/
def execFor (m : Module) (fuel : Nat) (st : FrameState) (target : Expr)
    (xs : List RVal) (body : List Stmt) : Run FrameState RFlow :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match xs with
    | [] => .ok st .next
    | x :: rest =>
        Run.liftRes st (assignToH st.world.heap st.locals target x) ⤳ fun st env₁ =>
        execStmts m fuel { st with locals := env₁ } body ⤳ fun st flow =>
        match flow with
        | .next | .cont => execFor m fuel st target rest body
        | .brk => .ok st .next
        | .ret v => .ok st (.ret v)
  termination_by structural fuel

/-- `for target in <heap list>: body` (H2) — the LIVE INDEX CURSOR:
each step re-reads the object at `a` (so in-place mutation, growth, and
`pop`-shrinkage during iteration are observed exactly as CPython's
listiterator observes them: `xs.pop()` in the body skips the tail;
`append` extends the iteration); the cursor `i` advances by one per
completed step; `i ≥ len` at re-read ends the loop. `break` exits,
`continue` steps, `return` propagates. Owns the referent dispatch for
`for`-over-`.ref` (a dict referent is the loud live-dict-iteration
refusal). A frozen recursion point like `execFor`. -/
def execForList (m : Module) (fuel : Nat) (st : FrameState) (target : Expr)
    (a : Addr) (i : Nat) (body : List Stmt) : Run FrameState RFlow :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match Heap.get? st.world.heap a with
    | some (.list xs) =>
      if i < xs.size then
        Run.liftRes st (assignToH st.world.heap st.locals target (xs.getD i .none)) ⤳ fun st env₁ =>
        execStmts m fuel { st with locals := env₁ } body ⤳ fun st flow =>
        match flow with
        | .next | .cont => execForList m fuel st target a (i + 1) body
        | .brk => .ok st .next
        | .ret v => .ok st (.ret v)
      else .ok st .next
    | some (.dict _ _) =>
        .unsupported "'for' over a dict is outside the tier (live dict iteration is deliberately NOT in the inventory — no snapshot shortcut; docs/memory-model.md)"
    | some (.instance _ _) =>
        -- H3: no `__iter__`/`__getitem__` can exist (dunder guard)
        .exn st (.typeError "'object' object is not iterable")
    | some (.generator ..) =>
        -- H4: `for x in <generator>` — the LAZY cursor. The guard is the
        -- one place the generator machinery meets the heap-free fragment:
        -- a module with no generator defs can hold no generator object, so
        -- this arm is unreachable there and says so LOUDLY instead of
        -- silently stepping (which is what keeps `worldInv` free of a
        -- heap-side invariant — see `moduleGenFree`).
        if moduleGenFree m then
          .unsupported "internal: a generator object in a module with no generator defs (heap well-formedness violation — report this)"
        else execForGen m fuel st target a body
    | some (.closure ..) =>
        .unsupported "internal: a list cursor over a function object (report this)"
    | Option.none => .unsupported danglingMsg
  termination_by structural fuel

/-- `while test: body else: orelse`. `break` exits the loop skipping `orelse`;
`continue` re-tests; `return` propagates; on normal exit (test falsy) the
`orelse` runs (a `break` inside it belongs to an enclosing loop and
propagates). -/
def execWhile (m : Module) (fuel : Nat) (st : FrameState) (test : Expr)
    (body orelse : List Stmt) : Run FrameState RFlow :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    evalExpr m fuel st test ⤳ fun st t =>
    Run.liftRes st (truthyH st.world.heap t) ⤳ fun st b =>
    if b then
      execStmts m fuel st body ⤳ fun st flow =>
      match flow with
      | .next | .cont => execWhile m fuel st test body orelse
      | .brk => .ok st .next
      | .ret v => .ok st (.ret v)
    else
      execStmts m fuel st orelse
  termination_by structural fuel

/-- Call a module-level function by name with already-evaluated runtime
arguments, INSIDE a world: the callee's frame shares the caller's `World`
(heap and globals — aliasing across calls, callee mutations visible to the
caller), with a fresh locals env. **The frozen recursion point** of the
proof doctrine (docs/memory-model.md v2, replacing `callFunction` in that
covenant): nested Python-to-Python calls use ONLY `callIn`.

Falling off the end (or bare `return`) yields `RVal.none`. Unknown name →
`NameError`; unsupported parameter features (`argsOk = false`: non-literal
defaults/varargs/kwargs/decorators) → unsupported; arity outside
`nparams - ndefaults ≤ nargs ≤ nparams` (`arityOk`) → `TypeError`. Missing
trailing arguments are filled from literal parameter defaults inside
`mkCallEnv` (see its docstring for why call-time filling of literals
matches CPython's def-time evaluation). -/
def callIn (m : Module) (fuel : Nat) (w : World) (fname : String)
    (args : Array RVal) : Run World RVal :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match findFunction m fname with
    | Option.none => .exn w (.nameError fname)
    | some f =>
      if !f.argsOk then
        .unsupported
          s!"function '{fname}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
      else if !f.localsOk then
        .unsupported
          s!"function '{fname}' calls a name it also assigns (CPython static-locals rule) — outside the v0 tier"
      else if !arityOk f.params args.size then
        .exn w (.typeError
          s!"{fname}() takes {f.params.size} positional arguments but {args.size} were given")
      else if f.isGenerator then
        -- H4 CREATION: calling a generator function runs NO code. It
        -- allocates the suspended frame — arguments bound into its
        -- locals, the whole body as the initial continuation — and
        -- returns the object. Every effect in the body (sunfish's
        -- TT writes) therefore happens only as a consumer steps it,
        -- which is exactly the laziness the search depends on.
        let g : Obj :=
          .generator fname (mkCallEnv f.params args) [.block f.body.toList] .created
        .ok { w with heap := w.heap.push g } (.ref w.heap.size)
      else
        Run.toWorld <|
          execStmts m fuel ⟨w, mkCallEnv f.params args⟩ f.body.toList ⤳ fun st flow =>
          match flow with
          | .ret v => .ok st v
          | .next => .ok st .none
          | .brk => .unsupported "'break' outside loop"
          | .cont => .unsupported "'continue' outside loop"
  termination_by structural fuel

/-- **The generator stepper** (H4, docs/memory-model.md §generator
semantics) — resume the generator at `a` until its next `yield`.
`some v` is that yield; `none` is exhaustion (the object becomes
`closed`, and every later step is `none` again).

The status is set to `running` for the duration, so a generator that
re-enters itself gets CPython's faithful `ValueError` rather than a
silent nested resumption. Resumption re-enters the body through the
stored continuation with the stored locals; suspension stores the
locals BACK, so the frame's variables survive between yields exactly as
CPython's do. A frozen recursion point, like `callIn`. -/
def stepIter (m : Module) (fuel : Nat) (w : World) (a : Addr) :
    Run World (Option RVal) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match Heap.get? w.heap a with
    | some (.generator qname locals cont status) =>
      match status with
      | .closed => .ok w Option.none
      | .running =>
        .exn w (.valueError "generator already executing")
      | _ =>
        match Heap.update w.heap a (.generator qname locals cont .running) with
        | Option.none => .unsupported danglingMsg
        | some h₁ =>
          Run.toWorld <|
            execGen m fuel ⟨{ w with heap := h₁ }, locals⟩ cont ⤳ fun st r =>
            match r with
            | some (v, cont') =>
              (match Heap.update st.world.heap a
                  (.generator qname st.locals cont' .suspended) with
               | Option.none => .unsupported danglingMsg
               | some h₂ =>
                 .ok { st with world := { st.world with heap := h₂ } } (some v))
            | Option.none =>
              (match Heap.update st.world.heap a
                  (.generator qname st.locals [] .closed) with
               | Option.none => .unsupported danglingMsg
               | some h₂ =>
                 .ok { st with world := { st.world with heap := h₂ } } Option.none)
    | some _ =>
      .exn w (.typeError s!"'{RVal.typeNameH w.heap (.ref a)}' object is not an iterator")
    | Option.none => .unsupported danglingMsg
  termination_by structural fuel

/-- **The continuation walker** (H4) — run a generator body from a
defunctionalized continuation until the next `yield` (`some (v, k')`) or
until the body ends (`none`: a bare `return`, or falling off the end).

Yield-FREE statements go through the ordinary `execStmt`, so their
semantics has exactly one definition; only the constructs that can
SUSPEND are opened here, and the frame stack replaces the Lean call
stack that `execStmts` would otherwise own. `break`/`continue` returned
by a delegated statement unwind the frame stack (`genBreak`/
`genContinue`); a `return` ends the generator. `return <value>` sets
`StopIteration.value` in CPython — a channel this tier does not model,
so it refuses LOUDLY rather than dropping the value. A frozen recursion
point. -/
def execGen (m : Module) (fuel : Nat) (st : FrameState) (k : GenCont) :
    Run FrameState (Option (RVal × GenCont)) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match k with
    | [] => .ok st Option.none
    | .block [] :: k' => execGen m fuel st k'
    | .block (s :: ss) :: k' =>
      (match genPlan s with
       | .delegate =>
         execStmt m fuel st s ⤳ fun st flow =>
         (match flow with
          | .next => execGen m fuel st (.block ss :: k')
          | .ret .none => .ok st Option.none
          | .ret _ =>
            .unsupported "'return <value>' inside a generator (StopIteration.value) is outside the tier"
          | .brk =>
            (match genBreak k' with
             | some k'' => execGen m fuel st k''
             | Option.none => .unsupported "'break' outside loop")
          | .cont =>
            (match genContinue k' with
             | some k'' => execGen m fuel st k''
             | Option.none => .unsupported "'continue' outside loop"))
       | .yieldHere e =>
           evalExpr m fuel st e ⤳ fun st v =>
           .ok st (some (v, .block ss :: k'))
       | .branch test body orelse =>
           evalExpr m fuel st test ⤳ fun st t =>
           Run.liftRes st (truthyH st.world.heap t) ⤳ fun st b =>
           execGen m fuel st
             ((if b then GenFrame.block body else GenFrame.block orelse)
               :: .block ss :: k')
       | .whileHere test body orelse =>
           execGen m fuel st (.whileLoop test body orelse :: .block ss :: k')
       | .forHere target iter body =>
           evalExpr m fuel st iter ⤳ fun st it =>
           (match it with
            | .listV xs =>
                execGen m fuel st (.forSeq target xs.toList body :: .block ss :: k')
            | .tuple xs =>
                execGen m fuel st (.forSeq target xs.toList body :: .block ss :: k')
            | .ntuple _ _ xs =>
                execGen m fuel st (.forSeq target xs.toList body :: .block ss :: k')
            | .str sv =>
                execGen m fuel st (.forSeq target (strCharVals sv) body :: .block ss :: k')
            | .ref ad =>
              (match Heap.get? st.world.heap ad with
               | some (.list _) =>
                   execGen m fuel st (.forList target ad 0 body :: .block ss :: k')
               | some (.generator ..) =>
                   execGen m fuel st (.forGen target ad body :: .block ss :: k')
               | some (.dict _ _) =>
                   .unsupported "'for' over a dict is outside the tier (live dict iteration is deliberately NOT in the inventory; docs/memory-model.md)"
               | some (.instance _ _) =>
                   .exn st (.typeError "'object' object is not iterable")
               | some (.closure ..) =>
                   .exn st (.typeError "'function' object is not iterable")
               | Option.none => .unsupported danglingMsg)
            | v => .exn st (.typeError s!"'{v.typeName}' object is not iterable"))
       | .refuse msg => .unsupported msg)
    | .forSeq target xs body :: k' =>
      (match xs with
       | [] => execGen m fuel st k'
       | x :: rest =>
         Run.liftRes st (assignToH st.world.heap st.locals target x) ⤳ fun st env₁ =>
         execGen m fuel { st with locals := env₁ }
           (.block body :: .forSeq target rest body :: k'))
    | .forList target ad i body :: k' =>
      (match Heap.get? st.world.heap ad with
       | some (.list xs) =>
         if i < xs.size then
           Run.liftRes st (assignToH st.world.heap st.locals target (xs.getD i .none)) ⤳ fun st env₁ =>
           execGen m fuel { st with locals := env₁ }
             (.block body :: .forList target ad (i + 1) body :: k')
         else execGen m fuel st k'
       | some (.dict _ _) =>
           .unsupported "'for' over a dict is outside the tier (live dict iteration; docs/memory-model.md)"
       | some (.instance _ _) => .exn st (.typeError "'object' object is not iterable")
       | some (.generator ..) =>
           .unsupported "internal: a list cursor over a generator object (report this)"
       | some (.closure ..) =>
           .unsupported "internal: a list cursor over a function object (report this)"
       | Option.none => .unsupported danglingMsg)
    | .forGen target ad body :: k' =>
      Run.withLocals st.locals (stepIter m fuel st.world ad) ⤳ fun st r =>
      (match r with
       | Option.none => execGen m fuel st k'
       | some v =>
         Run.liftRes st (assignToH st.world.heap st.locals target v) ⤳ fun st env₁ =>
         execGen m fuel { st with locals := env₁ }
           (.block body :: .forGen target ad body :: k'))
    | .enumSeq i xs :: k' =>
      (match xs with
       | [] => execGen m fuel st k'
       | x :: rest =>
         .ok st (some (.tuple #[.int i, x], .enumSeq (i + 1) rest :: k')))
    | .enumList i ad cur :: k' =>
      (match Heap.get? st.world.heap ad with
       | some (.list xs) =>
         if cur < xs.size then
           .ok st (some (.tuple #[.int i, xs.getD cur .none],
                         .enumList (i + 1) ad (cur + 1) :: k'))
         else execGen m fuel st k'
       | some _ => .unsupported "internal: an enumerate cursor over a non-list object (report this)"
       | Option.none => .unsupported danglingMsg)
    | .countFrom cur step :: k' =>
      -- never exhausts: `count` is the infinite ray of sunfish's move
      -- generator, and a consumer's `break` is what ends it
      .ok st (some (.int cur, .countFrom (cur + step) step :: k'))
    | .whileLoop test body orelse :: k' =>
      evalExpr m fuel st test ⤳ fun st t =>
      Run.liftRes st (truthyH st.world.heap t) ⤳ fun st b =>
      if b then
        execGen m fuel st (.block body :: .whileLoop test body orelse :: k')
      else execGen m fuel st (.block orelse :: k')
  termination_by structural fuel

/-- `for target in <generator at `a`>: body` (H4) — the LAZY cursor:
one `stepIter` per iteration, so the generator's effects interleave with
the body's, and `break` simply stops stepping, leaving the generator
SUSPENDED for the next consumer (`gen_lab.two_phase`). Exhaustion ends
the loop. `continue` steps, `return` propagates. A frozen recursion
point, like `execForList`. -/
def execForGen (m : Module) (fuel : Nat) (st : FrameState) (target : Expr)
    (a : Addr) (body : List Stmt) : Run FrameState RFlow :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    Run.withLocals st.locals (stepIter m fuel st.world a) ⤳ fun st r =>
    match r with
    | Option.none => .ok st .next
    | some v =>
      Run.liftRes st (assignToH st.world.heap st.locals target v) ⤳ fun st env₁ =>
      execStmts m fuel { st with locals := env₁ } body ⤳ fun st flow =>
      match flow with
      | .next | .cont => execForGen m fuel st target a body
      | .brk => .ok st .next
      | .ret v => .ok st (.ret v)
  termination_by structural fuel

/-- Drain a generator to EXHAUSTION (H6 draining consumers,
docs/memory-model.md §draining consumers): the yields, in order, for a
full-drain consumer (`sorted`/`max`/`min`). One `stepIter` per element,
so the body's effects interleave into the shared world exactly as lazy
stepping does; the object ends `closed`. Fuel bounds the drain — an
infinite generator is a loud timeout, exactly the divergence CPython
would have. A frozen recursion point, like `stepIter`. -/
def drainIter (m : Module) (fuel : Nat) (w : World) (a : Addr) :
    Run World (List RVal) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    stepIter m fuel w a ⤳ fun w r =>
    match r with
    | Option.none => .ok w []
    | some v =>
      drainIter m fuel w a ⤳ fun w vs => .ok w (v :: vs)
  termination_by structural fuel

/-- Short-circuit drain for `any`/`all` over a generator (H6): step until
the first truthy (`any`) / falsy (`all`) element and STOP — the
generator stays SUSPENDED and resumable, CPython's partial drain
(pinned differentially by an effect-observing generator plus a
post-call `next`). Exhaustion answers the identity (`all` → `true`,
`any` → `false`). A frozen recursion point, like `stepIter`. -/
def anyAllIter (m : Module) (fuel : Nat) (w : World) (a : Addr)
    (isAll : Bool) : Run World Bool :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    stepIter m fuel w a ⤳ fun w r =>
    match r with
    | Option.none => .ok w isAll
    | some v =>
      Run.liftRes w (truthyH w.heap v) ⤳ fun w b =>
      if b != isAll then .ok w b else anyAllIter m fuel w a isAll
  termination_by structural fuel

/-- Invoke a CLOSURE object (H7, docs/memory-model.md §nested defs and
closures): the callee env is parameters bound to arguments, THEN the
snapshot (parameters shadow captures). Mirrors `callIn`'s refusals and
call shape — `callIn`'s covenant signature stays untouched; a GENERATOR
closure allocates the H4 object with the snapshot inside its stored
locals, so resume-time capture reads ride the stepper unchanged. A
frozen recursion point, like `callIn`. -/
def callClosure (m : Module) (fuel : Nat) (w : World) (name : String)
    (params : Array Param) (argsOk localsOk isGenerator : Bool)
    (body : Array Stmt) (captured : REnv) (args : Array RVal) :
    Run World RVal :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    if !argsOk then
      .unsupported s!"nested function '{name}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
    else if !localsOk then
      .unsupported s!"nested function '{name}' calls a name it also assigns (CPython static-locals rule) — outside the tier"
    else if !arityOk params args.size then
      .exn w (.typeError
        s!"{name}() takes {params.size} positional arguments but {args.size} were given")
    else if isGenerator then
      let g : Obj :=
        .generator s!"<closure:{name}>" (mkCallEnv params args ++ captured)
          [.block body.toList] .created
      .ok { w with heap := w.heap.push g } (.ref w.heap.size)
    else
      Run.toWorld <|
        execStmts m fuel ⟨w, mkCallEnv params args ++ captured⟩ body.toList ⤳ fun st flow =>
        match flow with
        | .ret v => .ok st v
        | .next => .ok st .none
        | .brk => .unsupported "'break' outside loop"
        | .cont => .unsupported "'continue' outside loop"
  termination_by structural fuel

end

/-! ## The public boundary (docs/memory-model.md v2, call layering) -/

/-- The fresh `World` of one public call: the module-init heap (G1 dict
literals live here — sunfish's `piece`/`pst`) and the resolved constant
globals. Built afresh per public call, so module-global dicts are shared
across nested calls WITHIN one public call and fresh ACROSS two
(regression case 15). Name resolution reads the static `moduleGlobals`
table — equivalent while bindings are immutable in tier (§G1 section
comment); `World.globals` is the observation-side field and the seam for
the future `global`-statement tier. -/
def initWorld (m : Module) : World :=
  { heap := (moduleInit m).1, globals := resolvedG (moduleGlobals m).1 }

/-- The isolated public observation (signature UNCHANGED — `CallsTo`,
every `@[spec]` raw form, and every existing theorem statement are
literally untouched): create a fresh `World`, **thaw** the boundary
arguments (`Val → RVal` — every mutable-container occurrence freshly
materialized, so the public surface describes exactly the alias-free
argument graphs), run `callIn`, **deep-freeze** the returned value
(`RVal → Res Val`, active-path cycle detection once refs exist), and erase
the world from the public result. NOT the recursion point — nested calls
use `callIn`; proofs unfold this wrapper freely. -/
def callFunction (m : Module) (fname : String) (args : Array Val) (fuel : Nat) : Res Val :=
  Run.toPublic fuel (callIn m fuel (initWorld m) fname (RVal.thawArgs args))

end LeanModels.Python
