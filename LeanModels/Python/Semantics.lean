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

Threading stage (H1-1): the state is threaded but NOTHING allocates yet —
every reachable heap is `#[]`, every `.ref` arm of every helper is loudly
`unsupported`, and observable behavior through `callFunction` is unchanged
(pinned by the differential harness). The dict tier lands on top of this
in H1-proper.

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
  `sortedVal`, `assignTo`, …) that proofs can `simp`-unfold — since H1
  those needing a semantic decision a stage-1 value cannot carry are
  `Res`-valued (`truthy`, `valEq`, `evalCompareOp`: a `.ref`'s truthiness/
  equality needs the heap) — plus a mutual block of the normative
  functions (`evalExpr`, `execStmt`, `execStmts`, `callIn`) and the fueled
  chain helpers (`evalExprs`, `evalBoolChain`, `evalCompareChain`,
  `execWhile`, `execFor`).

Tier-boundary decisions refining DESIGN.md (Python supports these, the
tier does not — so they are `unsupported`, never a fake `TypeError`):
sequence repetition (`"a" * 2`), `%` string formatting, `str` unpacking
(`a, b = "xy"`), nested/starred unpacking targets, `break`/`continue`
escaping a function body, negative `**` exponents (incl. `0 ** -1`),
referencing a function (or a builtin — `len`/`sorted`) as a value, calling a
non-`Name` expression, `is`/`is not` without a `None` side (identity is not
value-determined), non-literal parameter defaults, `sorted` on anything but
an all-int list (see `sortedVal`), and — stage H1-1 only — every operation
on a heap `.ref` (none can exist yet; the arms are the loud frontier the
dict tier replaces).

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
BEFORE building an error message from `typeName`. -/
def RVal.typeName : RVal → String
  | .none => "NoneType"
  | .bool _ => "bool"
  | .int _ => "int"
  | .str _ => "str"
  | .listV _ => "list"
  | .tuple _ => "tuple"
  | .ref _ => "object"

/-- Is this runtime value one of the value-sequence types
(`str`/`listV`/`tuple`)? -/
def RVal.isSeq : RVal → Bool
  | .str _ | .listV _ | .tuple _ => true
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
  | .ref _ => .unsupported
      "truthiness of a heap object is outside the stage-1 tier (dict truthiness lands with H1-proper, docs/memory-model.md)"

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
    | .ref _, _ => .unsupported
        "'==' on a heap object is outside the stage-1 tier (dict equality lands with H1-proper, docs/memory-model.md)"
    | _, .ref _ => .unsupported
        "'==' on a heap object is outside the stage-1 tier (dict equality lands with H1-proper, docs/memory-model.md)"
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
      | .ref _, b =>
        .unsupported
          s!"comparison '{op.symbol}' on a heap object is outside the stage-1 tier ({b.typeName} rhs; docs/memory-model.md)"
      | a, .ref _ =>
        .unsupported
          s!"comparison '{op.symbol}' on a heap object is outside the stage-1 tier ({a.typeName} lhs; docs/memory-model.md)"
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
    | op, .ref _, _ =>
        .unsupported
          s!"binary '{op.symbol}' on a heap object is outside the stage-1 tier (docs/memory-model.md)"
    | op, _, .ref _ =>
        .unsupported
          s!"binary '{op.symbol}' on a heap object is outside the stage-1 tier (docs/memory-model.md)"
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
        .unsupported "unary '-' on a heap object is outside the stage-1 tier (docs/memory-model.md)"
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
  | .ref _ =>
      .unsupported "len() of a heap object is outside the stage-1 tier (dict len lands with H1-proper, docs/memory-model.md)"
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

/-- All-int extraction: `some ns` iff every element is `.int`. `.bool`s
deliberately do NOT coerce here — CPython sorts `[True, 0, 2]` keeping the
`True` object in the result, which the identity-free `.int` cannot
reproduce faithfully; such lists are refused loudly by `sortedVal`. -/
def asIntList : List RVal → Option (List Int)
  | [] => some []
  | .int n :: vs => (asIntList vs).map (n :: ·)
  | _ => Option.none

/-- `sorted(v)`: a NEW ascending list from an all-int list argument.
Honesty discipline (same as `lenVal`): fake exceptions never, `unsupported`
for anything CPython would handle differently.
* `.listV` of `.int`s → `.ok`, freshly sorted (`sortInts`); the input value
  is untouched.
* `.int`/`.bool`/`.none` → `TypeError` with CPython 3.9's exact class and
  message shape (`'int' object is not iterable`).
* `.str`/`.tuple`, and any list containing a non-`.int` element, refuse
  loudly: CPython *succeeds* on `sorted("cba")` / `sorted((3,1))` /
  all-str/bool lists (and TypeErrors only on mixed) — the tier does not
  guess. A `.ref` argument (sorted over dict keys) is a heap read — loud.
* `key=`/`reverse=` never reach here: keyword-only in 3.9, so the extractor
  ships such calls with `call_unsupported: "keywords"` (refused in
  `evalExpr` before argument evaluation). -/
def sortedVal : RVal → Res RVal
  | .listV xs =>
    match asIntList xs.toList with
    | some ns => .ok (.listV (((sortInts ns).map RVal.int).toArray))
    | Option.none =>
        .unsupported "sorted() on a list with non-int elements is outside the v0 tier"
  | .str _ => .unsupported "sorted() on a str is outside the v0 tier"
  | .tuple _ => .unsupported "sorted() on a tuple is outside the v0 tier"
  | .ref _ =>
      .unsupported "sorted() on a heap object is outside the stage-1 tier (docs/memory-model.md)"
  | v => .exn (.typeError s!"'{v.typeName}' object is not iterable")

/-- Left fold of `max`/`min` over ints (structural — kernel-reducible). -/
def foldExtremum (isMax : Bool) (acc : Int) : List Int → Int
  | [] => acc
  | n :: rest => foldExtremum isMax (if isMax then max acc n else min acc n) rest

/-- The `max`/`min` builtins (B1 tier): ≥ 2 int arguments, or one nonempty
int list/tuple. `key=`/`default=` are keyword arguments (refused upstream by
`call_unsupported`). Mixed/bool/str orderings are out of tier — loud, since
`asIntList` admits pure ints only; Python-invalid argument shapes raise the
faithful CPython error class; a `.ref` argument is a heap read — loud. -/
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
      | Option.none => .unsupported s!"{name}() over non-int elements is outside the v0 tier"
    | .tuple xs =>
      match asIntList xs.toList with
      | some (n :: rest) => .ok (.int (foldExtremum isMax n rest))
      | some [] => .exn (.valueError s!"{name}() arg is an empty sequence")
      | Option.none => .unsupported s!"{name}() over non-int elements is outside the v0 tier"
    | .str _ => .unsupported s!"{name}() over a str is outside the v0 tier"
    | .ref _ =>
        .unsupported s!"{name}() over a heap object is outside the stage-1 tier (docs/memory-model.md)"
    | v => .exn (.typeError s!"'{v.typeName}' object is not iterable")
  | vs =>
    match asIntList vs with
    | some (n :: rest) => .ok (.int (foldExtremum isMax n rest))
    | _ => .unsupported s!"{name}() over non-int arguments is outside the v0 tier"

/-- The `abs` builtin (B1): int/bool argument; a `.ref` is refused loudly
before the `TypeError` fallback. -/
def absVal : RVal → Res RVal
  | .int n => .ok (.int (if n < 0 then -n else n))
  | .bool b => .ok (.int (if b then 1 else 0))
  | .ref _ =>
      .unsupported "abs() of a heap object is outside the stage-1 tier (docs/memory-model.md)"
  | v => .exn (.typeError s!"bad operand type for abs(): '{v.typeName}'")

/-- The `int` constructor builtin (B1): identity on ints, bool coercion.
`int(str)` (parsing) and floats are out of tier; a `.ref` is refused loudly
before the `TypeError` fallback. -/
def intCastVal : RVal → Res RVal
  | .int n => .ok (.int n)
  | .bool b => .ok (.int (if b then 1 else 0))
  | .str _ => .unsupported "int() of a str is outside the v0 tier"
  | .ref _ =>
      .unsupported "int() of a heap object is outside the stage-1 tier (docs/memory-model.md)"
  | v => .exn (.typeError s!"int() argument must be a string, a bytes-like object or a real number, not '{v.typeName}'")

/-- Builtin names the interpreter implements (resolution: shadowable by
locals, module globals, and module `def`s, exactly like CPython builtins). -/
def isBuiltinName (id : String) : Bool :=
  id == "len" || id == "sorted" || id == "max" || id == "min" ||
  id == "abs" || id == "int"

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
      .unsupported "a heap object as a subscript index is outside the stage-1 tier (docs/memory-model.md)"
  | .ref _, _ =>
      .unsupported "subscripting a heap object is outside the stage-1 tier (dict reads land with H1-proper, docs/memory-model.md)"
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
  | .str s, index =>
    match asInt index with
    | some i =>
      match normIndex i s.length with
      | some n => .ok (.str (String.singleton (s.toList.getD n ' ')))
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"string indices must be integers, not {index.typeName}")
  | v, _ => .exn (.typeError s!"'{v.typeName}' object is not subscriptable")

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
    | .listV _ => false
    | .ref _ => false

  /-- Elementwise `hashableKey`. -/
  def hashableKeyList : List RVal → Bool
    | [] => true
    | v :: vs => hashableKey v && hashableKeyList vs
end

/-- CPython's type name in `unhashable type: '…'` messages. A `.ref` names
its referent's type — every H1 heap object is a dict. -/
def RVal.unhashName : RVal → String
  | .ref _ => "dict"
  | v => v.typeName

mutual
  /-- No `.ref` anywhere inside the value. The `==` fast path: ref-free
  pairs decide by the PURE `valEq` (fuel-independent), so symbolic
  execution never opens the fueled `heapEq` on ordinary values — `heapEq`
  is a frozen recursion point (its fueled unfolding on symbolic operands
  is unbounded, the `execWhile` situation exactly). -/
  def RVal.refFree : RVal → Bool
    | .none | .bool _ | .int _ | .str _ => true
    | .tuple xs => RVal.refFreeList xs.toList
    | .listV xs => RVal.refFreeList xs.toList
    | .ref _ => false

  /-- Elementwise `RVal.refFree`. -/
  def RVal.refFreeList : List RVal → Bool
    | [] => true
    | v :: vs => RVal.refFree v && RVal.refFreeList vs
end

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
    | _, _ => false

  /-- Elementwise `keyEq`; `false` on length mismatch. -/
  def keyEqList : List RVal → List RVal → Bool
    | [], [] => true
    | a :: as, b :: bs => keyEq a b && keyEqList as bs
    | _, _ => false
end

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
already evaluated by the caller). -/
def dictBuild (acc : List (RVal × RVal)) : List (RVal × RVal) → Res (List (RVal × RVal))
  | [] => .ok acc
  | (k, v) :: rest =>
    if hashableKey k then dictBuild (dictStore acc k v).1 rest
    else .exn (.typeError s!"unhashable type: '{k.unhashName}'")

/-- `d[k]` on a heap dict: unhashable keys raise BEFORE any scan (even on
an empty dict); a missing key is a faithful `KeyError`. -/
def heapIndex (h : Heap) (a : Addr) (k : RVal) : Res RVal :=
  if hashableKey k then
    match Heap.get? h a with
    | some (.dict es _) =>
      match dictFind es.toList k with
      | some v => .ok v
      | Option.none => .exn .keyError
    | Option.none => .unsupported danglingMsg
  else .exn (.typeError s!"unhashable type: '{k.unhashName}'")

/-- `d[k] = v` on a heap dict: value replacement keeps the shape version;
insertion increments it (`dictStore`'s growth bit). -/
def heapStore (h : Heap) (a : Addr) (k v : RVal) : Res Heap :=
  if hashableKey k then
    match Heap.get? h a with
    | some (.dict es ver) =>
      match dictStore es.toList k v with
      | (es', grew) =>
        match Heap.update h a (.dict es'.toArray (if grew then ver + 1 else ver)) with
        | some h' => .ok h'
        | Option.none => .unsupported danglingMsg
    | Option.none => .unsupported danglingMsg
  else .exn (.typeError s!"unhashable type: '{k.unhashName}'")

/-- `len(d)` on a heap dict. -/
def heapLen (h : Heap) (a : Addr) : Res RVal :=
  match Heap.get? h a with
  | some (.dict es _) => .ok (.int es.size)
  | Option.none => .unsupported danglingMsg

/-- `k in d` on a heap dict (unhashable probes raise, empty dict included). -/
def heapContains (h : Heap) (a : Addr) (k : RVal) : Res Bool :=
  if hashableKey k then
    match Heap.get? h a with
    | some (.dict es _) => .ok (dictFind es.toList k).isSome
    | Option.none => .unsupported danglingMsg
  else .exn (.typeError s!"unhashable type: '{k.unhashName}'")

/-- `d.get(k)` / `d.get(k, default)` (the H1 method tier): absent keys
yield the default, never `KeyError`; unhashable probes still raise. -/
def heapGet (h : Heap) (a : Addr) (k dflt : RVal) : Res RVal :=
  if hashableKey k then
    match Heap.get? h a with
    | some (.dict es _) => .ok ((dictFind es.toList k).getD dflt)
    | Option.none => .unsupported danglingMsg
  else .exn (.typeError s!"unhashable type: '{k.unhashName}'")

/-- Truthiness including heap objects: `bool(d)` is `len(d) != 0`. Non-ref
values decide exactly as the pure `truthy` (the proof layer's vocabulary —
`truthyH_of_truthy` lifts pure facts, so VC rule hypotheses never mention
the heap). -/
def truthyH (h : Heap) : RVal → Res Bool
  | .ref a =>
    match Heap.get? h a with
    | some (.dict es _) => .ok (es.size != 0)
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
          | _, _ => .unsupported danglingMsg
      | .ref _, _ => .ok false
      | _, .ref _ => .ok false
      | .tuple xs, .tuple ys => heapEqList h fuel active xs.toList ys.toList
      | .listV xs, .listV ys => heapEqList h fuel active xs.toList ys.toList
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

/-- The heap-aware comparison step (`evalCompareChain` consumes this since
H1-proper). `==`/`!=` go through `heapEq`; `is`/`is not` decide the `None`
link (as before), ref/ref address identity, and ref-vs-immediate `False`
faithfully — refusing only identity between two non-`None` immediates
(implementation-defined); `in`/`not in` are dict membership (value
containers stay loud — the H1 inventory is dicts only); ordering delegates
to the pure `evalCompareOp`. -/
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
  | .inOp =>
    match b with
    | .ref d => heapContains h d a
    | .listV _ | .tuple _ | .str _ =>
      .unsupported s!"'in' on '{b.typeName}' is outside this tier (dict membership only at H1)"
    | b => .exn (.typeError s!"argument of type '{b.typeName}' is not iterable")
  | .notIn =>
    match b with
    | .ref d => do let e ← heapContains h d a; return !e
    | .listV _ | .tuple _ | .str _ =>
      .unsupported s!"'not in' on '{b.typeName}' is outside this tier (dict membership only at H1)"
    | b => .exn (.typeError s!"argument of type '{b.typeName}' is not iterable")
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
  | .listV _, .ref _ => .exn (.typeError "list indices must be integers, not dict")
  | .tuple _, .ref _ => .exn (.typeError "tuple indices must be integers, not dict")
  | .str _, .ref _ => .exn (.typeError "string indices must be integers, not dict")
  | c, i => indexVal c i

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
tier; unpacking a `.ref` iterates the heap object — loud until H1-proper).
Environment-only in stage H1-1: subscript stores (`d[k] = v`, a heap write)
stay loud and make this state-aware at H1-proper. -/
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
      | .str _ => .unsupported "unpacking a str is outside the v0 tier"
      | .ref _ =>
          .unsupported "unpacking a heap object is outside the stage-1 tier (docs/memory-model.md)"
      | v => .exn (.typeError s!"cannot unpack non-iterable {v.typeName} object")
  | .subscript .. => .unsupported "assignment to a subscript is outside the v0 tier"
  | t => .unsupported s!"assignment target '{t.kindName}' is outside the v0 tier"

/-- Module function table lookup. Each `def` rebinds the module-level name, so
with duplicate definitions the LAST one wins, exactly as in CPython. -/
def findFunction (m : Module) (fname : String) : Option FunctionDefn :=
  m.functions.findRev? (fun f => f.name == fname)

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
* a top-level statement that could bind names invisibly (`import`,
  `ClassDef`, `for`, `if`, chained/starred targets, …) marks the globals
  **incomplete**: from then on a name miss is `unsupported` instead of
  `NameError`, because CPython might have bound it;
* module init is evaluated at the fixed fuel `globalFuel` — independent of
  the caller's fuel, so results never vary across call sites and fuel
  monotonicity is untouched. A hypothetical constant needing deeper
  evaluation times out into the `none` (out-of-tier) marking, loudly. -/

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
        let (h, vs) ← evalGlobalExprs h gs fuel elts.toList
        return (h, .listV vs.toArray)
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
        let entries ← dictBuild [] items
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

/-- The resolved (in-tier) globals as a runtime env (drops the out-of-tier
markers). Shadowed earlier bindings are harmless: `Env.lookup` also takes
the first match. -/
def resolvedG : GlobalsAcc → REnv
  | [] => []
  | (k, some v) :: rest => (k, v) :: resolvedG rest
  | (_, Option.none) :: rest => resolvedG rest

/-- All-names view of a tuple target's elements. -/
def targetNamesG : List Expr → Option (List String)
  | [] => some []
  | .name id _ :: rest => (targetNamesG rest).map (id :: ·)
  | _ => Option.none

/-- One module-level statement's effect on the init heap and the globals.
`(h, acc, complete)`: `complete = false` once any statement could have
bound a name invisibly. A failed RHS binds its names out-of-tier AND
discards its partial allocations (the original heap rides through — no
refs escape a refusal). -/
def globalsStep (h : Heap) (acc : GlobalsAcc) (complete : Bool) :
    Stmt → Heap × GlobalsAcc × Bool
  | .assign tgts rhs _ =>
    match tgts.toList with
    | [.name id _] =>
      match evalGlobalExpr h (resolvedG acc) globalFuel rhs with
      | .ok (h', v) => (h', (id, some v) :: acc, complete)
      | _ => (h, (id, Option.none) :: acc, complete)
    | [.tuple es _] =>
      match targetNamesG es.toList with
      | some ids =>
        match evalGlobalExpr h (resolvedG acc) globalFuel rhs with
        | .ok (h', .tuple vs) =>
          if ids.length == vs.size then
            (h', (ids.zip (vs.toList.map some)).reverse ++ acc, complete)
          else (h, ids.map (·, Option.none) ++ acc, complete)
        | .ok (h', .listV vs) =>
          if ids.length == vs.size then
            (h', (ids.zip (vs.toList.map some)).reverse ++ acc, complete)
          else (h, ids.map (·, Option.none) ++ acc, complete)
        | _ => (h, ids.map (·, Option.none) ++ acc, complete)
      | Option.none => (h, acc, false)
    | _ => (h, acc, false)
  | .exprStmt _ _ => (h, acc, complete)
  | .pass _ => (h, acc, complete)
  | _ => (h, acc, false)

/-- Fold `globalsStep` over the top-level statements (source order). -/
def globalsFold (h : Heap) (acc : GlobalsAcc) (complete : Bool) :
    List Stmt → Heap × GlobalsAcc × Bool
  | [] => (h, acc, complete)
  | s :: rest =>
    match globalsStep h acc complete s with
    | (h', acc', complete') => globalsFold h' acc' complete' rest

/-- The whole module-init result: the init heap, the accumulator, and the
completeness flag — a pure function of the module (fixed `globalFuel`). -/
def moduleInit (m : Module) : Heap × GlobalsAcc × Bool :=
  globalsFold #[] [] true m.topLevel.toList

/-- The module's constant globals: `(bindings, complete)` — the static
name-resolution table (see the section comment for why static reads are
faithful). -/
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
    | .call f args _ _ => f.heapFree && Expr.heapFreeList args.toList
    | .list es _ => Expr.heapFreeList es.toList
    | .tuple es _ => Expr.heapFreeList es.toList
    | .subscript v i _ => v.heapFree && i.heapFree
    | .dict .. => false                 -- ALLOCATES
    | .attribute v _ _ => v.heapFree    -- tier: read-only (`.get`)
    | .unsupported .. => true           -- loud, never decides `.ok`

  /-- Elementwise `Expr.heapFree`. -/
  def Expr.heapFreeList : List Expr → Bool
    | [] => true
    | e :: es => e.heapFree && Expr.heapFreeList es
end

mutual
  /-- Does executing this statement provably preserve the world? -/
  def Stmt.heapFree : Stmt → Bool
    | .ret Option.none _ => true
    | .ret (some e) _ => e.heapFree
    | .assign tgts v _ =>
      (match tgts.toList with
       | [.subscript ..] => false       -- MUTATES (`d[k] = v`)
       | _ => true) && v.heapFree
    | .augAssign _ _ v _ => v.heapFree
    | .whileLoop t body orelse _ =>
      t.heapFree && Stmt.heapFreeList body.toList && Stmt.heapFreeList orelse.toList
    | .forStmt _ iter body orelse _ =>
      iter.heapFree && Stmt.heapFreeList body.toList && Stmt.heapFreeList orelse.toList
    | .ifStmt t body orelse _ =>
      t.heapFree && Stmt.heapFreeList body.toList && Stmt.heapFreeList orelse.toList
    | .exprStmt e _ => e.heapFree
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

/-- Module-level heap freedom: every function body (nested calls then stay
inside the fragment). Top-level statements are NOT constrained — they run
only at module init, before any public run begins. -/
def Module.heapFree (m : Module) : Bool :=
  funsHeapFree m.functions.toList

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
  exact funsHeapFree_mem hm hmem

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
          else if isBuiltinName id then
            .unsupported s!"referencing builtin '{id}' as a value is outside the v0 tier"
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
    | .call f args callUnsupported _ =>
      match callUnsupported with
      | some reason => .unsupported s!"call uses unsupported features: {reason}"
      | Option.none =>
        match f with
        | .name fname _ =>
          -- The callee NAME is resolved before the arguments (an unbound name
          -- is a NameError without evaluating args, CPython order), but the
          -- callable CHECK happens at call time, AFTER argument evaluation:
          -- `x(1//0)` with `x = 5` raises ZeroDivisionError, not TypeError.
          match Env.lookup st.locals fname with
          | some (.ref _) =>
              -- every H1 heap object is a dict, and dicts are not
              -- callable: the faithful TypeError (H3 instances revisit
              -- this arm — instance callability lives in the heap)
              evalExprs m fuel st args.toList ⤳ fun st _ =>
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
              .unsupported s!"calling module-level '{fname}' (out-of-G1-tier value) is outside the v0 tier"
            | Option.none =>
            if (findFunction m fname).isSome then
              evalExprs m fuel st args.toList ⤳ fun st vs =>
              -- The frozen recursion point: the callee shares this frame's
              -- world; the caller's locals ride around the call.
              Run.withLocals st.locals (callIn m fuel st.world fname vs.toArray)
            else if fname == "len" then
              evalExprs m fuel st args.toList ⤳ fun st vs =>
              match vs with
              | [v] => Run.liftRes st (lenValH st.world.heap v)
              | _ => .exn st (.typeError s!"len() takes exactly one argument ({vs.length} given)")
            else if fname == "sorted" then
              -- After `findFunction`, so a module-level `def sorted` shadows
              -- the builtin, exactly as CPython's module globals do.
              evalExprs m fuel st args.toList ⤳ fun st vs =>
              match vs with
              | [v] => Run.liftRes st (sortedVal v)
              | _ => .exn st (.typeError s!"sorted expected 1 argument, got {vs.length}")
            else if fname == "max" then
              evalExprs m fuel st args.toList ⤳ fun st vs =>
              Run.liftRes st (extremumVal true vs)
            else if fname == "min" then
              evalExprs m fuel st args.toList ⤳ fun st vs =>
              Run.liftRes st (extremumVal false vs)
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
            else if (moduleGlobals m).2 then
              .exn st (.nameError fname)
            else
              .unsupported s!"name '{fname}' may be bound by an out-of-tier module-level statement"
        | .attribute recv attr _ =>
          -- Method calls (H1 tier: exactly `d.get(k)`/`d.get(k, default)`).
          -- CPython order: receiver (and its attribute lookup) BEFORE the
          -- arguments; both arguments evaluate before `.get` decides.
          if attr == "get" then
            evalExpr m fuel st recv ⤳ fun st r =>
            match r with
            | .ref a =>
              evalExprs m fuel st args.toList ⤳ fun st vs =>
              match vs with
              | [k] => Run.liftRes st (heapGet st.world.heap a k .none)
              | [k, d] => Run.liftRes st (heapGet st.world.heap a k d)
              | vs => .exn st (.typeError s!"get expected at most 2 arguments, got {vs.length}")
            | r =>
              .unsupported s!"method call '.get' on '{r.typeName}' is outside the H1 tier (dict receivers only, docs/memory-model.md)"
          else
            .unsupported s!"method '.{attr}()' is outside the H1 tier (only dict '.get'; docs/memory-model.md)"
        | f => .unsupported s!"calling a non-name expression ('{f.kindName}') is outside the v0 tier"
    | .list elts _ =>
        evalExprs m fuel st elts.toList ⤳ fun st vs =>
        .ok st (.listV vs.toArray)
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
        Run.liftRes st (dictBuild [] items) ⤳ fun st entries =>
        .ok { st with world :=
                { st.world with heap := st.world.heap.push (.dict entries.toArray 0) } }
          (.ref st.world.heap.size)
    | .attribute .. =>
      .unsupported "attribute access as a value is outside the H1 tier (only 'd.get(…)' method calls; heap layer H1/H3, docs/memory-model.md)"
    | .unsupported pyKind _ _ => .unsupported s!"unsupported expression '{pyKind}'"

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
      | [t] =>
          -- CPython order: the value is evaluated before the store.
          evalExpr m fuel st value ⤳ fun st v =>
          Run.liftRes st (assignTo st.locals t v) ⤳ fun st env' =>
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
              "augmented assignment to a heap object is outside the stage-1 tier (docs/memory-model.md)"
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
        | .str _ => .unsupported "'for' over a str is outside the v0 tier"
        | .ref _ =>
            .unsupported "'for' over a heap object is outside the stage-1 tier (live dict iteration lands with H1-proper, docs/memory-model.md)"
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
    | .pass _ => .ok st .next
    | .brk _ => .ok st .brk
    | .cont _ => .ok st .cont
    | .unsupported pyKind _ _ => .unsupported s!"unsupported statement '{pyKind}'"

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
        Run.liftRes st (assignTo st.locals target x) ⤳ fun st env₁ =>
        execStmts m fuel { st with locals := env₁ } body ⤳ fun st flow =>
        match flow with
        | .next | .cont => execFor m fuel st target rest body
        | .brk => .ok st .next
        | .ret v => .ok st (.ret v)

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
      else
        Run.toWorld <|
          execStmts m fuel ⟨w, mkCallEnv f.params args⟩ f.body.toList ⤳ fun st flow =>
          match flow with
          | .ret v => .ok st v
          | .next => .ok st .none
          | .brk => .unsupported "'break' outside loop"
          | .cont => .unsupported "'continue' outside loop"

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
  Run.toPublic (callIn m fuel (initWorld m) fname (RVal.thawArgs args))

end LeanModels.Python
