-- PARTLY LEGACY, and the split matters: this file holds BOTH the pre-rebuild
-- INTERPRETER (evalExpr/execStmt/callIn/execGen…) — legacy, the statement
-- target of pre-rebuild theorems, no new consumers, deleted when re-founded —
-- AND every PURE WORKER (evalBinOp, indexValH, sliceVal, truthyH, assignToH,
-- the string/render/sort workers). The workers are NOT legacy: the monadic
-- interpreter imports them, deliberately, so the rebuild owns the control and
-- the trunk owns the arithmetic. Marking the whole file legacy would be false.
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
heap-list repetition (`[1] * 2`), `%` string formatting, `str` unpacking
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
  | .ellipsis => "ellipsis"
  | .bool _ => "bool"
  | .int _ => "int"
  | .float _ => "float"
  | .str _ => "str"
  | .bytes _ => "bytes"
  | .range _ _ _ => "range"
  | .list _ => "list"
  | .tuple _ => "tuple"

/-- Python type name of a runtime value. A `.ref`'s real type name lives in
the heap (H1-proper resolves it there); the `"object"` placeholder is never
part of a *decided* outcome — every helper refuses `.ref` operands loudly
BEFORE building an error message from `typeName`. A namedtuple names its
own class (`Move`), exactly as CPython error messages do. -/
def RVal.typeName : RVal → String
  | .none => "NoneType"
  | .ellipsis => "ellipsis"
  | .bool _ => "bool"
  | .int _ => "int"
  | .float _ => "float"
  | .str _ => "str"
  | .bytes _ => "bytes"
  | .listV _ => "list"
  | .tuple _ => "tuple"
  | .ntuple tn _ _ => tn
  | .rangeV .. => "range"
  | .ref _ => "object"

/-- Is this runtime value one of the value-sequence types
(`str`/`listV`/`tuple`/namedtuple)? Namedtuples ARE tuples in CPython
(sequence protocol included), so they answer `true` — multiplication
dispatches the sequence protocol before the numeric fallback. -/
def RVal.isSeq : RVal → Bool
  | .str _ | .bytes _ | .listV _ | .tuple _ => true
  | .ntuple _ _ _ => true
  | _ => false

/-! ### Ranges (pass 3, docs/memory-model.md §module-init execution)

A range is an IMMUTABLE, re-iterable sequence, carried as the immediate
`RVal.rangeV` and MATERIALIZED per use — exact because nothing can
mutate it between uses. The materialization budget is a FIXED constant
(never the fuel), so refusing an over-budget range is `unsupported` —
fuel-independent, per the loudness doctrine — and the helpers stay
fuel-free (`Run.le_refl` in every meta-proof arm). -/

/-- Elements a range yields (CPython's exact length formula — the
`sliceCount` shape; `step ≠ 0` by construction of `rangeV`). -/
def rangeLen (lo hi step : Int) : Nat :=
  if 0 < step then
    if lo < hi then ((hi - lo - 1) / step).toNat + 1 else 0
  else
    if hi < lo then ((lo - hi - 1) / (-step)).toNat + 1 else 0

/-- Collect `n` ints from `cur`, stepping. Structural (kernel-reducible). -/
def rangeValsAux : Nat → Int → Int → List RVal
  | 0, _, _ => []
  | n + 1, cur, step => .int cur :: rangeValsAux n (cur + step) step

/-- The fixed materialization budget (a million elements). A constant on
purpose: budget-refusals must be fuel-INDEPENDENT (`unsupported`, never
a fuel-varying outcome). -/
def seqBudget : Nat := 1048576

/-- The pinned CPython 3.9 `Py_ssize_t` magnitude on the 64-bit oracle.
Repetition may short-circuit an empty/nonpositive result only after this
index-sized conversion would succeed. -/
def seqIndexBudget : Nat := 9223372036854775807

/-- The left-shift budget: the largest shift COUNT `<<` will build, so the
widest result is about a million bits (128 KB). Its own constant rather
than a reuse of `seqBudget` — they bound different resources and the
backlog recorded this as its own budget decision — but the same
discipline: fixed, therefore fuel-INDEPENDENT.

Why any bound at all (docs/memory-model.md §left shift and bitwise or):
`x << n` is `x * 2^n` with nothing limiting `n`, and the arm was reachable
with an arbitrary `n`. Measured 2026-08-15 on this toolchain,
`1 << (10^30)` did not compute and did not refuse — it died
`INTERNAL PANIC: Nat.pow exponent is too big`, a runner abort rather than
an answer. Below the budget nothing changes and CPython is matched
exactly; above it the model says so LOUDLY. Note this refuses some shifts
CPython performs happily (`1 << 10^9` is a real 125 MB integer there): a
declared tier gap, never a claim that CPython raises. -/
def shiftBudget : Nat := 1048576

/-- A conservative count at which CPython 3.9 reports `OverflowError: too many
integer digits` before attempting an impossible left-shift allocation. Counts
between `shiftBudget` and this guard remain loud tier refusals. -/
def shiftOverflowBudget : Nat := 100000000000000000000

/-- The largest negative integer exponent whose reciprocal power is built as
an exact integer ratio before binary64 rounding. Larger exponents remain loud
rather than forcing an unbounded kernel `Int.pow`. -/
def floatPowBudget : Nat := 1024

/-- The number of bits needed to represent an integer's magnitude. -/
def intBitLength (value : Int) : Nat :=
  if value = 0 then 0 else value.natAbs.log2 + 1

/-- Materialize a range value, budget-guarded (see the section comment). -/
def rangeVals (lo hi step : Int) : Res (List RVal) :=
  let n := rangeLen lo hi step
  if n ≤ seqBudget then .ok (rangeValsAux n lo step)
  else .unsupported "materializing a range beyond seqBudget is outside the tier (docs/memory-model.md §module-init execution)"

/-- CPython's range equality compares the produced integer sequence, not the
constructor spelling. Empty ranges are all equal; a singleton only compares
its first value; longer ranges additionally require equal length and step. -/
def rangeEq (alo ahi astep blo bhi bstep : Int) : Bool :=
  let an := rangeLen alo ahi astep
  let bn := rangeLen blo bhi bstep
  if an == 0 then
    bn == 0
  else if bn == 0 then
    false
  else if alo != blo then
    false
  else if an == 1 then
    bn == 1
  else
    an == bn && astep == bstep

def rangeContainsInt (lo hi step value : Int) : Bool :=
  if 0 < step then
    lo ≤ value && value < hi && (value - lo) % step == 0
  else
    hi < value && value ≤ lo && (lo - value) % (-step) == 0

/-- Is this runtime value Python's `None` singleton? (The value-level test
behind `is None` / `is not None` — see `evalCompareOp`.) A heap object is
never `None`, so the `.ref` arm is a faithful `false`, not a refusal. -/
def RVal.isNone : RVal → Bool
  | .none => true
  | _ => false

def RVal.isEllipsis : RVal → Bool
  | .ellipsis => true
  | _ => false

/-- Python surface syntax of a binary operator (error messages). -/
def BinOp.symbol : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mult => "*"
  | .div => "/"
  | .floorDiv => "//"
  | .mod => "%"
  | .pow => "**"
  | .lshift => "<<"
  | .rshift => ">>"
  | .bitOr => "|"
  | .bitXor => "^"
  | .bitAnd => "&"
  | .matMult => "@"

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
  | .namedExpr .. => "NamedExpr"
  | .constant .. => "Constant"
  | .name .. => "Name"
  | .binOp .. => "BinOp"
  | .unaryOp .. => "UnaryOp"
  | .formattedValue .. => "FormattedValue"
  | .formattedValueAscii .. => "FormattedValue"
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
  | .unpackAssign .. => "UnpackAssign"
  | .augAssign .. => "AugAssign"
  | .whileLoop .. => "While"
  | .forStmt .. => "For"
  | .ifStmt .. => "If"
  | .exprStmt .. => "Expr"
  | .yieldStmt .. => "Yield"
  | .yieldFromStmt .. => "YieldFrom"
  | .defStmt .. => "NestedDef"
  | .raiseStmt .. => "Raise"
  | .assertStmt .. => "Assert"
  | .tryStmt .. => "Try"
  | .withStmt .. => "With"
  | .importFrom .. => "ImportFrom"
  | .delStmt .. => "Delete"
  | .pass _ => "Pass"
  | .brk _ => "Break"
  | .cont _ => "Continue"
  | .unsupported pyKind _ _ => pyKind

/-- A CLOSURE CELL reached a VALUE position (H7 cells,
docs/memory-model.md §nested defs and closures). A cell is an
interpreter-internal heap slot: it is created by a `def` with a
late-bound capture, addressed ONLY through a frame's `<cell>x` env key,
and read ONLY by `cellsFor`, at the closure call. No Python expression
can produce one, so every value-position consumer says so LOUDLY rather
than inventing a type for it. -/
def cellInternal : String :=
  "internal: a closure CELL reached a value position — a cell is never a Python value (unreachable through ingestion; report this)"

/-- Python truthiness `bool(x)`: `None` → false; `bool` → itself;
`int` → `≠ 0`; `str`/`listV`/`tuple` → nonempty. `Res`-valued since H1:
a `.ref`'s truthiness lives in the heap (`bool(d)` is `len(d) != 0`) —
loud until the dict tier reads it there. -/
def truthy : RVal → Res Bool
  | .none => .ok false
  | .ellipsis => .ok true
  | .bool b => .ok b
  | .int n => .ok (n != 0)
  | .float value => .ok (!value.isZero)
  | .str s => .ok (!s.isEmpty)
  | .bytes xs => .ok (xs.size != 0)
  | .listV xs => .ok (xs.size != 0)
  | .tuple xs => .ok (xs.size != 0)
  | .ntuple _ _ xs => .ok (xs.size != 0)
  | .rangeV lo hi step => .ok (rangeLen lo.toInt hi.toInt step.toInt != 0)
  | .ref _ => .unsupported
      "truthiness of a heap object lives in the heap (`truthyH` decides it; this pure helper is the proof-layer vocabulary)"

/- Reserved instance payload used only for the exact literal `__bool__` slice.
It is not a Python-spellable attribute and therefore cannot be observed as
instance data; `truthyH` consumes it before the ordinary default-protocol arm. -/
def instanceBoolMarker : String := "<leanpy:bool-literal>"

/-- Reserved instance payload used only for the exact literal `__eq__` slice.
It is not a Python-spellable attribute. `heapEq` consumes it before the
ordinary identity/default-protocol arm, so a literal custom equality method
also applies when the instance is compared with itself or an immediate. -/
def instanceEqMarker : String := "<leanpy:eq-literal>"

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
    | some (.dictView _ .keys) => "dict_keys"
    | some (.dictView _ .values) => "dict_values"
    | some (.dictView _ .items) => "dict_items"
    -- H3: the class NAME lives in the module, not the heap — "object" is
    -- the message-only placeholder (the harness compares exception CLASS
    -- names, never messages).
    | some (.instance _ _) => "object"
    | some (.generator ..) => "generator"
    -- a CELL is interpreter-internal and never names a Python type; the
    -- message-only placeholder keeps this total (the value-position
    -- consumers all refuse with `cellInternal`).
    | some (.cell _) => "cell"
    | some (.closure ..) => "function"
    | some (.pyset _) => "set"
    | Option.none => "object"
  | v => v.typeName

/-- CPython's byte-limited type names decode a truncated UTF-8 character
with a replacement character. The walk is structural on characters. -/
def typeNamePrefixChars : List Char → Nat → List Char
  | [], _ => []
  | character :: rest, byteLimit =>
      if character.utf8Size ≤ byteLimit then
        character :: typeNamePrefixChars rest (byteLimit - character.utf8Size)
      else if byteLimit = 0 then []
      else ['�']

def typeNamePrefix (name : String) (byteLimit : Nat) : String :=
  String.mk (typeNamePrefixChars name.toList byteLimit)

/-- bool→int coercion (Python's `bool` is an `int` subtype): `int` passes
through, `True`/`False` become `1`/`0`, everything else is `none`. -/
def asInt : RVal → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => Option.none

def rangeContains (lo hi step : Int) (value : RVal) : Bool :=
  match value with
  | .float number =>
    match number.toIntegralInt with
    | some integer => rangeContainsInt lo hi step integer
    | Option.none => false
  | value =>
    match asInt value with
    | some integer => rangeContainsInt lo hi step integer
    | Option.none => false

mutual
  def RVal.hasFloat : RVal → Bool
    | .float _ => true
    | .tuple values | .listV values | .ntuple _ _ values => RVal.hasFloatList values.toList
    | _ => false

  def RVal.hasFloatList : List RVal → Bool
    | [] => false
    | value :: rest => value.hasFloat || RVal.hasFloatList rest
end

mutual
  /-- Whether a value contains a NaN or infinity. Finite floats are
  hashable; non-finite floats remain loud because their immediate
  representation has no object identity for CPython's NaN key shortcut. -/
  def RVal.hasNonFiniteFloat : RVal → Bool
    | .float value => value.isNaN || value.isInf
    | .tuple values | .listV values | .ntuple _ _ values =>
      RVal.hasNonFiniteFloatList values.toList
    | _ => false

  def RVal.hasNonFiniteFloatList : List RVal → Bool
    | [] => false
    | value :: rest => value.hasNonFiniteFloat || RVal.hasNonFiniteFloatList rest
end

/-- Admit integer range fields without erasing their bool subtype. -/
def asRangeBound : RVal → Option RangeBound
  | .int value => some (.int value)
  | .bool value => some (.bool value)
  | _ => Option.none

/-- `range(…)` construction from evaluated arguments: 1–3 int args
(bool objects retained by CPython's `__index__`), `step = 0` the faithful
`ValueError`, wrong arity/types the faithful `TypeError`s. -/
def rangeMake (h : Heap) (vs : List RVal) : Res RVal :=
  -- CPython names the OFFENDING OBJECT's type, never range's requirements,
  -- and it names the FIRST bad argument left to right (measured 3.9.19:
  -- `range([1],[2],[3])` and `range(1,[2],[3])` are both `'list' object
  -- cannot be interpreted as an integer`). The three-argument arm used to
  -- answer `range() arguments must be integers`, which is not a sentence
  -- CPython 3.9 produces. `typeNameH` and not `typeName`: a heap operand
  -- is reachable here (`range({1: 2})` is `'dict' object …`) and the bare
  -- `typeName` would put the `"object"` placeholder into a decided
  -- outcome, which the recorded rule forbids.
  let bad := fun (v : RVal) =>
    Res.exn (α := RVal)
      (.typeError s!"'{RVal.typeNameH h v}' object cannot be interpreted as an integer")
  match vs with
  | [] => .exn (.typeError "range expected at least 1 argument, got 0")
  | [v] =>
    (match asRangeBound v with
     | some n => .ok (.rangeV (.int 0) n (.int 1))
     | Option.none => bad v)
  | [a, b] =>
    (match asRangeBound a, asRangeBound b with
     | some x, some y => .ok (.rangeV x y (.int 1))
     | Option.none, _ => bad a
     | some _, Option.none => bad b)
  | [a, b, c] =>
    (match asRangeBound a, asRangeBound b, asRangeBound c with
     | some x, some y, some z =>
       if z.toInt == 0 then .exn (.valueError "range() arg 3 must not be zero")
       else .ok (.rangeV x y z)
     | Option.none, _, _ => bad a
     | some _, Option.none, _ => bad b
     | some _, some _, Option.none => bad c)
  | vs => .exn (.typeError s!"range expected at most 3 arguments, got {vs.length}")


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
    | .ellipsis, .ellipsis => .ok true
    | .bool a, .bool b => .ok (a == b)
    | .bool a, .int m => .ok ((if a then (1 : Int) else 0) == m)
    | .int n, .bool b => .ok (n == (if b then (1 : Int) else 0))
    | .int n, .int m => .ok (n == m)
    | .float a, .float b =>
        -- IEEE/CPython NaN equality is value-determined: every NaN compares
        -- unequal, including with itself. Payload identity matters for
        -- arithmetic propagation, but never for `==`/`!=`.
        if a.isNaN || b.isNaN then .ok false
        else .ok (a.eqv b)
    | .float a, .int n => .ok (a.eqInt n)
    | .int n, .float a => .ok (a.eqInt n)
    | .float a, .bool b => .ok (a.eqInt (if b then 1 else 0))
    | .bool b, .float a => .ok (a.eqInt (if b then 1 else 0))
    | .str s, .str t => .ok (s == t)
    | .bytes xs, .bytes ys => .ok (xs == ys)
    | .listV xs, .listV ys => valEqList xs.toList ys.toList
    | .tuple xs, .tuple ys => valEqList xs.toList ys.toList
    | .rangeV alo ahi astep, .rangeV blo bhi bstep =>
        .ok (rangeEq alo.toInt ahi.toInt astep.toInt blo.toInt bhi.toInt bstep.toInt)
    -- namedtuples compare as plain tuples (CPython: tuple.__eq__ — the
    -- class is IGNORED, even across two different namedtuple classes)
    | .ntuple _ _ xs, .ntuple _ _ ys => valEqList xs.toList ys.toList
    | .ntuple _ _ xs, .tuple ys => valEqList xs.toList ys.toList
    | .tuple xs, .ntuple _ _ ys => valEqList xs.toList ys.toList
    | .ref _, _ => .unsupported
        "'==' on a heap object lives in the heap (`heapEq` decides it; this pure helper is the proof-layer vocabulary)"
    | _, .ref _ => .unsupported
        "'==' on a heap object lives in the heap (`heapEq` decides it; this pure helper is the proof-layer vocabulary)"
    -- pass 3: range/range equality compares the integer sequence; a range
    -- against another value remains loud because its protocol is separate.
    | .rangeV .., _ => .unsupported
        "'==' on a range against a non-range is outside the tier (docs/memory-model.md §module-init execution)"
    | _, .rangeV .. => .unsupported
        "'==' on a non-range against a range is outside the tier (docs/memory-model.md §module-init execution)"
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

def bytesCmp : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | left :: lefts, right :: rights =>
      if left == right then bytesCmp lefts rights else left < right

def bytesCmpOp (op : CmpOp) (xs ys : Array UInt8) : Bool :=
  let equal := xs == ys
  let less := bytesCmp xs.toList ys.toList
  match op with
  | .eq => equal
  | .notEq => !equal
  | .lt => less
  | .ltE => less || equal
  | .gt => !less && !equal
  | .gtE => !less
  | .is => equal
  | .isNot => !equal
  | .inOp | .notIn => false

def bytesContains (values probe : List UInt8) : Bool :=
  if probe.isPrefixOf values then true
  else match values with
    | [] => false
    | _ :: rest => bytesContains rest probe
termination_by structural values

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
    | .float left, .float right =>
        -- CPython's binary64 comparison is unordered when either operand is
        -- NaN: `<` simply returns False.  The stable sort consumes this same
        -- relation, so NaNs retain their input position without a fabricated
        -- total-order key.
        if left.isNaN || right.isNaN then .ok false else .ok (left.lt right)
    | .float left, .int right =>
        if left.isNaN then .ok false else .ok (left.ltInt right)
    | .int left, .float right =>
        if right.isNaN then .ok false else .ok (Float64.intLt left right)
    | .float left, .bool right =>
        if left.isNaN then .ok false else .ok (left.ltInt (if right then 1 else 0))
    | .bool left, .float right =>
        if right.isNaN then .ok false else .ok (Float64.intLt (if left then 1 else 0) right)
    | .str s, .str t => .ok (strCmp .lt s t)
    | .str _, .int _ => .exn (.typeError "'<' not supported between instances of 'str' and 'int'")
    | .str _, .bool _ => .exn (.typeError "'<' not supported between instances of 'str' and 'bool'")
    | .int _, .str _ => .exn (.typeError "'<' not supported between instances of 'int' and 'str'")
    | .bool _, .str _ => .exn (.typeError "'<' not supported between instances of 'bool' and 'str'")
    | .bytes xs, .bytes ys => .ok (bytesCmp xs.toList ys.toList)
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

def floatOrder (op : CmpOp) (equal less greater : Bool) : Bool :=
  match op with
  | .lt => less
  | .ltE => less || equal
  | .gt => greater
  | .gtE => greater || equal
  | _ => false

def smallIntIdentity (x : Int) : Bool := -5 ≤ x && x ≤ 256

/-- One comparison step. `==`/`!=` are `valEq` (`Res`-valued since H1 — see
there). Identity against `None` or `Ellipsis` is value-determined because
both are singletons. Other immediate identities stay loud (small-int caching,
str interning); `evalCompareOpH` also decides heap references by address.
Ordering: int/bool by value (bool→int coercion), str lexicographic;
ordering any other type combination is outside the tier. -/
def evalCompareOp (op : CmpOp) (a b : RVal) : Res Bool :=
  match op with
  | .eq => valEq a b
  | .notEq => do let e ← valEq a b; return !e
  | .is =>
    if a.isNone || b.isNone then .ok (a.isNone && b.isNone)
    else if a.isEllipsis || b.isEllipsis then .ok (a.isEllipsis && b.isEllipsis)
    else match a, b with
      | .bool x, .bool y => .ok (x == y)
      | .int x, .int y =>
          if smallIntIdentity x && smallIntIdentity y then .ok (x == y)
          else .unsupported s!"'is' between '{a.typeName}' and '{b.typeName}' (identity is not value-determined) is outside the v0 tier"
      | .bool _, .int _ | .int _, .bool _ => .ok false
      | _, _ => .unsupported s!"'is' between '{a.typeName}' and '{b.typeName}' (identity is not value-determined) is outside the v0 tier"
  | .isNot =>
    if a.isNone || b.isNone then .ok (!(a.isNone && b.isNone))
    else if a.isEllipsis || b.isEllipsis then .ok (!(a.isEllipsis && b.isEllipsis))
    else match a, b with
      | .bool x, .bool y => .ok (x != y)
      | .int x, .int y =>
          if smallIntIdentity x && smallIntIdentity y then .ok (x != y)
          else .unsupported s!"'is not' between '{a.typeName}' and '{b.typeName}' (identity is not value-determined) is outside the v0 tier"
      | .bool _, .int _ | .int _, .bool _ => .ok true
      | _, _ => .unsupported s!"'is not' between '{a.typeName}' and '{b.typeName}' (identity is not value-determined) is outside the v0 tier"
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
      | .float left, .float right =>
        .ok (floatOrder op (left.eqv right) (left.lt right) (right.lt left))
      | .float left, .int right =>
        .ok (floatOrder op (left.eqInt right) (left.ltInt right) (Float64.intLt right left))
      | .int left, .float right =>
        .ok (floatOrder op (right.eqInt left) (Float64.intLt left right) (right.ltInt left))
      | .float left, .bool right =>
        let integer := if right then 1 else 0
        .ok (floatOrder op (left.eqInt integer) (left.ltInt integer) (Float64.intLt integer left))
      | .bool left, .float right =>
        let integer := if left then 1 else 0
        .ok (floatOrder op (right.eqInt integer) (Float64.intLt integer right) (right.ltInt integer))
      | .str s, .str t => .ok (strCmp op s t)
      | .bytes xs, .bytes ys => .ok (bytesCmpOp op xs ys)
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

/-- Tuple repetition with fuel-independent bounds on positive nonempty
results. Nonpositive counts short-circuit exactly as CPython does, without
constructing or budgeting the requested magnitude; an oversized count raises
the faithful CPython `OverflowError` before that result can be formed. -/
def tupleRepeat (xs : Array RVal) (count : Int) : Res RVal :=
  if count.natAbs > seqIndexBudget then
    .exn (.overflowError "cannot fit 'int' into an index-sized integer")
  else if count ≤ 0 || xs.isEmpty then
    .ok (.tuple #[])
  else if count.natAbs ≤ seqBudget ∧ xs.size * count.toNat ≤ seqBudget then
    .ok (.tuple ((List.replicate count.toNat xs.toList).flatten.toArray))
  else
    .unsupported "tuple repetition beyond seqBudget is outside the tier (count magnitude or output element count; docs/memory-model.md §tuple repetition)"

/-- Repeat a boundary list snapshot. A `Val.list` argument is represented as
`.listV` by the public wrapper, so this path is immutable from the caller's
point of view: multiplication allocates a fresh list in Python, but no alias
to that fresh result can escape the isolated call except through its returned
snapshot. Heap-backed lists still use the stateful monadic worker. -/
def listValueRepeat (xs : Array RVal) (count : Int) : Res RVal :=
  if count.natAbs > seqIndexBudget then
    .exn (.overflowError "cannot fit 'int' into an index-sized integer")
  else if count ≤ 0 || xs.isEmpty then
    .ok (.listV #[])
  else if count.natAbs ≤ seqBudget ∧ xs.size * count.toNat ≤ seqBudget then
    .ok (.listV ((List.replicate count.toNat xs.toList).flatten.toArray))
  else
    .unsupported "list repetition beyond seqBudget is outside the tier (count magnitude or output element count; docs/memory-model.md §list repetition)"

def bytesRepeat (xs : Array UInt8) (count : Int) : Res RVal :=
  if count.natAbs > seqIndexBudget then
    .unsupported "sequence repetition count does not fit CPython's index-sized integer"
  else if count ≤ 0 || xs.isEmpty then
    .ok (.bytes #[])
  else if count.natAbs ≤ seqBudget ∧ xs.size * count.toNat ≤ seqBudget then
    .ok (.bytes ((List.replicate count.toNat xs.toList).flatten.toArray))
  else
    .unsupported "bytes repetition beyond seqBudget is outside the tier"

/-- String repetition with fuel-independent bounds on positive nonempty
results. Empty strings and nonpositive counts short-circuit exactly as CPython
does, without constructing or budgeting the requested magnitude. -/
def strRepeat (text : String) (count : Int) : Res RVal :=
  if count.natAbs > seqIndexBudget then
    .exn (.overflowError "cannot fit 'int' into an index-sized integer")
  else if count ≤ 0 || text.isEmpty then
    .ok (.str "")
  else if count.natAbs ≤ seqBudget ∧ text.length * count.toNat ≤ seqBudget then
    .ok (.str (String.ofList ((List.replicate count.toNat text.toList).flatten)))
  else
    .unsupported "string repetition beyond seqBudget is outside the tier (count magnitude or output code-point length; docs/memory-model.md §string repetition)"

/-- Repeat an admitted immediate sequence; the count's real Python type
is known before constructing the faithful non-integer `TypeError`. -/
def sequenceRepeat (sequence count : RVal) : Res RVal :=
  match sequence, count with
  | .ref _, _ | _, .ref _ =>
      .unsupported "sequence repetition with a heap object is outside the tier (docs/memory-model.md §string repetition)"
  | _, _ =>
      match asInt count with
      | some number =>
          match sequence with
          | .str text => strRepeat text number
          | .bytes values => bytesRepeat values number
          | .listV values => listValueRepeat values number
          | .tuple values | .ntuple _ _ values => tupleRepeat values number
          | _ => .unsupported "repetition of this sequence is outside the tier"
      | Option.none =>
          .exn (.typeError s!"can't multiply sequence by non-int of type '{typeNamePrefix count.typeName 200}'")

/-- Value-sequence multiplication preserves the left operand's protocol:
`str * tuple` and `tuple * str` name different non-integer counts. -/
def sequenceMult (left right : RVal) : Res RVal :=
  match left, right with
  | .ref _, _ | _, .ref _ =>
      .unsupported "sequence multiplication with a heap object is outside the tier (docs/memory-model.md §string repetition)"
  | .str _, _ | .bytes _, _ | .tuple _, _ | .ntuple _ _ _, _ => sequenceRepeat left right
  | .listV _, _ => sequenceRepeat left right
  | _, .str _ | _, .bytes _ | _, .listV _ | _, .tuple _ | _, .ntuple _ _ _ =>
      sequenceRepeat right left
  | _, _ =>
      if (left.isSeq && (asInt right).isSome) || ((asInt left).isSome && right.isSeq) then
        .unsupported
          s!"sequence repetition ('{left.typeName}' * '{right.typeName}') is outside the v0 tier"
      else
        .exn (.typeError s!"unsupported operand type(s) for *: '{left.typeName}' and '{right.typeName}'")

/-- Fast length for a value-sequence multiplication nested directly under
`len`.  CPython computes the resulting length without materializing the
sequence, so this path deliberately does not apply `seqBudget`; it keeps the
index-sized count conversion and the ordinary sequence `TypeError`s from
`sequenceRepeat`.  `none` means that the heap-aware multiplication path must
run (for example, a heap-backed list). -/
def sequenceMultLength (left right : RVal) : Option (Res RVal) :=
  let repeatSeq (sequence count : RVal) : Res RVal :=
    match sequence, count with
    | .ref _, _ | _, .ref _ =>
        .unsupported "sequence repetition with a heap object is outside the tier (docs/memory-model.md §string repetition)"
    | .str text, _ =>
        match asInt count with
        | some number =>
            if number.natAbs > seqIndexBudget then
              .exn (.overflowError "cannot fit 'int' into an index-sized integer")
            else if number ≤ 0 || text.isEmpty then
              .ok (.int 0)
            else
              .ok (.int (text.length * number.toNat))
        | Option.none =>
            .exn (.typeError s!"can't multiply sequence by non-int of type '{typeNamePrefix count.typeName 200}'")
    | .bytes values, _ =>
        match asInt count with
        | some number =>
            if number.natAbs > seqIndexBudget then
              .unsupported "sequence repetition count does not fit CPython's index-sized integer"
            else if number ≤ 0 || values.isEmpty then
              .ok (.int 0)
            else
              .ok (.int (values.size * number.toNat))
        | Option.none =>
            .exn (.typeError s!"can't multiply sequence by non-int of type '{typeNamePrefix count.typeName 200}'")
    | .listV values, _ | .tuple values, _ | .ntuple _ _ values, _ =>
        match asInt count with
        | some number =>
            if number.natAbs > seqIndexBudget then
              .exn (.overflowError "cannot fit 'int' into an index-sized integer")
            else if number ≤ 0 || values.isEmpty then
              .ok (.int 0)
            else
              .ok (.int (values.size * number.toNat))
        | Option.none =>
            .exn (.typeError s!"can't multiply sequence by non-int of type '{typeNamePrefix count.typeName 200}'")
    | _, _ =>
        .unsupported "repetition of this sequence is outside the tier"
  match left, right with
  | .ref _, _ | _, .ref _ => Option.none
  | .str _, _ | .bytes _, _ | .listV _, _ | .tuple _, _ | .ntuple _ _ _, _ =>
      some (repeatSeq left right)
  | _, .str _ | _, .bytes _ | _, .listV _ | _, .tuple _ | _, .ntuple _ _ _ =>
      some (repeatSeq right left)
  | _, _ => Option.none

/-- `a &&& ~m` over `Nat`. `Nat.ldiff` does not exist in v4.33.0-rc1, and
none is needed: every bit of `a` either is or is not in `m`, so removing
the ones that are IS the difference. Never underflows (the grid instrument
in docs/backlog.md §construct 4 checked 0 underflows over 22201 pairs). -/
def ndiff (a m : Nat) : Nat := a - (a &&& m)

/-- `&` over `Int`, EXACT on negative operands. Nothing is guessed:
Lean's `Int.negSucc n` IS `-(n+1)`, so for a negative `x` the number
`-x-1` — whose bits are the complement of `x`'s — is the constructor's own
argument, available by matching and requiring no arithmetic at all
(docs/memory-model.md §bitwise `&`). -/
def intAnd : Int → Int → Int
  | .ofNat a,   .ofNat b   => .ofNat (a &&& b)
  | .negSucc a, .ofNat b   => .ofNat (ndiff b a)
  | .ofNat a,   .negSucc b => .ofNat (ndiff a b)
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

/-- `|` over `Int`, the same construction. This REPLACES pass 5's negative
refusal, which was a design-time prediction rather than a measurement:
`-1 | 4` has a value (`-1`), it is exact here, and keeping the refusal
would be manufacturing one for a case known to be right. -/
def intOr : Int → Int → Int
  | .ofNat a,   .ofNat b   => .ofNat (a ||| b)
  | .negSucc a, .ofNat b   => .negSucc (ndiff a b)
  | .ofNat a,   .negSucc b => .negSucc (ndiff b a)
  | .negSucc a, .negSucc b => .negSucc (a &&& b)

/-- `^` over `Int`, the same construction — and the simplest of the three,
because XOR commutes with complement. `.negSucc a` IS `~a`, and
`~p ^ q = ~(p ^ q)`, `~p ^ ~q = p ^ q`, so every arm is one `Nat` XOR
whose sign is read off the operands' parity: no `ndiff`, no subtraction,
nothing to underflow. (§L39 rung 1: the tail batch landed `|` and `&`
and left `^` out, with nothing recorded about the omission.) -/
def intXor : Int → Int → Int
  | .ofNat a,   .ofNat b   => .ofNat (a ^^^ b)
  | .negSucc a, .ofNat b   => .negSucc (a ^^^ b)
  | .ofNat a,   .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

/-! ### Scalar rendering (`str()` and a str's `repr`)

These sit HERE, above the operator block, because both users need them
and one of the users is the `%` operator below: `evalBinOp` precedes
§rendering in this file and Lean has no forward references. Moved
verbatim from §rendering, which keeps the heap-recursive `reprVal`/
`printOne`/`strOfValH` built on top of them. -/

/-- The fixed decimal conversion budget used by this tier. CPython 3.9 permits
the process to configure a limit as low as 640 digits; the pinned oracle
uses its default 4300-digit limit, which is the tier's fixed rendering/parsing boundary. -/
def intDigitBudget : Nat := 4300

/-- Decimal integer rendering within the fixed pinned budget,
checked on the magnitude before materializing its digits. Kept opaque to
symbolic simplification so unrelated branches do not expand the digit bound. -/
@[irreducible] def intDecimal (value : Int) : Option String :=
  if value.natAbs < 10 ^ intDigitBudget then some (toString value) else Option.none

/-- CPython's default decimal conversion error at the pinned 4300-digit limit. -/
def decimalLimitError : PyErr :=
  .valueError "Exceeds the limit (4300) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit"

/-- Whether an immediate value is an over-budget decimal integer. -/
def decimalOverflowImmediate : RVal → Bool
  | .int value => (intDecimal value).isNone
  | _ => false

/-! `%s` and `%r` can render the ref-free container values that arrive at a
function through the public boundary. They cannot use the heap-backed
`reprVal` below, so this is a small value-only twin. Keeping it here also
keeps `evalBinOp`'s pure `%` arm pure; heap references continue to refuse at
the operator boundary. -/
def strFormatReprFuel : Nat := 256

def strFormatCommaJoin : List String → String
  | [] => ""
  | [s] => s
  | s :: ss => s ++ ", " ++ strFormatCommaJoin ss

def strFormatZipNames : List String → List String → List String
  | n :: ns, p :: ps => (n ++ "=" ++ p) :: strFormatZipNames ns ps
  | _, _ => []

mutual
  def strFormatImmediateReprOverflow (fuel : Nat) : RVal → Bool
    | .int value => (intDecimal value).isNone
    | .tuple xs | .listV xs | .ntuple _ _ xs =>
      match fuel with
      | 0 => false
      | fuel + 1 => strFormatImmediateReprOverflowList fuel xs.toList
    | .rangeV lo hi step =>
      match fuel with
      | 0 => false
      | fuel + 1 =>
        strFormatImmediateReprOverflow fuel lo.toRVal ||
          strFormatImmediateReprOverflow fuel hi.toRVal ||
          strFormatImmediateReprOverflow fuel step.toRVal
    | _ => false

  def strFormatImmediateReprOverflowList (fuel : Nat) : List RVal → Bool
    | [] => false
    | v :: vs =>
      strFormatImmediateReprOverflow fuel v ||
        strFormatImmediateReprOverflowList fuel vs
end

mutual
  def strFormatImmediateRepr (fuel : Nat) : RVal → Option String
    | .int value => intDecimal value
    | .float value => value.repr
    | .bool b => some (if b then "True" else "False")
    | .none => some "None"
    | .ellipsis => some "Ellipsis"
    | .str text => reprStr text
    | .bytes _ => Option.none
    | .tuple xs =>
      match fuel with
      | 0 => Option.none
      | fuel + 1 => do
        let parts ← strFormatImmediateReprs fuel xs.toList
        if parts.length == 1 then
          return "(" ++ parts.foldl (· ++ ·) "" ++ ",)"
        else return "(" ++ strFormatCommaJoin parts ++ ")"
    | .ntuple tname fields xs =>
      match fuel with
      | 0 => Option.none
      | fuel + 1 => do
        let parts ← strFormatImmediateReprs fuel xs.toList
        return tname ++ "(" ++ strFormatCommaJoin (strFormatZipNames fields.toList parts) ++ ")"
    | .listV xs =>
      match fuel with
      | 0 => Option.none
      | fuel + 1 => do
        let parts ← strFormatImmediateReprs fuel xs.toList
        return "[" ++ strFormatCommaJoin parts ++ "]"
    | .rangeV lo hi step =>
      match fuel with
      | 0 => Option.none
      | fuel + 1 => do
        let start ← strFormatImmediateRepr fuel lo.toRVal
        let stop ← strFormatImmediateRepr fuel hi.toRVal
        if step.toInt == 1 then return "range(" ++ start ++ ", " ++ stop ++ ")"
        else
          let stride ← strFormatImmediateRepr fuel step.toRVal
          return "range(" ++ start ++ ", " ++ stop ++ ", " ++ stride ++ ")"
    | .ref _ => Option.none

  def strFormatImmediateReprs (fuel : Nat) : List RVal → Option (List String)
    | [] => some []
    | v :: vs => do
      let text ← strFormatImmediateRepr fuel v
      let rest ← strFormatImmediateReprs fuel vs
      return text :: rest
end

/-- Lowercase hexadecimal rendering for the bounded `%x` conversion. -/
def intHex (value : Int) : Option String :=
  if value.natAbs < 16 ^ intDigitBudget then
    let digits := String.ofList (Nat.toDigits 16 value.natAbs)
    some (if value < 0 then "-" ++ digits else digits)
  else Option.none

/-- Lowercase octal rendering for the bounded `%o` conversion. -/
def intOct (value : Int) : Option String :=
  if value.natAbs < 8 ^ intDigitBudget then
    let digits := String.ofList (Nat.toDigits 8 value.natAbs)
    some (if value < 0 then "-" ++ digits else digits)
  else Option.none

def intOctPrefixed (value : Int) : Option String :=
  if value.natAbs < 8 ^ intDigitBudget then
    let digits := String.ofList (Nat.toDigits 8 value.natAbs)
    some (if value < 0 then "-0o" ++ digits else "0o" ++ digits)
  else Option.none

def intBinPrefixed (value : Int) : Option String :=
  if value.natAbs < 2 ^ intDigitBudget then
    let digits := String.ofList (Nat.toDigits 2 value.natAbs)
    some (if value < 0 then "-0b" ++ digits else "0b" ++ digits)
  else Option.none

def intHexPrefixed (value : Int) : Option String :=
  if value.natAbs < 16 ^ intDigitBudget then
    let digits := String.ofList (Nat.toDigits 16 value.natAbs)
    some (if value < 0 then "-0x" ++ digits else "0x" ++ digits)
  else Option.none

/-- Lowercase hex digit. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Two-digit lowercase hex (`\xNN` escapes). -/
def hex2 (n : Nat) : String :=
  String.mk [hexDigit (n / 16 % 16), hexDigit (n % 16)]

def hex4 (n : Nat) : String :=
  String.mk [hexDigit (n / 4096 % 16), hexDigit (n / 256 % 16),
    hexDigit (n / 16 % 16), hexDigit (n % 16)]

def hex8 (n : Nat) : String :=
  String.mk [hexDigit (n / 0x10000000 % 16), hexDigit (n / 0x1000000 % 16),
    hexDigit (n / 0x100000 % 16), hexDigit (n / 0x10000 % 16),
    hexDigit (n / 4096 % 16), hexDigit (n / 256 % 16),
    hexDigit (n / 16 % 16), hexDigit (n % 16)]

def bytesQuote (values : List UInt8) : Char :=
  if values.contains 39 && !values.contains 34 then '"' else '\''

def bytesChar (quote : Char) (byte : UInt8) : String :=
  let number := byte.toNat
  if number == 92 then "\\\\"
  else if number == 10 then "\\n"
  else if number == 13 then "\\r"
  else if number == 9 then "\\t"
  else if number == quote.val.toNat then String.mk ['\\', quote]
  else if 0x20 ≤ number && number < 0x7f then String.mk [Char.ofNat number]
  else "\\x" ++ hex2 number

def bytesChars (quote : Char) : List UInt8 → String
  | [] => ""
  | byte :: rest => bytesChar quote byte ++ bytesChars quote rest

def bytesRepr (values : Array UInt8) : String :=
  let quote := bytesQuote values.toList
  "b" ++ String.mk [quote] ++ bytesChars quote values.toList ++ String.mk [quote]

def bytesIntVals (values : Array UInt8) : List RVal :=
  values.toList.map (fun byte => .int byte.toNat)

/-- `str(…)` — value-only (docs/memory-model.md §the cast tier): budgeted
exact decimal for ints, `True`/`False`, identity on strs, `None`, and bytes repr;
containers and refs refuse loudly (repr recursion is not guessed). -/
def strOfVal : RVal → Res RVal
  | .int value =>
    match intDecimal value with
    | some text => .ok (.str text)
    | Option.none => .exn decimalLimitError
  | .float value =>
    match value.repr with
    | some text => .ok (.str text)
    | none => .unsupported "float rendering is outside the tier"
  | .bool boolean => .ok (.str (if boolean then "True" else "False"))
  | .str text => .ok (.str text)
  | .bytes values => .ok (.str (bytesRepr values))
  | .none => .ok (.str "None")
  | .ellipsis => .ok (.str "Ellipsis")
  | value => .unsupported s!"str() of '{value.typeName}' is outside the tier (repr recursion is not guessed; docs/memory-model.md §the cast tier)"

/-- The quote CPython picks for a string's `repr`: `'` unless the string
contains one and no `"`. -/
def reprQuote (s : String) : Char :=
  if s.toList.contains '\'' && !s.toList.contains '"' then '"' else '\''

/-- CPython's printable Latin-1 intervals. The C1 controls, NBSP, and soft
hyphen retain their `\\xNN` escapes. -/
def latin1ReprPrintable (c : Char) : Bool :=
  let n := c.val.toNat
  (0xA1 ≤ n && n ≤ 0xAC) || (0xAE ≤ n && n ≤ 0xFF)

/-- Unicode 13.0 printable code-point ranges above Latin-1, as used by
`PyUnicode_IsPrintable` in CPython 3.9. The category rule is exactly
`General_Category` outside `C*` and `Z*`; U+0020 is handled above. -/
def unicodeReprPrintableRanges : List (Nat × Nat) :=
  [
    (0x100, 0x377),
    (0x37a, 0x37f),
    (0x384, 0x38a),
    (0x38c, 0x38c),
    (0x38e, 0x3a1),
    (0x3a3, 0x52f),
    (0x531, 0x556),
    (0x559, 0x58a),
    (0x58d, 0x58f),
    (0x591, 0x5c7),
    (0x5d0, 0x5ea),
    (0x5ef, 0x5f4),
    (0x606, 0x61b),
    (0x61e, 0x6dc),
    (0x6de, 0x70d),
    (0x710, 0x74a),
    (0x74d, 0x7b1),
    (0x7c0, 0x7fa),
    (0x7fd, 0x82d),
    (0x830, 0x83e),
    (0x840, 0x85b),
    (0x85e, 0x85e),
    (0x860, 0x86a),
    (0x8a0, 0x8b4),
    (0x8b6, 0x8c7),
    (0x8d3, 0x8e1),
    (0x8e3, 0x983),
    (0x985, 0x98c),
    (0x98f, 0x990),
    (0x993, 0x9a8),
    (0x9aa, 0x9b0),
    (0x9b2, 0x9b2),
    (0x9b6, 0x9b9),
    (0x9bc, 0x9c4),
    (0x9c7, 0x9c8),
    (0x9cb, 0x9ce),
    (0x9d7, 0x9d7),
    (0x9dc, 0x9dd),
    (0x9df, 0x9e3),
    (0x9e6, 0x9fe),
    (0xa01, 0xa03),
    (0xa05, 0xa0a),
    (0xa0f, 0xa10),
    (0xa13, 0xa28),
    (0xa2a, 0xa30),
    (0xa32, 0xa33),
    (0xa35, 0xa36),
    (0xa38, 0xa39),
    (0xa3c, 0xa3c),
    (0xa3e, 0xa42),
    (0xa47, 0xa48),
    (0xa4b, 0xa4d),
    (0xa51, 0xa51),
    (0xa59, 0xa5c),
    (0xa5e, 0xa5e),
    (0xa66, 0xa76),
    (0xa81, 0xa83),
    (0xa85, 0xa8d),
    (0xa8f, 0xa91),
    (0xa93, 0xaa8),
    (0xaaa, 0xab0),
    (0xab2, 0xab3),
    (0xab5, 0xab9),
    (0xabc, 0xac5),
    (0xac7, 0xac9),
    (0xacb, 0xacd),
    (0xad0, 0xad0),
    (0xae0, 0xae3),
    (0xae6, 0xaf1),
    (0xaf9, 0xaff),
    (0xb01, 0xb03),
    (0xb05, 0xb0c),
    (0xb0f, 0xb10),
    (0xb13, 0xb28),
    (0xb2a, 0xb30),
    (0xb32, 0xb33),
    (0xb35, 0xb39),
    (0xb3c, 0xb44),
    (0xb47, 0xb48),
    (0xb4b, 0xb4d),
    (0xb55, 0xb57),
    (0xb5c, 0xb5d),
    (0xb5f, 0xb63),
    (0xb66, 0xb77),
    (0xb82, 0xb83),
    (0xb85, 0xb8a),
    (0xb8e, 0xb90),
    (0xb92, 0xb95),
    (0xb99, 0xb9a),
    (0xb9c, 0xb9c),
    (0xb9e, 0xb9f),
    (0xba3, 0xba4),
    (0xba8, 0xbaa),
    (0xbae, 0xbb9),
    (0xbbe, 0xbc2),
    (0xbc6, 0xbc8),
    (0xbca, 0xbcd),
    (0xbd0, 0xbd0),
    (0xbd7, 0xbd7),
    (0xbe6, 0xbfa),
    (0xc00, 0xc0c),
    (0xc0e, 0xc10),
    (0xc12, 0xc28),
    (0xc2a, 0xc39),
    (0xc3d, 0xc44),
    (0xc46, 0xc48),
    (0xc4a, 0xc4d),
    (0xc55, 0xc56),
    (0xc58, 0xc5a),
    (0xc60, 0xc63),
    (0xc66, 0xc6f),
    (0xc77, 0xc8c),
    (0xc8e, 0xc90),
    (0xc92, 0xca8),
    (0xcaa, 0xcb3),
    (0xcb5, 0xcb9),
    (0xcbc, 0xcc4),
    (0xcc6, 0xcc8),
    (0xcca, 0xccd),
    (0xcd5, 0xcd6),
    (0xcde, 0xcde),
    (0xce0, 0xce3),
    (0xce6, 0xcef),
    (0xcf1, 0xcf2),
    (0xd00, 0xd0c),
    (0xd0e, 0xd10),
    (0xd12, 0xd44),
    (0xd46, 0xd48),
    (0xd4a, 0xd4f),
    (0xd54, 0xd63),
    (0xd66, 0xd7f),
    (0xd81, 0xd83),
    (0xd85, 0xd96),
    (0xd9a, 0xdb1),
    (0xdb3, 0xdbb),
    (0xdbd, 0xdbd),
    (0xdc0, 0xdc6),
    (0xdca, 0xdca),
    (0xdcf, 0xdd4),
    (0xdd6, 0xdd6),
    (0xdd8, 0xddf),
    (0xde6, 0xdef),
    (0xdf2, 0xdf4),
    (0xe01, 0xe3a),
    (0xe3f, 0xe5b),
    (0xe81, 0xe82),
    (0xe84, 0xe84),
    (0xe86, 0xe8a),
    (0xe8c, 0xea3),
    (0xea5, 0xea5),
    (0xea7, 0xebd),
    (0xec0, 0xec4),
    (0xec6, 0xec6),
    (0xec8, 0xecd),
    (0xed0, 0xed9),
    (0xedc, 0xedf),
    (0xf00, 0xf47),
    (0xf49, 0xf6c),
    (0xf71, 0xf97),
    (0xf99, 0xfbc),
    (0xfbe, 0xfcc),
    (0xfce, 0xfda),
    (0x1000, 0x10c5),
    (0x10c7, 0x10c7),
    (0x10cd, 0x10cd),
    (0x10d0, 0x1248),
    (0x124a, 0x124d),
    (0x1250, 0x1256),
    (0x1258, 0x1258),
    (0x125a, 0x125d),
    (0x1260, 0x1288),
    (0x128a, 0x128d),
    (0x1290, 0x12b0),
    (0x12b2, 0x12b5),
    (0x12b8, 0x12be),
    (0x12c0, 0x12c0),
    (0x12c2, 0x12c5),
    (0x12c8, 0x12d6),
    (0x12d8, 0x1310),
    (0x1312, 0x1315),
    (0x1318, 0x135a),
    (0x135d, 0x137c),
    (0x1380, 0x1399),
    (0x13a0, 0x13f5),
    (0x13f8, 0x13fd),
    (0x1400, 0x167f),
    (0x1681, 0x169c),
    (0x16a0, 0x16f8),
    (0x1700, 0x170c),
    (0x170e, 0x1714),
    (0x1720, 0x1736),
    (0x1740, 0x1753),
    (0x1760, 0x176c),
    (0x176e, 0x1770),
    (0x1772, 0x1773),
    (0x1780, 0x17dd),
    (0x17e0, 0x17e9),
    (0x17f0, 0x17f9),
    (0x1800, 0x180d),
    (0x1810, 0x1819),
    (0x1820, 0x1878),
    (0x1880, 0x18aa),
    (0x18b0, 0x18f5),
    (0x1900, 0x191e),
    (0x1920, 0x192b),
    (0x1930, 0x193b),
    (0x1940, 0x1940),
    (0x1944, 0x196d),
    (0x1970, 0x1974),
    (0x1980, 0x19ab),
    (0x19b0, 0x19c9),
    (0x19d0, 0x19da),
    (0x19de, 0x1a1b),
    (0x1a1e, 0x1a5e),
    (0x1a60, 0x1a7c),
    (0x1a7f, 0x1a89),
    (0x1a90, 0x1a99),
    (0x1aa0, 0x1aad),
    (0x1ab0, 0x1ac0),
    (0x1b00, 0x1b4b),
    (0x1b50, 0x1b7c),
    (0x1b80, 0x1bf3),
    (0x1bfc, 0x1c37),
    (0x1c3b, 0x1c49),
    (0x1c4d, 0x1c88),
    (0x1c90, 0x1cba),
    (0x1cbd, 0x1cc7),
    (0x1cd0, 0x1cfa),
    (0x1d00, 0x1df9),
    (0x1dfb, 0x1f15),
    (0x1f18, 0x1f1d),
    (0x1f20, 0x1f45),
    (0x1f48, 0x1f4d),
    (0x1f50, 0x1f57),
    (0x1f59, 0x1f59),
    (0x1f5b, 0x1f5b),
    (0x1f5d, 0x1f5d),
    (0x1f5f, 0x1f7d),
    (0x1f80, 0x1fb4),
    (0x1fb6, 0x1fc4),
    (0x1fc6, 0x1fd3),
    (0x1fd6, 0x1fdb),
    (0x1fdd, 0x1fef),
    (0x1ff2, 0x1ff4),
    (0x1ff6, 0x1ffe),
    (0x2010, 0x2027),
    (0x2030, 0x205e),
    (0x2070, 0x2071),
    (0x2074, 0x208e),
    (0x2090, 0x209c),
    (0x20a0, 0x20bf),
    (0x20d0, 0x20f0),
    (0x2100, 0x218b),
    (0x2190, 0x2426),
    (0x2440, 0x244a),
    (0x2460, 0x2b73),
    (0x2b76, 0x2b95),
    (0x2b97, 0x2c2e),
    (0x2c30, 0x2c5e),
    (0x2c60, 0x2cf3),
    (0x2cf9, 0x2d25),
    (0x2d27, 0x2d27),
    (0x2d2d, 0x2d2d),
    (0x2d30, 0x2d67),
    (0x2d6f, 0x2d70),
    (0x2d7f, 0x2d96),
    (0x2da0, 0x2da6),
    (0x2da8, 0x2dae),
    (0x2db0, 0x2db6),
    (0x2db8, 0x2dbe),
    (0x2dc0, 0x2dc6),
    (0x2dc8, 0x2dce),
    (0x2dd0, 0x2dd6),
    (0x2dd8, 0x2dde),
    (0x2de0, 0x2e52),
    (0x2e80, 0x2e99),
    (0x2e9b, 0x2ef3),
    (0x2f00, 0x2fd5),
    (0x2ff0, 0x2ffb),
    (0x3001, 0x303f),
    (0x3041, 0x3096),
    (0x3099, 0x30ff),
    (0x3105, 0x312f),
    (0x3131, 0x318e),
    (0x3190, 0x31e3),
    (0x31f0, 0x321e),
    (0x3220, 0x9ffc),
    (0xa000, 0xa48c),
    (0xa490, 0xa4c6),
    (0xa4d0, 0xa62b),
    (0xa640, 0xa6f7),
    (0xa700, 0xa7bf),
    (0xa7c2, 0xa7ca),
    (0xa7f5, 0xa82c),
    (0xa830, 0xa839),
    (0xa840, 0xa877),
    (0xa880, 0xa8c5),
    (0xa8ce, 0xa8d9),
    (0xa8e0, 0xa953),
    (0xa95f, 0xa97c),
    (0xa980, 0xa9cd),
    (0xa9cf, 0xa9d9),
    (0xa9de, 0xa9fe),
    (0xaa00, 0xaa36),
    (0xaa40, 0xaa4d),
    (0xaa50, 0xaa59),
    (0xaa5c, 0xaac2),
    (0xaadb, 0xaaf6),
    (0xab01, 0xab06),
    (0xab09, 0xab0e),
    (0xab11, 0xab16),
    (0xab20, 0xab26),
    (0xab28, 0xab2e),
    (0xab30, 0xab6b),
    (0xab70, 0xabed),
    (0xabf0, 0xabf9),
    (0xac00, 0xd7a3),
    (0xd7b0, 0xd7c6),
    (0xd7cb, 0xd7fb),
    (0xf900, 0xfa6d),
    (0xfa70, 0xfad9),
    (0xfb00, 0xfb06),
    (0xfb13, 0xfb17),
    (0xfb1d, 0xfb36),
    (0xfb38, 0xfb3c),
    (0xfb3e, 0xfb3e),
    (0xfb40, 0xfb41),
    (0xfb43, 0xfb44),
    (0xfb46, 0xfbc1),
    (0xfbd3, 0xfd3f),
    (0xfd50, 0xfd8f),
    (0xfd92, 0xfdc7),
    (0xfdf0, 0xfdfd),
    (0xfe00, 0xfe19),
    (0xfe20, 0xfe52),
    (0xfe54, 0xfe66),
    (0xfe68, 0xfe6b),
    (0xfe70, 0xfe74),
    (0xfe76, 0xfefc),
    (0xff01, 0xffbe),
    (0xffc2, 0xffc7),
    (0xffca, 0xffcf),
    (0xffd2, 0xffd7),
    (0xffda, 0xffdc),
    (0xffe0, 0xffe6),
    (0xffe8, 0xffee),
    (0xfffc, 0xfffd),
    (0x10000, 0x1000b),
    (0x1000d, 0x10026),
    (0x10028, 0x1003a),
    (0x1003c, 0x1003d),
    (0x1003f, 0x1004d),
    (0x10050, 0x1005d),
    (0x10080, 0x100fa),
    (0x10100, 0x10102),
    (0x10107, 0x10133),
    (0x10137, 0x1018e),
    (0x10190, 0x1019c),
    (0x101a0, 0x101a0),
    (0x101d0, 0x101fd),
    (0x10280, 0x1029c),
    (0x102a0, 0x102d0),
    (0x102e0, 0x102fb),
    (0x10300, 0x10323),
    (0x1032d, 0x1034a),
    (0x10350, 0x1037a),
    (0x10380, 0x1039d),
    (0x1039f, 0x103c3),
    (0x103c8, 0x103d5),
    (0x10400, 0x1049d),
    (0x104a0, 0x104a9),
    (0x104b0, 0x104d3),
    (0x104d8, 0x104fb),
    (0x10500, 0x10527),
    (0x10530, 0x10563),
    (0x1056f, 0x1056f),
    (0x10600, 0x10736),
    (0x10740, 0x10755),
    (0x10760, 0x10767),
    (0x10800, 0x10805),
    (0x10808, 0x10808),
    (0x1080a, 0x10835),
    (0x10837, 0x10838),
    (0x1083c, 0x1083c),
    (0x1083f, 0x10855),
    (0x10857, 0x1089e),
    (0x108a7, 0x108af),
    (0x108e0, 0x108f2),
    (0x108f4, 0x108f5),
    (0x108fb, 0x1091b),
    (0x1091f, 0x10939),
    (0x1093f, 0x1093f),
    (0x10980, 0x109b7),
    (0x109bc, 0x109cf),
    (0x109d2, 0x10a03),
    (0x10a05, 0x10a06),
    (0x10a0c, 0x10a13),
    (0x10a15, 0x10a17),
    (0x10a19, 0x10a35),
    (0x10a38, 0x10a3a),
    (0x10a3f, 0x10a48),
    (0x10a50, 0x10a58),
    (0x10a60, 0x10a9f),
    (0x10ac0, 0x10ae6),
    (0x10aeb, 0x10af6),
    (0x10b00, 0x10b35),
    (0x10b39, 0x10b55),
    (0x10b58, 0x10b72),
    (0x10b78, 0x10b91),
    (0x10b99, 0x10b9c),
    (0x10ba9, 0x10baf),
    (0x10c00, 0x10c48),
    (0x10c80, 0x10cb2),
    (0x10cc0, 0x10cf2),
    (0x10cfa, 0x10d27),
    (0x10d30, 0x10d39),
    (0x10e60, 0x10e7e),
    (0x10e80, 0x10ea9),
    (0x10eab, 0x10ead),
    (0x10eb0, 0x10eb1),
    (0x10f00, 0x10f27),
    (0x10f30, 0x10f59),
    (0x10fb0, 0x10fcb),
    (0x10fe0, 0x10ff6),
    (0x11000, 0x1104d),
    (0x11052, 0x1106f),
    (0x1107f, 0x110bc),
    (0x110be, 0x110c1),
    (0x110d0, 0x110e8),
    (0x110f0, 0x110f9),
    (0x11100, 0x11134),
    (0x11136, 0x11147),
    (0x11150, 0x11176),
    (0x11180, 0x111df),
    (0x111e1, 0x111f4),
    (0x11200, 0x11211),
    (0x11213, 0x1123e),
    (0x11280, 0x11286),
    (0x11288, 0x11288),
    (0x1128a, 0x1128d),
    (0x1128f, 0x1129d),
    (0x1129f, 0x112a9),
    (0x112b0, 0x112ea),
    (0x112f0, 0x112f9),
    (0x11300, 0x11303),
    (0x11305, 0x1130c),
    (0x1130f, 0x11310),
    (0x11313, 0x11328),
    (0x1132a, 0x11330),
    (0x11332, 0x11333),
    (0x11335, 0x11339),
    (0x1133b, 0x11344),
    (0x11347, 0x11348),
    (0x1134b, 0x1134d),
    (0x11350, 0x11350),
    (0x11357, 0x11357),
    (0x1135d, 0x11363),
    (0x11366, 0x1136c),
    (0x11370, 0x11374),
    (0x11400, 0x1145b),
    (0x1145d, 0x11461),
    (0x11480, 0x114c7),
    (0x114d0, 0x114d9),
    (0x11580, 0x115b5),
    (0x115b8, 0x115dd),
    (0x11600, 0x11644),
    (0x11650, 0x11659),
    (0x11660, 0x1166c),
    (0x11680, 0x116b8),
    (0x116c0, 0x116c9),
    (0x11700, 0x1171a),
    (0x1171d, 0x1172b),
    (0x11730, 0x1173f),
    (0x11800, 0x1183b),
    (0x118a0, 0x118f2),
    (0x118ff, 0x11906),
    (0x11909, 0x11909),
    (0x1190c, 0x11913),
    (0x11915, 0x11916),
    (0x11918, 0x11935),
    (0x11937, 0x11938),
    (0x1193b, 0x11946),
    (0x11950, 0x11959),
    (0x119a0, 0x119a7),
    (0x119aa, 0x119d7),
    (0x119da, 0x119e4),
    (0x11a00, 0x11a47),
    (0x11a50, 0x11aa2),
    (0x11ac0, 0x11af8),
    (0x11c00, 0x11c08),
    (0x11c0a, 0x11c36),
    (0x11c38, 0x11c45),
    (0x11c50, 0x11c6c),
    (0x11c70, 0x11c8f),
    (0x11c92, 0x11ca7),
    (0x11ca9, 0x11cb6),
    (0x11d00, 0x11d06),
    (0x11d08, 0x11d09),
    (0x11d0b, 0x11d36),
    (0x11d3a, 0x11d3a),
    (0x11d3c, 0x11d3d),
    (0x11d3f, 0x11d47),
    (0x11d50, 0x11d59),
    (0x11d60, 0x11d65),
    (0x11d67, 0x11d68),
    (0x11d6a, 0x11d8e),
    (0x11d90, 0x11d91),
    (0x11d93, 0x11d98),
    (0x11da0, 0x11da9),
    (0x11ee0, 0x11ef8),
    (0x11fb0, 0x11fb0),
    (0x11fc0, 0x11ff1),
    (0x11fff, 0x12399),
    (0x12400, 0x1246e),
    (0x12470, 0x12474),
    (0x12480, 0x12543),
    (0x13000, 0x1342e),
    (0x14400, 0x14646),
    (0x16800, 0x16a38),
    (0x16a40, 0x16a5e),
    (0x16a60, 0x16a69),
    (0x16a6e, 0x16a6f),
    (0x16ad0, 0x16aed),
    (0x16af0, 0x16af5),
    (0x16b00, 0x16b45),
    (0x16b50, 0x16b59),
    (0x16b5b, 0x16b61),
    (0x16b63, 0x16b77),
    (0x16b7d, 0x16b8f),
    (0x16e40, 0x16e9a),
    (0x16f00, 0x16f4a),
    (0x16f4f, 0x16f87),
    (0x16f8f, 0x16f9f),
    (0x16fe0, 0x16fe4),
    (0x16ff0, 0x16ff1),
    (0x17000, 0x187f7),
    (0x18800, 0x18cd5),
    (0x18d00, 0x18d08),
    (0x1b000, 0x1b11e),
    (0x1b150, 0x1b152),
    (0x1b164, 0x1b167),
    (0x1b170, 0x1b2fb),
    (0x1bc00, 0x1bc6a),
    (0x1bc70, 0x1bc7c),
    (0x1bc80, 0x1bc88),
    (0x1bc90, 0x1bc99),
    (0x1bc9c, 0x1bc9f),
    (0x1d000, 0x1d0f5),
    (0x1d100, 0x1d126),
    (0x1d129, 0x1d172),
    (0x1d17b, 0x1d1e8),
    (0x1d200, 0x1d245),
    (0x1d2e0, 0x1d2f3),
    (0x1d300, 0x1d356),
    (0x1d360, 0x1d378),
    (0x1d400, 0x1d454),
    (0x1d456, 0x1d49c),
    (0x1d49e, 0x1d49f),
    (0x1d4a2, 0x1d4a2),
    (0x1d4a5, 0x1d4a6),
    (0x1d4a9, 0x1d4ac),
    (0x1d4ae, 0x1d4b9),
    (0x1d4bb, 0x1d4bb),
    (0x1d4bd, 0x1d4c3),
    (0x1d4c5, 0x1d505),
    (0x1d507, 0x1d50a),
    (0x1d50d, 0x1d514),
    (0x1d516, 0x1d51c),
    (0x1d51e, 0x1d539),
    (0x1d53b, 0x1d53e),
    (0x1d540, 0x1d544),
    (0x1d546, 0x1d546),
    (0x1d54a, 0x1d550),
    (0x1d552, 0x1d6a5),
    (0x1d6a8, 0x1d7cb),
    (0x1d7ce, 0x1da8b),
    (0x1da9b, 0x1da9f),
    (0x1daa1, 0x1daaf),
    (0x1e000, 0x1e006),
    (0x1e008, 0x1e018),
    (0x1e01b, 0x1e021),
    (0x1e023, 0x1e024),
    (0x1e026, 0x1e02a),
    (0x1e100, 0x1e12c),
    (0x1e130, 0x1e13d),
    (0x1e140, 0x1e149),
    (0x1e14e, 0x1e14f),
    (0x1e2c0, 0x1e2f9),
    (0x1e2ff, 0x1e2ff),
    (0x1e800, 0x1e8c4),
    (0x1e8c7, 0x1e8d6),
    (0x1e900, 0x1e94b),
    (0x1e950, 0x1e959),
    (0x1e95e, 0x1e95f),
    (0x1ec71, 0x1ecb4),
    (0x1ed01, 0x1ed3d),
    (0x1ee00, 0x1ee03),
    (0x1ee05, 0x1ee1f),
    (0x1ee21, 0x1ee22),
    (0x1ee24, 0x1ee24),
    (0x1ee27, 0x1ee27),
    (0x1ee29, 0x1ee32),
    (0x1ee34, 0x1ee37),
    (0x1ee39, 0x1ee39),
    (0x1ee3b, 0x1ee3b),
    (0x1ee42, 0x1ee42),
    (0x1ee47, 0x1ee47),
    (0x1ee49, 0x1ee49),
    (0x1ee4b, 0x1ee4b),
    (0x1ee4d, 0x1ee4f),
    (0x1ee51, 0x1ee52),
    (0x1ee54, 0x1ee54),
    (0x1ee57, 0x1ee57),
    (0x1ee59, 0x1ee59),
    (0x1ee5b, 0x1ee5b),
    (0x1ee5d, 0x1ee5d),
    (0x1ee5f, 0x1ee5f),
    (0x1ee61, 0x1ee62),
    (0x1ee64, 0x1ee64),
    (0x1ee67, 0x1ee6a),
    (0x1ee6c, 0x1ee72),
    (0x1ee74, 0x1ee77),
    (0x1ee79, 0x1ee7c),
    (0x1ee7e, 0x1ee7e),
    (0x1ee80, 0x1ee89),
    (0x1ee8b, 0x1ee9b),
    (0x1eea1, 0x1eea3),
    (0x1eea5, 0x1eea9),
    (0x1eeab, 0x1eebb),
    (0x1eef0, 0x1eef1),
    (0x1f000, 0x1f02b),
    (0x1f030, 0x1f093),
    (0x1f0a0, 0x1f0ae),
    (0x1f0b1, 0x1f0bf),
    (0x1f0c1, 0x1f0cf),
    (0x1f0d1, 0x1f0f5),
    (0x1f100, 0x1f1ad),
    (0x1f1e6, 0x1f202),
    (0x1f210, 0x1f23b),
    (0x1f240, 0x1f248),
    (0x1f250, 0x1f251),
    (0x1f260, 0x1f265),
    (0x1f300, 0x1f6d7),
    (0x1f6e0, 0x1f6ec),
    (0x1f6f0, 0x1f6fc),
    (0x1f700, 0x1f773),
    (0x1f780, 0x1f7d8),
    (0x1f7e0, 0x1f7eb),
    (0x1f800, 0x1f80b),
    (0x1f810, 0x1f847),
    (0x1f850, 0x1f859),
    (0x1f860, 0x1f887),
    (0x1f890, 0x1f8ad),
    (0x1f8b0, 0x1f8b1),
    (0x1f900, 0x1f978),
    (0x1f97a, 0x1f9cb),
    (0x1f9cd, 0x1fa53),
    (0x1fa60, 0x1fa6d),
    (0x1fa70, 0x1fa74),
    (0x1fa78, 0x1fa7a),
    (0x1fa80, 0x1fa86),
    (0x1fa90, 0x1faa8),
    (0x1fab0, 0x1fab6),
    (0x1fac0, 0x1fac2),
    (0x1fad0, 0x1fad6),
    (0x1fb00, 0x1fb92),
    (0x1fb94, 0x1fbca),
    (0x1fbf0, 0x1fbf9),
    (0x20000, 0x2a6dd),
    (0x2a700, 0x2b734),
    (0x2b740, 0x2b81d),
    (0x2b820, 0x2cea1),
    (0x2ceb0, 0x2ebe0),
    (0x2f800, 0x2fa1d),
    (0x30000, 0x3134a),
    (0xe0100, 0xe01ef)
  ]

def unicodeReprPrintable (c : Char) : Bool :=
  unicodeReprPrintableRanges.any (fun (lo, hi) =>
    lo ≤ c.val.toNat && c.val.toNat ≤ hi)

/-- `repr` of one character inside a string literal. -/
def reprChar (q : Char) : Char → Option String
  | '\\' => some "\\\\"
  | '\n' => some "\\n"
  | '\r' => some "\\r"
  | '\t' => some "\\t"
  | c =>
    if c == q then some (String.mk ['\\', c])
    else if c.val < 0x20 || c.val == 0x7f then some ("\\x" ++ hex2 c.val.toNat)
    else if c.val < 0x7f then some (String.mk [c])
    else if latin1ReprPrintable c then some (String.mk [c])
    else if c.val < 0x100 then some ("\\x" ++ hex2 c.val.toNat)
    else if unicodeReprPrintable c then some (String.mk [c])
    else if c.val ≤ 0xffff then some ("\\u" ++ hex4 c.val.toNat)
    else some ("\\U" ++ hex8 c.val.toNat)

/-- `reprChar` over a character list. -/
def reprChars (q : Char) : List Char → Option String
  | [] => some ""
  | c :: cs => do
    let a ← reprChar q c
    let rest ← reprChars q cs
    return a ++ rest

/-- CPython `repr` of a str: the quote choice above, backslash/quote/
`\n`/`\r`/`\t` escapes, `\xNN` for the other C0/C1 controls and DEL, direct
rendering for CPython-printable Unicode, and `\uNNNN`/`\UNNNNNNNN` for
non-printable Unicode. -/
def reprStr (s : String) : Option String := do
  let q := reprQuote s
  let body ← reprChars q s.data
  return String.mk [q] ++ body ++ String.mk [q]

def asciiChar (q : Char) (c : Char) : String :=
  if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c == q then String.mk ['\\', c]
  else if c.val < 0x20 || c.val == 0x7f then "\\x" ++ hex2 c.val.toNat
  else if c.val < 0x7f then String.mk [c]
  else if c.val ≤ 0xff then "\\x" ++ hex2 c.val.toNat
  else if c.val ≤ 0xffff then "\\u" ++ hex4 c.val.toNat
  else "\\U" ++ hex8 c.val.toNat

def asciiChars (q : Char) : List Char → String
  | [] => ""
  | c :: cs => asciiChar q c ++ asciiChars q cs

def asciiStr (s : String) : String :=
  let q := reprQuote s
  String.mk [q] ++ asciiChars q s.data ++ String.mk [q]

/-! ### `%`-formatting (docs/memory-model.md §`%`-formatting on strings)

`str % args` is CPython's `unicode_mod`: ONE left-to-right pass over the
format string. This operator is a pure function of two VALUES and cannot
see the heap, so it admits scalars and ref-free containers whose rendering is
heap-independent; heap references still refuse loudly rather than guessing a
`repr` the heap holds. -/

/-- `%s` of an argument: `strOfVal` verbatim for scalars; ref-free tuple,
namedtuple, range, and boundary-list values use their value-only `repr`.
`none` = outside the inventory. -/
def strFormatStr (v : RVal) : Option String :=
  match v with
  | .tuple _ | .ntuple _ _ _ | .listV _ | .rangeV _ _ _ =>
      strFormatImmediateRepr strFormatReprFuel v
  | _ =>
      match strOfVal v with
      | .ok (.str s) => some s
      | _ => Option.none

/-- `%r` of an argument. Only a str differs from `%s` — CPython's `repr`
and `str` COINCIDE on int/bool/None — and its quoting/escaping IS the
shipped `reprStr`, including the admitted printable Unicode strings. -/
def strFormatRepr (v : RVal) : Option String :=
  match v with
  | .str s => reprStr s
  | .bytes values => some (bytesRepr values)
  | .tuple _ | .ntuple _ _ _ | .listV _ | .rangeV _ _ _ =>
      strFormatImmediateRepr strFormatReprFuel v
  | v => strFormatStr v

/-- `%c` accepts an integer code point or a one-character string. -/
def strFormatChar (v : RVal) : Res String :=
  match v with
  | .str s =>
      match s.toList with
      | [c] => .ok (String.ofList [c])
      | _ => .exn (.typeError "%c requires int or char")
  | v =>
      match asInt v with
      | some n =>
          if n < 0 || 0x10FFFF < n then
            .exn (.overflowError "%c arg not in range(0x110000)")
          else if 0xD800 ≤ n && n ≤ 0xDFFF then
            .unsupported
              "%c of a surrogate code point is outside the tier (Lean's Char excludes surrogates; docs/memory-model.md §string semantics)"
          else .ok (String.ofList [Char.ofNat n.toNat])
      | Option.none => .exn (.typeError "%c requires int or char")

/-- One admitted conversion applied to one argument. A `.ref` argument
(reachable only nested inside a tuple, since an operand-position `.ref`
is refused before this arm) is LOUD, never a `TypeError` built from
`RVal.typeName`'s `"object"` placeholder. -/
def strFormatConv (c : Char) (v : RVal) : Res String :=
  match v with
  | .ref _ =>
      .unsupported "a heap object as a '%'-format argument is outside the tier (its repr lives in the heap, which the operator cannot see; docs/memory-model.md §`%`-formatting on strings)"
  | v =>
    if c == 'a' then
      match v with
      | .str s => .ok (asciiStr s)
      | v =>
          match strFormatRepr v with
          | some s => .ok s
          | Option.none => .unsupported s!"'%{c}' of a '{v.typeName}' is outside the tier (only scalar values render here; docs/memory-model.md §`%`-formatting on strings)"
    else if c == 'c' then
      strFormatChar v
    else if c == 'd' || c == 'i' || c == 'u' then
      match (match v with | .float value => value.toInt | _ => asInt v) with
      | some value =>
        match intDecimal value with
        | some text => .ok text
        | Option.none => .exn decimalLimitError
      -- CPython leaves this type name UNQUOTED (measured against 3.9)
      | Option.none =>
        if v.hasFloat then .unsupported s!"'%{c}' of a non-finite float is outside the tier"
        else .exn (.typeError s!"%{c} format: a number is required, not {v.typeName}")
    else if c == 'x' then
      match asInt v with
      | some value =>
          match intHex value with
          | some text => .ok text
          | Option.none => .unsupported "'%x' integer rendering beyond intDigitBudget is outside the tier (docs/memory-model.md §decimal integer rendering)"
      | Option.none => .exn (.typeError s!"%x format: an integer is required, not {v.typeName}")
    else if c == 'o' then
      match asInt v with
      | some value =>
          match intOct value with
          | some text => .ok text
          | Option.none => .unsupported "'%o' integer rendering beyond intDigitBudget is outside the tier (docs/memory-model.md §decimal integer rendering)"
      | Option.none => .exn (.typeError s!"%o format: an integer is required, not {v.typeName}")
    else if (c == 'r' || c == 's') &&
        strFormatImmediateReprOverflow strFormatReprFuel v then
      .exn decimalLimitError
    else
      match (if c == 'r' then strFormatRepr v else strFormatStr v) with
      | some s => .ok s
      | Option.none =>
        .unsupported s!"'%{c}' of a '{v.typeName}' is outside the tier (only int/bool/str/None render here, integers within intDigitBudget; docs/memory-model.md §`%`-formatting on strings)"

/-- CPython's `ctx.dict` test, verbatim: `PyMapping_Check(args) &&
!PyTuple_Check(args) && !PyUnicode_Check(args)` (`PyUnicode_Format`,
Objects/unicodeobject.c). `PyMapping_Check` is `tp_as_mapping->mp_subscript
≠ NULL` — MEASURED true on str/tuple/list/dict/range/bytes/bytearray and
false on None/bool/int/float/set (3.9.19, through `ctypes.pythonapi`), so
inside this tier the mapping right operand is exactly `listV` and `rangeV`:
str and tuple are struck out by the two `!` clauses, a namedtuple by
`PyTuple_Check` on the subclass, and a `.ref` never arrives at all
(`evalBinOp`'s heap-operand refusal fires first — the invariant §`%`-
formatting states, and the thing to revisit when lists move to the heap).

It decides ONE observable, and that is why it is here: with a mapping RHS
the trailing `not all arguments converted` check DOES NOT RUN (the check
is guarded `argidx < arglen && !dict`), so `'  x  ' % [1, 3, 5]` is
`'  x  '` and not a `TypeError`. The other half of the mapping path, the
`%(key)s` protocol, is refused LOUDLY by the walker below and stays so. -/
def strFormatMappingRhs : RVal → Bool
  | .listV _ => true
  | .rangeV _ _ _ => true
  | _ => false

/-- Parse the small mapping-key token admitted by the heap formatting rung.
The returned tail starts after the conversion character, so the formatting
walk remains a single left-to-right pass. Rich mapping syntax remains loud. -/
def strFormatMapToken : List Char → Option (String × Char × List Char)
  | cs => go [] cs
where
  go (key : List Char) : List Char → Option (String × Char × List Char)
    | [] => Option.none
    | ')' :: c :: rest => some (String.ofList key, c, rest)
    | c :: rest => go (key ++ [c]) rest

def strFormatDictFind : List (RVal × RVal) → String → Option RVal
  | [], _ => Option.none
  | (k, v) :: rest, key =>
      match k with
      | .str stored => if stored == key then some v else strFormatDictFind rest key
      | _ => strFormatDictFind rest key

/-- The measured heap-dict mapping slice for `str % rhs`. A mapping key is a
plain string in `%(key)s`; the dict lookup is insertion-order independent and
uses the same `keyEq`/`dictFind` worker as ordinary subscripting. -/
def strFormatMappingWalk (h : Heap) (a : Addr) : Nat → List Char → String → Res String
  | 0, [], acc => .ok acc
  | 0, _, _ => .timeout
  | fuel + 1, [], acc => .ok acc
  | fuel + 1, '%' :: '%' :: cs, acc => strFormatMappingWalk h a fuel cs (acc ++ "%")
  | fuel + 1, '%' :: '(' :: cs, acc =>
      match strFormatMapToken cs with
      | some (key, conv, rest) =>
          match Heap.get? h a with
          | some (.dict entries _) =>
              match strFormatDictFind entries.toList key with
              | some value =>
                  match strFormatConv conv value with
                  | .ok piece => strFormatMappingWalk h a fuel rest (acc ++ piece)
                  | .exn e => .exn e
                  | .timeout => .timeout
                  | .unsupported msg => .unsupported msg
              | Option.none => .exn .keyError
          | _ => .unsupported "dangling heap reference"
      | Option.none =>
          .unsupported "mapping-key string formatting is outside the tier (only literal string keys are admitted; docs/memory-model.md §`%`-formatting on strings)"
  | fuel + 1, '%' :: c :: cs, acc =>
      match Heap.get? h a with
      | some (.dict entries _) =>
          match strFormatDictFind entries.toList "" with
          | _ =>
              -- A non-mapping conversion has one mapping argument. Keep the
              -- boundary loud rather than fabricating a dict representation.
              .unsupported s!"the '%{c}' conversion over a dict mapping is outside the tier"
      | _ => .unsupported "dangling heap reference"
  | fuel + 1, ['%'], _ => .exn (.valueError "incomplete format")
  | fuel + 1, c :: cs, acc => strFormatMappingWalk h a fuel cs (acc ++ String.ofList [c])
  termination_by structural fuel => fuel

def padFormatField (width : Nat) (s : String) : String :=
  if s.length < width then
    String.ofList (List.replicate (width - s.length) ' ') ++ s
  else s

def padFormatFieldLeft (width : Nat) (s : String) : String :=
  if s.length < width then
    s ++ String.ofList (List.replicate (width - s.length) ' ')
  else s

def zeroPadFormatField (width : Nat) (s : String) : String :=
  if s.length < width then
    let zeros := String.ofList (List.replicate (width - s.length) '0')
    match s.toList with
    | '-' :: cs => "-" ++ zeros ++ String.ofList cs
    | _ => zeros ++ s
  else s

/-- The single left-to-right pass. Literals copy; `%%` emits one `%` and
consumes NOTHING; `%s`/`%r`/`%a`/`%c`/`%d`/`%i`/`%u`/`%x`/`%o` consume the next argument. Running out
mid-walk is CPython's `not enough arguments` verbatim, and so are
leftover arguments at the end — EXCEPT under `mapping`, the `ctx.dict`
flag above, which is exactly the condition CPython guards that second
check with. Anything else after a `%` — a flag, a width, a precision, a
mapping key, another supported conversion character, or the end of the
string — is LOUD: the format minilanguage is a second tier. The invalid `%q`
form and a trailing `%` carry CPython's faithful `ValueError`s. -/
def strFormatWalk : List Char → List RVal → Bool → String → Res String
  | [], args, mapping, acc =>
      if args.isEmpty || mapping then .ok acc
      else .exn (.typeError "not all arguments converted during string formatting")
  | '%' :: '%' :: cs, args, mapping, acc => strFormatWalk cs args mapping (acc ++ "%")
  | '%' :: '5' :: 'd' :: cs, args, mapping, acc =>
      match args with
      | [] => .exn (.typeError "not enough arguments for format string")
      | a :: rest =>
          match strFormatConv 'd' a with
          | .ok piece => strFormatWalk cs rest mapping (acc ++ padFormatField 5 piece)
          | .exn e => .exn e
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
  | '%' :: '0' :: '5' :: 'd' :: cs, args, mapping, acc =>
      match args with
      | [] => .exn (.typeError "not enough arguments for format string")
      | a :: rest =>
          match strFormatConv 'd' a with
          | .ok piece => strFormatWalk cs rest mapping (acc ++ zeroPadFormatField 5 piece)
          | .exn e => .exn e
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
  | '%' :: '-' :: '5' :: 'd' :: cs, args, mapping, acc =>
      match args with
      | [] => .exn (.typeError "not enough arguments for format string")
      | a :: rest =>
          match strFormatConv 'd' a with
          | .ok piece => strFormatWalk cs rest mapping (acc ++ padFormatFieldLeft 5 piece)
          | .exn e => .exn e
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
  | '%' :: c :: cs, args, mapping, acc =>
      if c == 's' || c == 'r' || c == 'a' || c == 'c' || c == 'd' || c == 'i' || c == 'u' || c == 'x' || c == 'o' then
        match args with
        | [] => .exn (.typeError "not enough arguments for format string")
        -- the conversion is matched OPEN, not bound through `Res`'s
        -- `bind`: a recursive call under the bind's lambda is invisible
        -- to structural recursion, and this walker must stay
        -- kernel-reducible (the mergeSort trap, AGENTS.md)
        | a :: rest =>
            match strFormatConv c a with
            | .ok piece => strFormatWalk cs rest mapping (acc ++ piece)
            | .exn e => .exn e
            | .timeout => .timeout
            | .unsupported msg => .unsupported msg
      else if c == 'q' then
        .exn (.valueError "unsupported format character 'q' (0x71) at index 1")
      else
        .unsupported s!"the '%{c}' conversion is outside the tier (only bare %s/%r/%a/%c/%d/%i/%u/%x/%o/%% — no flags, width, precision, or mapping key; docs/memory-model.md §`%`-formatting on strings)"
  | ['%'], _, _, _ =>
      .exn (.valueError "incomplete format")
  | c :: cs, args, mapping, acc => strFormatWalk cs args mapping (acc ++ String.mk [c])

/-- `str % args`. The argument LIST is the RHS spread when it is a tuple
— and a NAMEDTUPLE spreads too, because `PyTuple_Check` succeeds on the
subclass (`'%s %s' % Move(1,2)` is `'1 2'`, measured): treating it as one
argument would fabricate an arity error for a program CPython runs.
Everything else is the one-element list — which is CPython's `arglen = -1,
argidx = -2` state exactly: the first conversion gets the whole object,
the second is `not enough arguments`. Whether a LEFTOVER is an error is
the separate `ctx.dict` question `strFormatMappingRhs` answers. -/
def strFormat (fmt : String) (rhs : RVal) : Res RVal := do
  let args : List RVal :=
    match rhs with
    | .tuple xs => xs.toList
    | .ntuple _ _ xs => xs.toList
    | v => [v]
  let s ← strFormatWalk fmt.data args (strFormatMappingRhs rhs) ""
  return .str s

def strFormatH (h : Heap) (fmt : String) (rhs : RVal) : Res RVal :=
  match rhs with
  | .ref a =>
      match Heap.get? h a with
      | some (.dict ..) => do
          let s ← strFormatMappingWalk h a fmt.length fmt.toList ""
          return .str s
      | _ => strFormat fmt rhs
  | _ => strFormat fmt rhs

/-- The measured bare bytes formatting rung: `b"%s" % bytes` copies the
operand bytes. Other format strings and operand protocols remain loud until
CPython's bytes formatting grammar is represented. -/
def bytesFormat (fmt : Array UInt8) (rhs : RVal) : Res RVal :=
  if fmt.toList == [37, 115] then
    match rhs with
    | .bytes xs => .ok (.bytes xs)
    | _ => .unsupported "bytes percent formatting with this operand is outside the tier"
  else
    .unsupported "bytes percent formatting is outside the tier (only bare %s with bytes is admitted)"

def floatNumber (value : RVal) : Res Float64 :=
  match value with
  | .float number => .ok number
  | value =>
    match asInt value with
    | some integer =>
      match Float64.fromInt integer with
      | some number => .ok number
      | Option.none => .exn (.overflowError "int too large to convert to float")
    | Option.none => .unsupported "float arithmetic with a nonnumeric operand requires its numeric protocol"

def floatIsInteger (value : Float64) : Bool :=
  let exponent := value.exponent
  if exponent == 2047 then false
  else if exponent == 0 then value.fraction == 0
  else if exponent < 1023 then false
  else if exponent >= 1075 then true
  else value.fraction % 2 ^ (1075 - exponent) == 0

def floatArithmeticInvalid (operator : Float64.ArithmeticOp)
    (left right : Float64) : Bool :=
  match operator with
  | .add => left.isInf && right.isInf && left.sign != right.sign
  | .sub => left.isInf && right.isInf && left.sign == right.sign
  | .mult => (left.isInf && right.isZero) || (right.isInf && left.isZero)

def evalFloatArithmetic (operator : Float64.ArithmeticOp) (left right : RVal) : Res RVal := do
  let leftNumber ← floatNumber left
  let rightNumber ← floatNumber right
  if leftNumber.isNaN || rightNumber.isNaN then
    match Float64.arithmeticWithNaN operator leftNumber rightNumber with
    | .ok value => return .float value
    | .error .conversionOverflow => .exn (.overflowError "int too large to convert to float")
    | .error .nanPayload =>
      .unsupported "NaN payload/sign propagation requires an explicit floating-point oracle"
  else if floatArithmeticInvalid operator leftNumber rightNumber then
    .ok (.float (Float64.ofBits 0xfff8000000000000))
  else
    match Float64.arithmetic operator leftNumber rightNumber with
    | .ok value => return .float value
    | .error .conversionOverflow => .exn (.overflowError "int too large to convert to float")
    | .error .nanPayload =>
      .unsupported "NaN payload/sign propagation requires an explicit floating-point oracle"

def evalFloatDivmod (zeroError : PyErr) (left right : RVal) : Res (Float64 × Float64) := do
  let leftNumber ← floatNumber left
  let rightNumber ← floatNumber right
  match Float64.floorRemWithNaN leftNumber rightNumber with
  | .ok pair => return pair
  | .error .zeroDivision => .exn zeroError
  | .error .conversionOverflow => .exn (.overflowError "int too large to convert to float")
  | .error .nanPayload =>
    .unsupported "NaN payload/sign propagation requires an explicit floating-point oracle"

/-- Binary operator on already-evaluated operands. Integer/Boolean `+`, `-`
and `*` return integers; true division returns binary64. Mixed arithmetic
converts the integer before computing and preserves signed zero and rounding.
`//`/`%` floor (`Int.fdiv`/`Int.fmod`); divisor 0 → `ZeroDivisionError`.
`**` with a negative integer exponent returns a binary64 reciprocal when the
exponent is within `floatPowBudget`; larger exponents remain unsupported.
`+` concatenates matching sequence types; `%` on a str is the format operator
(`strFormat`, §`%`-formatting above). Unresolved protocols and NaN payloads
remain loud. A `.ref` operand is refused before a fabricated type-name error. -/
def evalBinOp (op : BinOp) (a b : RVal) : Res RVal :=
  match asInt a, asInt b with
  | some x, some y =>
    match op with
    | .add => .ok (.int (x + y))
    | .sub => .ok (.int (x - y))
    | .mult => .ok (.int (x * y))
    | .div =>
        match Float64.divideInt x y with
        | .ok value => .ok (.float value)
        | .error .zeroDivision => .exn .trueZeroDivisionError
        | .error .overflow => .exn (.overflowError "integer division result too large for a float")
    | .floorDiv =>
        if y = 0 then .exn .zeroDivisionError else .ok (.int (Int.fdiv x y))
    | .mod =>
        if y = 0 then .exn .zeroDivisionError else .ok (.int (Int.fmod x y))
    | .pow =>
        if y < 0 then
          if x = 0 then .exn .zeroDivisionPow
          else if y.natAbs > floatPowBudget then
            .unsupported "'**' with a negative exponent beyond floatPowBudget is outside the tier (docs/memory-model.md §power)"
          else
            match Float64.divideInt 1 (x ^ y.natAbs) with
            | .ok value => .ok (.float value)
            | .error .zeroDivision => .exn .zeroDivisionPow
            | .error .overflow => .exn (.overflowError "integer power result too large for a float")
        else .ok (.int (x ^ y.toNat))
    -- pass 5 (docs/memory-model.md §left shift and bitwise or):
    -- `x << n` is EXACT on all ints as `x * 2^n` (unbounded ints, sign
    -- carries through); the negative count is the faithful ValueError.
    | .lshift =>
        if y < 0 then .exn (.valueError "negative shift count")
        else if y.toNat > shiftBudget then
          if y.toNat >= shiftOverflowBudget then
            .exn (.overflowError "too many digits in integer")
          else
            .unsupported "a left shift beyond shiftBudget is outside the tier (docs/memory-model.md §left shift and bitwise or)"
        else .ok (.int (x * (2 : Int) ^ y.toNat))
    -- `>>` is `<<`'s mirror and is CPython's ARITHMETIC shift: it rounds
    -- toward -inf, which is exactly `Int.fdiv` by `2^n` (`-5 >> 1 == -3`).
    -- CPython saturates once the count reaches the operand's bit length,
    -- so huge counts can be answered without constructing `2^n`: nonnegative
    -- operands become 0 and negative operands become -1. Counts below that
    -- boundary still use `<<`'s fixed budget to protect kernel reduction.
    | .rshift =>
        if y < 0 then .exn (.valueError "negative shift count")
        else if y.toNat >= intBitLength x then
          .ok (.int (if x < 0 then -1 else 0))
        else if y.toNat > shiftBudget then
          .unsupported "a right shift beyond shiftBudget is outside the tier (docs/memory-model.md §left shift and bitwise or)"
        else .ok (.int (Int.fdiv x ((2 : Int) ^ y.toNat)))
    -- `|` and `&` decide BOOLNESS first (`bool.__or__(bool)` returns a
    -- BOOL, any int operand makes it an int), then compute over `Int` —
    -- negative operands INCLUDED (docs/memory-model.md §bitwise `&`; the
    -- pass-5 refusal was measured wrong and is retired here, in the same
    -- landing that admits `&`, so the family cannot drift apart).
    | .bitOr =>
        (match a, b with
         | .bool p, .bool q => .ok (.bool (p || q))
         | _, _ => .ok (.int (intOr x y)))
    | .bitXor =>
        (match a, b with
         | .bool p, .bool q => .ok (.bool (p != q))
         | _, _ => .ok (.int (intXor x y)))
    | .bitAnd =>
        (match a, b with
         | .bool p, .bool q => .ok (.bool (p && q))
         | _, _ => .ok (.int (intAnd x y)))
    | .matMult =>
        .exn (.typeError
          s!"unsupported operand type(s) for @: '{a.typeName}' and '{b.typeName}'")
  | _, _ =>
    match op, a, b with
    | .div, .float left, .float right =>
        match Float64.divideFiniteWithNaN left right with
        | .ok value => .ok (.float value)
        | .error .zeroDivision => .exn .floatZeroDivisionError
        | .error .conversionOverflow => .exn (.overflowError "int too large to convert to float")
        | .error .nanPayload => .unsupported "NaN payload/sign propagation requires an explicit floating-point oracle"
    | .div, .int left, .float right =>
        match Float64.divideIntFloatWithNaN left right with
        | .ok value => .ok (.float value)
        | .error .zeroDivision => .exn .floatZeroDivisionError
        | .error .conversionOverflow => .exn (.overflowError "int too large to convert to float")
        | .error .nanPayload => .unsupported "NaN payload/sign propagation requires an explicit floating-point oracle"
    | .div, .float left, .int right =>
        match Float64.divideFloatIntWithNaN left right with
        | .ok value => .ok (.float value)
        | .error .zeroDivision => .exn .floatZeroDivisionError
        | .error .conversionOverflow => .exn (.overflowError "int too large to convert to float")
        | .error .nanPayload => .unsupported "NaN payload/sign propagation requires an explicit floating-point oracle"
    | .div, .bool left, .float right =>
        match Float64.divideIntFloatWithNaN (if left then 1 else 0) right with
        | .ok value => .ok (.float value)
        | .error .zeroDivision => .exn .floatZeroDivisionError
        | .error .conversionOverflow => .exn (.overflowError "int too large to convert to float")
        | .error .nanPayload => .unsupported "NaN payload/sign propagation requires an explicit floating-point oracle"
    | .div, .float left, .bool right =>
        match Float64.divideFloatIntWithNaN left (if right then 1 else 0) with
        | .ok value => .ok (.float value)
        | .error .zeroDivision => .exn .floatZeroDivisionError
        | .error .conversionOverflow => .exn (.overflowError "int too large to convert to float")
        | .error .nanPayload => .unsupported "NaN payload/sign propagation requires an explicit floating-point oracle"
    | .add, .str s, .str t => .ok (.str (s ++ t))
    | .mod, .bytes fmt, rhs => bytesFormat fmt rhs
    | .add, .bytes xs, .bytes ys => .ok (.bytes (xs ++ ys))
    | .add, .bytes _, .ref _ => .unsupported "bytes concatenation with heap values requires the buffer protocol"
    | .add, .bytes _, value => .exn (.typeError s!"can't concat {typeNamePrefix value.typeName 100} to bytes")
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
    | .matMult, a, b =>
        .exn (.typeError
          s!"unsupported operand type(s) for @: '{a.typeName}' and '{b.typeName}'")
    | .add, .float _, _ | .add, _, .float _ => evalFloatArithmetic .add a b
    | .sub, .float _, _ | .sub, _, .float _ => evalFloatArithmetic .sub a b
    | .mult, .float _, _ | .mult, _, .float _ => evalFloatArithmetic .mult a b
    | .mult, left, right => sequenceMult left right
    | .mod, .str fmt, rhs => strFormat fmt rhs
    | .floorDiv, .float _, _ | .floorDiv, _, .float _ => do
        let (quotient, _) ← evalFloatDivmod .floatFloorZeroDivisionError a b
        return .float quotient
    | .mod, .float _, _ | .mod, _, .float _ => do
        let (_, remainder) ← evalFloatDivmod .floatModuloZeroDivisionError a b
        return .float remainder
    | _, .float _, _ | _, _, .float _ =>
        .unsupported "this float arithmetic operator is not yet modelled"
    | op, a, b =>
        .exn (.typeError
          s!"unsupported operand type(s) for {op.symbol}: '{a.typeName}' and '{b.typeName}'")

/-- Unary operator: `not` is truthiness negation (`Res`-valued through
`truthy` since H1); `-`, `+` and `~` need an int/bool operand and all
three DROP boolness the way CPython does (`-True == -1`, `+True == 1`,
`~True == -2` — `bool` has no `__neg__`/`__pos__`/`__invert__`, so the
int slots run); a `.ref` operand is refused loudly (its dunder lives in
the heap). `+` is the identity on an int and `~x` is `-x - 1`, which is
two's complement by definition, not a bit-level guess. -/
def evalUnaryOp (op : UnaryOp) (v : RVal) : Res RVal :=
  match op with
  | .not => do let b ← truthy v; return .bool (!b)
  | .usub =>
    match v with
    | .float value => .ok (.float value.neg)
    | .ref _ =>
        .unsupported "unary '-' on a heap object is outside the H1 tier (docs/memory-model.md)"
    | v =>
      match asInt v with
      | some n => .ok (.int (-n))
      | Option.none => .exn (.typeError s!"bad operand type for unary -: '{v.typeName}'")
  | .uadd =>
    match v with
    | .float value => .ok (.float value)
    | .ref _ =>
        .unsupported "unary '+' on a heap object is outside the H1 tier (docs/memory-model.md)"
    | v =>
      match asInt v with
      | some n => .ok (.int n)
      | Option.none => .exn (.typeError s!"bad operand type for unary +: '{v.typeName}'")
  | .invert =>
    match v with
    | .ref _ =>
        .unsupported "unary '~' on a heap object is outside the H1 tier (docs/memory-model.md)"
    | v =>
      match asInt v with
      | some n => .ok (.int (-n - 1))
      | Option.none => .exn (.typeError s!"bad operand type for unary ~: '{v.typeName}'")

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

/-- Remove the first binding of `name` (the one `Env.lookup` sees) — the
`del` statement's primitive (docs/memory-model.md §the del statement).
Structural recursion beside `lookup`/`set`; a missing name removes
nothing (the CALLERS decide the miss — the two arms decide it
differently, and neither reaches here on a miss). -/
def Env.remove : List (String × α) → String → List (String × α)
  | [], _ => []
  | (k, w) :: rest, name =>
    if k == name then rest else (k, w) :: Env.remove rest name

/-- Fold `del`'s targets LEFT TO RIGHT over an env — the PARTIAL effect
(CPython really removes `x` before raising on `nosuch` in
`del x, nosuch`): the env after every successful removal, plus the first
missing name if any. Pure; both runtime arms dispatch on the pair. -/
def delNames : List (String × α) → List String → List (String × α) × Option String
  | env, [] => (env, Option.none)
  | env, n :: rest =>
    match Env.lookup env n with
    | some _ => delNames (Env.remove env n) rest
    | Option.none => (env, some n)

/-- Constant literal → boundary value (G1 freeze side). -/
def Const.toVal : Const → Val
  | .none => .none
  | .ellipsis => .ellipsis
  | .bool b => .bool b
  | .int n => .int n
  | .float value => .float value
  | .str s => .str s
  | .bytes xs => .bytes xs

/-- Constant literal → runtime value (constants are scalars — no
allocation). -/
def Const.toRVal : Const → RVal
  | .none => .none
  | .ellipsis => .ellipsis
  | .bool b => .bool b
  | .int n => .int n
  | .float value => .float value
  | .str s => .str s
  | .bytes xs => .bytes xs

/-- `len(v)` for `str`/`listV`/`tuple` (str counts code points), else
`TypeError`; `len` of a `.ref` is a heap read (dicts) — loud until
H1-proper. -/
def lenVal : RVal → Res RVal
  | .str s => .ok (.int s.length)
  | .bytes xs => .ok (.int xs.size)
  | .listV xs => .ok (.int xs.size)
  | .tuple xs => .ok (.int xs.size)
  | .ntuple _ _ xs => .ok (.int xs.size)
  | .rangeV lo hi step => .ok (.int (rangeLen lo.toInt hi.toInt step.toInt))
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
  | .bytes values => do return .listV (← sortByLt desc (bytesIntVals values)).toArray
  | .tuple xs => do return .listV (← sortByLt desc xs.toList).toArray
  | .ntuple _ _ xs => do return .listV (← sortByLt desc xs.toList).toArray
  | .rangeV lo hi step => do
      return .listV (← sortByLt desc (← rangeVals lo.toInt hi.toInt step.toInt)).toArray
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
    | .bytes values => extremumOf isMax name (bytesIntVals values)
    | .rangeV lo hi step => do extremumOf isMax name (← rangeVals lo.toInt hi.toInt step.toInt)
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
  | .float value => .ok (.float value.abs)
  | .ref _ =>
      .unsupported "abs() of a heap object is outside the H1 tier (docs/memory-model.md)"
  | v => .exn (.typeError s!"bad operand type for abs(): '{v.typeName}'")

/-- pass 8 (docs/memory-model.md §the cast tier): is the character one of the
ASCII whitespace characters `int(<str>)` strips? -/
def intWs (character : Char) : Bool :=
  character == ' ' || character == '\t' || character == '\n' ||
    character == '\r' || character.toNat == 0x0b || character.toNat == 0x0c

/-- ASCII digit value in bases 2–36; 36 is the non-digit sentinel. -/
def intRadixDigit (character : Char) : Nat :=
  let code := character.toNat
  if 48 ≤ code && code ≤ 57 then code - 48
  else if 65 ≤ code && code ≤ 90 then code - 65 + 10
  else if 97 ≤ code && code ≤ 122 then code - 97 + 10
  else 36

/-- Structural radix parser; an underscore requires a digit on both sides. -/
def radixDigitsAux (base : Nat) : List Char → Nat → Bool → Option Nat
  | [], value, previousDigit => if previousDigit then some value else Option.none
  | character :: rest, value, previousDigit =>
      if intRadixDigit character < base then
        radixDigitsAux base rest (value * base + intRadixDigit character) true
      else if character == '_' && previousDigit then
        radixDigitsAux base rest value false
      else Option.none

/-- The decimal specialization of the shared digit walker. -/
def decimalDigitsAux := radixDigitsAux 10

/-- ASCII decimal digits, optionally grouped by single underscores, to a `Nat`. -/
def digitsToNat (characters : List Char) : Option Nat :=
  decimalDigitsAux characters 0 false

/-- Consume a matching binary/octal/hexadecimal prefix, including its optional
single underscore. Base zero also rejects nonzero, unprefixed leading zeroes. -/
def radixUnsigned (characters : List Char) (base : Nat) : Option Nat :=
  let radixPrefix := match characters with
    | '0' :: marker :: _ =>
      if marker == 'b' || marker == 'B' then 2
      else if marker == 'o' || marker == 'O' then 8
      else if marker == 'x' || marker == 'X' then 16
      else 0
    | _ => 0
  if radixPrefix != 0 && (base == 0 || base == radixPrefix) then
    let digits := characters.drop 2
    let digits := match digits with
      | '_' :: rest => rest
      | _ => digits
    radixDigitsAux radixPrefix digits 0 false
  else if base == 0 then
    (radixDigitsAux 10 characters 0 false).bind fun value =>
      if characters.head? == some '0' && value != 0 then Option.none else some value
  else radixDigitsAux base characters 0 false

/-- Parse the shared ASCII integer syntax after base validation and the
caller's character-inventory and digit-budget checks. -/
def radixInt (characters : List Char) (base : Nat) : Option Int :=
  let core := ((characters.dropWhile intWs).reverse.dropWhile intWs).reverse
  match core with
  | '+' :: digits => (radixUnsigned digits base).map Int.ofNat
  | '-' :: digits => (radixUnsigned digits base).map (fun value => -(value : Int))
  | digits => (radixUnsigned digits base).map Int.ofNat

/-- Decimal specialization, retaining the existing pure parsing surface. -/
def decimalInt (characters : List Char) : Option Int := radixInt characters 10

/-- Decimal conversion keeps its existing digit count; explicit other bases
bound all ASCII alphanumeric characters, including a possible prefix. -/
def intDigitCount (characters : List Char) (base : Nat) : Nat :=
  characters.countP (fun character =>
    if base == 10 then character.isDigit else intRadixDigit character < 36)

/-- `int(<str>, base)` decides integer syntax within `intDigitBudget`,
including base-zero prefixes, underscore grouping, and CPython's Unicode
decimal digits and whitespace. The shared float-text normalizer maps the
Unicode decimal and whitespace inventory to the ASCII grammar; other
non-ASCII characters remain malformed input and take CPython's exact
repr-rendered `ValueError` path. Invalid input is rendered with the same
200-character truncation used by CPython. -/
def intOfStr (text : String) (base : Nat := 10) : Res RVal :=
  let characters := text.toList.map Float64.normalizeDecimalChar
  if intDigitCount characters base > intDigitBudget then
    .exn decimalLimitError
  else
    match radixInt characters base with
    | some value => .ok (.int value)
    | Option.none =>
      match reprStr text with
      | some rendered =>
          .exn (.valueError s!"invalid literal for int() with base {base}: {String.ofList (rendered.toList.take 200)}")
      | Option.none =>
          .unsupported "int() cannot render this invalid literal exactly (docs/memory-model.md §the cast tier)"

/-- `int(bytes)` shares the ASCII decimal grammar with `int(str)`. Non-ASCII
octets are invalid input (CPython does not decode them as text), so they take
the same bytes-rendered `ValueError` path as other malformed forms. -/
def intOfBytes (values : Array UInt8) (base : Nat := 10) : Res RVal :=
  let octets := values.toList
  if intDigitCount (octets.map (fun octet => Char.ofNat octet.toNat)) base > intDigitBudget then
    .unsupported "int() of these bytes exceeds the tier's 4300-digit budget (CPython's configured conversion limit is not guessed; docs/memory-model.md §the cast tier)"
  else
    let characters := octets.map (fun octet => Char.ofNat octet.toNat)
    match radixInt characters base with
    | some value => .ok (.int value)
    | Option.none =>
      .exn (.valueError s!"invalid literal for int() with base {base}: {String.ofList ((bytesRepr values).toList.take 200)}")

/-- The `int` constructor builtin: identity on ints, bool coercion,
`int(<str>)` and the ASCII `int(bytes)` slice through the pass-8 honest
subset (`intOfStr`/`intOfBytes`); finite floats
truncate toward zero; a `.ref` is refused loudly before the `TypeError`
fallback. -/
def intCastVal : RVal → Res RVal
  | .int n => .ok (.int n)
  | .bool b => .ok (.int (if b then 1 else 0))
  | .float value =>
    match value.toInt with
    | some integer => .ok (.int integer)
    | none =>
      if value.isNaN then .exn (.valueError "cannot convert float NaN to integer")
      else .exn (.overflowError "cannot convert float infinity to integer")
  | .str s => intOfStr s
  | .bytes values => intOfBytes values
  | .ref _ =>
      .unsupported "int() of a heap object is outside the H1 tier (docs/memory-model.md)"
  | v => .exn (.typeError s!"int() argument must be a string, a bytes-like object or a real number, not '{v.typeName}'")

/-- Explicit-base conversion checks the base's index type and range before
the input type, matching CPython. Heap protocols remain loud. -/
def intCastBase (value base : RVal) : Res RVal :=
  match base with
  | .ref _ => .unsupported "int() with a heap-object base requires its __index__ protocol"
  | _ =>
    match asInt base with
    | none => .exn (.typeError s!"'{base.typeName}' object cannot be interpreted as an integer")
    | some radix =>
      if radix != 0 && (radix < 2 || radix > 36) then
        .exn (.valueError "int() base must be >= 2 and <= 36, or 0")
      else
        match value with
        | .str text => intOfStr text radix.toNat
        | .bytes values => intOfBytes values radix.toNat
        | .ref _ => .unsupported "int() of a heap object with explicit base is outside the tier"
        | _ => .exn (.typeError "int() can't convert non-string with explicit base")

/-- CPython's `int` call binder. Argument evaluation precedes this pure
worker; total argument count precedes keyword validation and conversion.
The string argument is positional-only and only `base` accepts a keyword. -/
def intCastArgs (values : List RVal) (keywords : List (String × RVal) := []) : Res RVal :=
  let count := values.length + keywords.length
  if count > 2 then
    let kind := if values.isEmpty then "keyword arguments" else "arguments"
    .exn (.typeError s!"int() takes at most 2 {kind} ({count} given)")
  else
    match keywords.find? (fun entry => entry.1 != "base") with
    | some (name, _) => .exn (.typeError s!"'{name}' is an invalid keyword argument for int()")
    | none =>
      match values, keywords with
      | [], [] => .ok (.int 0)
      | [], _ => .exn (.typeError "int() missing string argument")
      | [value], [] => intCastVal value
      | [value], [(_, base)] => intCastBase value base
      | [value, base], [] => intCastBase value base
      | _, _ => .unsupported "internal: int argument binder received duplicate base keywords (report this)"

def hexVal : RVal → Res RVal
  | .ref _ =>
      .unsupported "hex() of a heap object is outside the tier (docs/memory-model.md §the cast tier)"
  | v =>
    match asInt v with
    | some value =>
      match intHexPrefixed value with
      | some text => .ok (.str text)
      | Option.none =>
        .unsupported "hex() integer rendering beyond intDigitBudget is outside the tier (docs/memory-model.md §the cast tier)"
    | Option.none =>
      .exn (.typeError s!"'{v.typeName}' object cannot be interpreted as an integer")

def octVal : RVal → Res RVal
  | .ref _ =>
      .unsupported "oct() of a heap object is outside the tier (docs/memory-model.md §the cast tier)"
  | v =>
    match asInt v with
    | some value =>
      match intOctPrefixed value with
      | some text => .ok (.str text)
      | Option.none =>
        .unsupported "oct() integer rendering beyond intDigitBudget is outside the tier (docs/memory-model.md §the cast tier)"
    | Option.none =>
      .exn (.typeError s!"'{v.typeName}' object cannot be interpreted as an integer")

def binVal : RVal → Res RVal
  | .ref _ =>
      .unsupported "bin() of a heap object is outside the tier (docs/memory-model.md §the cast tier)"
  | v =>
    match asInt v with
    | some value =>
      match intBinPrefixed value with
      | some text => .ok (.str text)
      | Option.none =>
        .unsupported "bin() integer rendering beyond intDigitBudget is outside the tier (docs/memory-model.md §the cast tier)"
    | Option.none =>
      .exn (.typeError s!"'{v.typeName}' object cannot be interpreted as an integer")

mutual
  /-- ASCII-escaped repr for immediate containers. Heap-backed objects stay
  loud; these values carry their complete contents and need no heap lookup. -/
  def asciiReprVal : Nat → RVal → Option String
    | 0, _ => Option.none
    | fuel + 1, .int value => intDecimal value
    | fuel + 1, .float value => value.repr
    | fuel + 1, .bool b => some (if b then "True" else "False")
    | fuel + 1, .none => some "None"
    | fuel + 1, .ellipsis => some "Ellipsis"
    | fuel + 1, .str s => some (asciiStr s)
    | fuel + 1, .bytes values => some (bytesRepr values)
    | fuel + 1, .tuple xs => do
      let parts ← asciiReprVals fuel xs.toList
      if parts.length == 1 then
        return "(" ++ parts.head! ++ ",)"
      else return "(" ++ String.intercalate ", " parts ++ ")"
    | fuel + 1, .listV xs => do
      let parts ← asciiReprVals fuel xs.toList
      return "[" ++ String.intercalate ", " parts ++ "]"
    | fuel + 1, .ntuple _ _ _ | fuel + 1, .rangeV _ _ _ => Option.none
    | fuel + 1, .ref _ => Option.none

  def asciiReprVals : Nat → List RVal → Option (List String)
    | _, [] => some []
    | fuel, v :: vs => do
      let text ← asciiReprVal fuel v
      let rest ← asciiReprVals fuel vs
      return text :: rest
end

def asciiVal : RVal → Res RVal
  | .str s => .ok (.str (asciiStr s))
  | .tuple xs =>
    match asciiReprVal 128 (.tuple xs) with
    | some text => .ok (.str text)
    | Option.none => .unsupported "ascii() of an immediate container is outside the tier"
  | .listV xs =>
    match asciiReprVal 128 (.listV xs) with
    | some text => .ok (.str text)
    | Option.none => .unsupported "ascii() of an immediate container is outside the tier"
  | v =>
    match strFormatRepr v with
    | some text => .ok (.str text)
    | Option.none =>
      .unsupported s!"ascii() of '{v.typeName}' is outside the scalar tier (heap-recursive repr is not guessed; docs/memory-model.md §the cast tier)"

def floatCastVal : RVal → Res RVal
  | .float value => .ok (.float value)
  | .int integer => floatNumber (.int integer) >>= fun value => .ok (.float value)
  | .bool boolean => floatNumber (.bool boolean) >>= fun value => .ok (.float value)
  | .str text =>
    match Float64.fromText text with
    | .ok value => .ok (.float value)
    | .error .nanPayload =>
      .unsupported "float() textual NaN payload spelling requires an explicit payload oracle (docs/python-floats.md)"
    | .error .invalid =>
      match reprStr text with
      | some rendered => .exn (.valueError s!"could not convert string to float: {rendered}")
      | none => .unsupported "float() cannot render this invalid Unicode literal exactly (docs/python-floats.md)"
  | .bytes values =>
    if !values.toList.all (fun octet => octet.toNat < 128) then
      .unsupported "float() parsing of bytes containing non-ASCII octets is outside the tier"
    else
      let text := String.ofList (values.toList.map (fun octet => Char.ofNat octet.toNat))
      match Float64.fromText text with
      | .ok value => .ok (.float value)
      | .error .nanPayload =>
        .unsupported "float() textual NaN payload spelling requires an explicit payload oracle (docs/python-floats.md)"
      | .error .invalid =>
        .exn (.valueError s!"could not convert string to float: {bytesRepr values}")
  | .ref _ =>
    .unsupported "float() heap-object conversion protocols remain unmodelled (docs/python-floats.md)"
  | value => .exn (.typeError s!"float() argument must be a string or a number, not '{value.typeName}'")

/-- The heap-aware constructor boundary. Admitted classes cannot define a
`__float__` protocol, so a heap value in this tier has the ordinary CPython
non-numeric `TypeError`; a future protocol tier can replace this arm without
changing the scalar parser above. -/
def floatCastValH (h : Heap) : RVal → Res RVal
  | .ref a =>
      .exn (.typeError s!"float() argument must be a string or a number, not '{RVal.typeNameH h (.ref a)}'")
  | value => floatCastVal value

def floatCastArgsH (h : Heap) (arguments : List RVal) : Res RVal :=
  match arguments with
  | [] => .ok (.float (Float64.ofBits 0))
  | [value] => floatCastValH h value
  | _ => .exn (.typeError s!"float expected at most 1 argument, got {arguments.length}")

def floatCastArgs (arguments : List RVal) : Res RVal :=
  match arguments with
  | [] => .ok (.float (Float64.ofBits 0))
  | [value] => floatCastVal value
  | _ => .exn (.typeError s!"float expected at most 1 argument, got {arguments.length}")


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
  | .bytes values =>
    if values.size = 1 then .ok (.int (values.getD 0 0).toNat)
    else .exn (.typeError s!"ord() expected a character, but string of length {values.size} found")
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

/-- `sum(x)` / `sum(x, start)` argument split; `none` = wrong arity. -/
def sumArgs : List RVal → Option (RVal × RVal)
  | [v] => some (v, .int 0)
  | [v, start] => some (v, start)
  | _ => Option.none

/-- The element fold of `sum` IS `evalBinOp .add` (pass 3): int and
tuple sums are exactly Python's `+`, and a mixed-type step raises its
faithful `TypeError`. Structural on the list (kernel-reducible). -/
def sumFold (acc : RVal) : List RVal → Res RVal
  | [] => .ok acc
  | v :: vs => do sumFold (← evalBinOp .add acc v) vs

-- `isBuiltinName` / `isPyBuiltinName` moved VERBATIM to `Ast.lean`
-- (2026-08-14, docs/memory-model.md §module-level def aliasing): the
-- ingestion census consults them, and `Json.lean` cannot import this file.

/-- The synthetic builtins ingestion lowers dict views and `del d[k]` to
(`dictViewBuiltinName`/`dictDelBuiltinName`, Ast.lean), as one test. THIS
interpreter does not model them — only the runner's (`Monadic/Eval.lean`)
does — so its `NameError`-deciding arms consult this before deciding: the
name is unspellable, so CPython never sees it unbound, and a `NameError`
here is a wrong answer (measured 2026-09-24: 25 rows of `harness/cases.json`
— `len(d.keys())`, `del d[k]`, … — answered `NameError` when this
interpreter was run as the runner). Kept separate from `isPyBuiltinName`,
which stays the pinned CPython `dir(builtins)`. -/
def isLoweredBuiltinName (id : String) : Bool :=
  id == dictDelBuiltinName || id == attrDelBuiltinName || id == "<dictkeys>" || id == "<dictvalues>" ||
  id == "<dictitems>" || id == lenMultBuiltinName || id == fstringFormatBuiltinName

/-- The refusal a name-resolution arm owes an UNMODELLED CPython builtin
(see `isPyBuiltinName`) — the message names the construct, never a
fabricated `NameError`. -/
def unmodelledBuiltinMsg (id : String) : String :=
  if isLoweredBuiltinName id then
    s!"'{id}' (a synthetic ingestion builtin) is not modelled by the proof interpreter — outside its tier"
  else
  s!"builtin '{id}' exists in CPython but is not modelled — outside the tier (a NameError here would be a wrong answer for a name CPython binds)"

/-! ### `print` — the one effect the interpreter performs
(docs/memory-model.md §effects: stdout is DATA, `World.stdout`). -/

/-- `", "`-join. -/
def commaJoin : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ ", " ++ commaJoin xs

/-- `name=value` pairs for a namedtuple's `repr`. -/
def zipNames : List String → List String → List String
  | [], _ => []
  | _, [] => []
  | n :: ns, v :: vs => (n ++ "=" ++ v) :: zipNames ns vs

/-- Allocate a fresh heap dict holding `entries` and return its `.ref` —
the dict-display idiom (`BUILD_MAP`), shared with the `dict(…)`
constructor, which CPython also guarantees to be a NEW mapping. -/
def allocDictRun (st : FrameState) (entries : Array (RVal × RVal)) : Run FrameState RVal :=
  .ok { st with world := { st.world with heap := st.world.heap.push (.dict entries 0) } }
    (.ref st.world.heap.size)

/-! `print` renders through CPython's own two-level rule: the ARGUMENTS
go through `str()`, and every value INSIDE a container goes through
`repr()`. The two differ on exactly one shape — `str("a")` is `a` while
`repr("a")` is `'a'` — which is why `print(["a"])` shows quotes and
`print("a")` does not. Everything the tier cannot render EXACTLY refuses
loudly: a set (hash order), an instance/closure/generator (identity in
 the address), and a structure deeper than `reprFuel`. Unicode strings use the same
 CPython 3.9 printability table as `reprStr`. The
SCALAR half of the rule — `strOfVal` and a str's `reprStr` — lives above
the operator block (§scalar rendering), because the `%` operator needs
it and `evalBinOp` comes first in this file; what follows is the
heap-recursive half built on top of it. -/

/-- Depth budget for `repr` — FIXED (the loudness doctrine: a budget
refusal must not depend on the caller's fuel). Cycles are caught by the
active-path list instead, faithfully. -/
def reprFuel : Nat := 512

/-! Decimal-limit detection follows the same bounded active-path traversal as
`reprVal`, but keeps the renderer's existing `Option` interface intact. This
lets a nested integer raise CPython's ValueError instead of being conflated with
an unrelated loud rendering boundary. -/
mutual
  def decimalOverflowValH (h : Heap) (fuel : Nat) (active : List Addr) : RVal → Bool
    | .int value => decimalOverflowImmediate (.int value)
    | .tuple xs =>
      match fuel with
      | 0 => false
      | fuel + 1 => decimalOverflowValsH h fuel active xs.toList
    | .ntuple _ _ xs =>
      match fuel with
      | 0 => false
      | fuel + 1 => decimalOverflowValsH h fuel active xs.toList
    | .listV xs =>
      match fuel with
      | 0 => false
      | fuel + 1 => decimalOverflowValsH h fuel active xs.toList
    | .rangeV lo hi step =>
      decimalOverflowImmediate lo.toRVal ||
        decimalOverflowImmediate hi.toRVal || decimalOverflowImmediate step.toRVal
    | .ref a =>
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if active.contains a then false
        else
          match Heap.get? h a with
          | some (.list xs) => decimalOverflowValsH h fuel (a :: active) xs.toList
          | some (.dict entries _) => decimalOverflowEntriesH h fuel (a :: active) entries.toList
          | some (.dictView da kind) =>
            match Heap.get? h da with
            | some (.dict entries _) =>
              let elems := match kind with
                | .keys => entries.map Prod.fst
                | .values => entries.map Prod.snd
                | .items => entries.map (fun kv : RVal × RVal => .tuple #[kv.1, kv.2])
              decimalOverflowValsH h fuel (a :: active) elems.toList
            | _ => false
          | _ => false
    | _ => false

  def decimalOverflowValsH (h : Heap) (fuel : Nat) (active : List Addr) :
      List RVal → Bool
    | [] => false
    | v :: vs => decimalOverflowValH h fuel active v || decimalOverflowValsH h fuel active vs

  def decimalOverflowEntriesH (h : Heap) (fuel : Nat) (active : List Addr) :
      List (RVal × RVal) → Bool
    | [] => false
    | (k, v) :: rest =>
      decimalOverflowValH h fuel active k || decimalOverflowValH h fuel active v ||
        decimalOverflowEntriesH h fuel active rest
end

/-- Render a retained range field through the canonical scalar renderer. -/
def rangeBoundRepr (bound : RangeBound) : Option String :=
  match strOfVal bound.toRVal with
  | .ok (.str text) => some text
  | _ => Option.none

/-- The narrow exact set-rendering slice.  CPython 3.9 prints an empty set as
`set()` and an increasing small-integer set in that same order; arbitrary
hash-table orders remain outside the renderer. -/
def setReprIncreasing : List RVal → Bool
  | [] | [_] => true
  | .int x :: (.int y :: rest) => x < y && setReprIncreasing (.int y :: rest)
  | _ => false

def setReprSafe (xs : Array RVal) : Bool :=
  setReprIncreasing xs.toList

mutual
  /-- CPython `repr` of an in-tier value. `active` is the chain of heap
  addresses currently being rendered: CPython prints `[...]` / `{...}`
  for a container that contains itself, and so does this. -/
  def reprVal (h : Heap) (fuel : Nat) (active : List Addr) : RVal → Option String
    | .int value => intDecimal value
    | .float value => value.repr
    | .bool b => some (if b then "True" else "False")
    | .none => some "None"
    | .ellipsis => some "Ellipsis"
    | .str t => reprStr t
    | .bytes xs => some (bytesRepr xs)
    | .tuple xs => do
      match fuel with
      | 0 => Option.none
      | fuel + 1 =>
        let parts ← reprVals h fuel active xs.toList
        if parts.length == 1 then
          return "(" ++ parts.foldl (· ++ ·) "" ++ ",)"
        else return "(" ++ commaJoin parts ++ ")"
    | .ntuple tname fields xs => do
      match fuel with
      | 0 => Option.none
      | fuel + 1 =>
        let parts ← reprVals h fuel active xs.toList
        return tname ++ "(" ++ commaJoin (zipNames fields.toList parts) ++ ")"
    | .listV xs => do
      match fuel with
      | 0 => Option.none
      | fuel + 1 =>
        let parts ← reprVals h fuel active xs.toList
        return "[" ++ commaJoin parts ++ "]"
    | .rangeV lo hi step => do
      let start ← rangeBoundRepr lo
      let stop ← rangeBoundRepr hi
      if step.toInt == 1 then return "range(" ++ start ++ ", " ++ stop ++ ")"
      else
        let stride ← rangeBoundRepr step
        return "range(" ++ start ++ ", " ++ stop ++ ", " ++ stride ++ ")"
    | .ref a =>
      match fuel with
      | 0 => Option.none
      | fuel + 1 =>
        match Heap.get? h a with
        | some (.list xs) =>
          if active.contains a then some "[...]"
          else do
            let parts ← reprVals h fuel (a :: active) xs.toList
            return "[" ++ commaJoin parts ++ "]"
        | some (.dict entries _) =>
          if active.contains a then some "{...}"
          else do
            let parts ← reprEntries h fuel (a :: active) entries.toList
            return "{" ++ commaJoin parts ++ "}"
        | some (.dictView da kind) =>
          let name := match kind with
            | .keys => "dict_keys"
            | .values => "dict_values"
            | .items => "dict_items"
          if active.contains a then some (name ++ "([...])")
          else do
            let es ← match Heap.get? h da with
              | some (.dict es _) => some es
              | _ => Option.none
            let elems := match kind with
              | .keys => es.map Prod.fst
              | .values => es.map Prod.snd
              | .items => es.map (fun kv : RVal × RVal => .tuple #[kv.1, kv.2])
            let parts ← reprVals h fuel (a :: active) elems.toList
            return name ++ "([" ++ commaJoin parts ++ "])"
        | some (.pyset xs) =>
          -- A set's general repr is hash-table order.  The first exact
          -- renderer slice is the deterministic CPython shape whose stored
          -- integer elements are already in increasing order; every other
          -- order remains loud rather than guessing a hash layout.
          if setReprSafe xs then
            if xs.isEmpty then some "set()" else do
              let parts ← reprVals h fuel (a :: active) xs.toList
              return "{" ++ commaJoin parts ++ "}"
          else Option.none
        | _ => Option.none

  /-- Elementwise `reprVal`. -/
  def reprVals (h : Heap) (fuel : Nat) (active : List Addr) :
      List RVal → Option (List String)
    | [] => some []
    | v :: vs => do
      let a ← reprVal h fuel active v
      let rest ← reprVals h fuel active vs
      return a :: rest

  /-- `key: value` pairs of a dict, in INSERTION order (which the model
  preserves, so it is CPython's own order). -/
  def reprEntries (h : Heap) (fuel : Nat) (active : List Addr) :
      List (RVal × RVal) → Option (List String)
    | [] => some []
    | (k, v) :: rest => do
      let ks ← reprVal h fuel active k
      let vs ← reprVal h fuel active v
      let more ← reprEntries h fuel active rest
      return (ks ++ ": " ++ vs) :: more
end

mutual
  /-- CPython's `ascii()` rendering over the same heap-backed container
  inventory as `reprVal`. The only difference is that every string leaf is
  escaped with `asciiStr`; active-path cycle markers and the fixed depth
  budget remain identical to `repr`. -/
  def asciiReprValH (h : Heap) (fuel : Nat) (active : List Addr) :
      RVal → Option String
    | .int value => intDecimal value
    | .float value => value.repr
    | .bool b => some (if b then "True" else "False")
    | .none => some "None"
    | .ellipsis => some "Ellipsis"
    | .str t => some (asciiStr t)
    | .bytes xs => some (bytesRepr xs)
    | .tuple xs => do
      match fuel with
      | 0 => Option.none
      | fuel + 1 =>
        let parts ← asciiReprValsH h fuel active xs.toList
        if parts.length == 1 then
          return "(" ++ parts.head! ++ ",)"
        else return "(" ++ commaJoin parts ++ ")"
    | .ntuple tname fields xs => do
      match fuel with
      | 0 => Option.none
      | fuel + 1 =>
        let parts ← asciiReprValsH h fuel active xs.toList
        return tname ++ "(" ++ commaJoin (zipNames fields.toList parts) ++ ")"
    | .listV xs => do
      match fuel with
      | 0 => Option.none
      | fuel + 1 =>
        let parts ← asciiReprValsH h fuel active xs.toList
        return "[" ++ commaJoin parts ++ "]"
    | .rangeV lo hi step => do
      let start ← rangeBoundRepr lo
      let stop ← rangeBoundRepr hi
      if step.toInt == 1 then return "range(" ++ start ++ ", " ++ stop ++ ")"
      else
        let stride ← rangeBoundRepr step
        return "range(" ++ start ++ ", " ++ stop ++ ", " ++ stride ++ ")"
    | .ref a =>
      match fuel with
      | 0 => Option.none
      | fuel + 1 =>
        match Heap.get? h a with
        | some (.list xs) =>
          if active.contains a then some "[...]"
          else do
            let parts ← asciiReprValsH h fuel (a :: active) xs.toList
            return "[" ++ commaJoin parts ++ "]"
        | some (.dict entries _) =>
          if active.contains a then some "{...}"
          else do
            let parts ← asciiReprEntriesH h fuel (a :: active) entries.toList
            return "{" ++ commaJoin parts ++ "}"
        | _ => Option.none

  def asciiReprValsH (h : Heap) (fuel : Nat) (active : List Addr) :
      List RVal → Option (List String)
    | [] => some []
    | v :: vs => do
      let text ← asciiReprValH h fuel active v
      let rest ← asciiReprValsH h fuel active vs
      return text :: rest

  def asciiReprEntriesH (h : Heap) (fuel : Nat) (active : List Addr) :
      List (RVal × RVal) → Option (List String)
    | [] => some []
    | (k, v) :: rest => do
      let ks ← asciiReprValH h fuel active k
      let vs ← asciiReprValH h fuel active v
      let more ← asciiReprEntriesH h fuel active rest
      return (ks ++ ": " ++ vs) :: more
end

def asciiValH (h : Heap) (v : RVal) : Res RVal :=
  if decimalOverflowValH h reprFuel [] v then
    .exn decimalLimitError
  else
    match asciiReprValH h reprFuel [] v with
    | some text => .ok (.str text)
    | Option.none =>
      .unsupported s!"ascii() of '{v.typeName}' is outside the tier (its rendering refuses; docs/memory-model.md §the cast tier)"

/-- CPython `str()` of a value as `print` sees it: a str prints RAW,
everything else through `repr`. -/
def printOne (h : Heap) (v : RVal) : Option String :=
  match v with
  | .str t => some t
  | v => reprVal h reprFuel [] v

/-- `str(…)` over the heap: immediates keep `strOfVal`'s exact normal
form; containers and refs render through `printOne` (CPython's two-level
`str` rule, §rendering). The cast tier's original refusal reason —
"repr recursion is not guessed" — expired the day §rendering landed,
so this widening deletes a stale restriction rather than adding a
capability. An unrenderable value (set/instance/non-ASCII inside a
container) refuses with the rendering boundary's own reason. -/
def strOfValH (h : Heap) (v : RVal) : Res RVal :=
  match v with
  | .int _ | .bool _ | .str _ | .none => strOfVal v
  | v =>
    if decimalOverflowValH h reprFuel [] v then
      .exn decimalLimitError
    else
      match printOne h v with
      | some s => .ok (.str s)
      | Option.none => .unsupported s!"str() of '{v.typeName}' is outside the tier (its rendering refuses; docs/memory-model.md §rendering)"

def reprArgs (h : Heap) (vs : List RVal) : Res RVal :=
  match vs with
  | [v] =>
    if decimalOverflowValH h reprFuel [] v then
      .exn decimalLimitError
    else
      match reprVal h reprFuel [] v with
      | some text => .ok (.str text)
      | Option.none => .unsupported s!"repr() of '{v.typeName}' is outside the tier (its rendering refuses; docs/memory-model.md §rendering)"
  | vs => .exn (.typeError s!"repr() takes exactly one argument ({vs.length} given)")

def formatValueH (heap : Heap) (value : RVal) (reprConversion : Bool) : Res RVal :=
  if reprConversion then reprArgs heap [value] else strOfValH heap value

/-- The measured non-empty format specification rung: bare decimal `d` for
integers and Booleans. The full format mini-language and non-integral
protocols remain loud until their grammar is represented. -/
def formatSpecH (value : RVal) (spec : String) : Res RVal :=
  if spec == "d" || spec == ">5" || spec == "03d" then
    match value with
    | .int n =>
        match intDecimal n with
        | some text =>
            let rendered :=
              if spec == ">5" then padFormatField 5 text
              else if spec == "03d" then zeroPadFormatField 3 text
              else text
            .ok (.str rendered)
        | Option.none => .exn decimalLimitError
    | .bool b =>
        let text := if b then "1" else "0"
        let rendered :=
          if spec == ">5" then padFormatField 5 text
          else if spec == "03d" then zeroPadFormatField 3 text
          else text
        .ok (.str rendered)
    | _ => .unsupported "format() with this value/specification is outside the tier (only d, >5, and 03d for int/bool are modeled)"
  else
    .unsupported "format() with a non-empty format specification is outside the tier"

/-- Space-join `print` arguments (CPython's default `sep`); the first
unrenderable one wins. `print()` is the empty line. -/
def strOfArgs (h : Heap) : List RVal → Option String
  | [] => some ""
  | [v] => printOne h v
  | v :: vs => do
    let s ← printOne h v
    let rest ← strOfArgs h vs
    return s ++ " " ++ rest

/-- The first measured complex-literal slice.  The extractor keeps complex
constants as `Unsupported` because the runtime has no complex value type.
The one observation that needs no such value is the exact grammar witness
`print(1j)`: CPython's `str(1j)` is the literal text `"1j"`.  This helper is
consulted only after ordinary builtin name resolution has selected `print`,
so a shadowing local/module binding still evaluates the unsupported node and
remains loud.  Other complex spellings and every non-print use stay loud. -/
def complexPrintLiteral : Expr → Option RVal
  | .unsupported pyKind text _ =>
      if pyKind == "Constant:complex" && text == "1j" then
        some (.str "1j")
      else
        Option.none
  | _ => Option.none

/-- Rewrite the one admitted print argument to an ordinary string expression
before evaluation.  Keeping this as a pure list transform means all existing
fuel, clock, and world-invariance proofs continue to use `evalExprs` without
an extra recursive worker. -/
def complexPrintArgs : List Expr → List Expr
  | [e] =>
      match complexPrintLiteral e with
      | some (.str text) => [.constant (.str text) default]
      | _ => [e]
  | es => es

/-- Allocate a fresh heap list holding `xs` and return its `.ref` — the
list-display idiom (`BUILD_LIST`: the fresh address is the old heap
size), shared with the `list(…)` constructor, which CPython also
guarantees to be a NEW object, never an alias. -/
def allocListRun (st : FrameState) (xs : Array RVal) : Run FrameState RVal :=
  .ok { st with world := { st.world with heap := st.world.heap.push (.list xs) } }
    (.ref st.world.heap.size)

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

def rangeIndex (lo hi step : Int) (index : RVal) : Res RVal :=
  match asInt index with
  | some i =>
    match normIndex i (rangeLen lo hi step) with
    | some n => .ok (.int (lo + step * (n : Int)))
    | Option.none => .exn .indexErrorRange
  | Option.none =>
    .exn (.typeError s!"range indices must be integers or slices, not {index.typeName}")

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
  | .rangeV lo hi step, index => rangeIndex lo.toInt hi.toInt step.toInt index
  | .listV xs, index =>
    match asInt index with
    | some i =>
      match normIndex i xs.size with
      | some n => .ok (xs.getD n .none)
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"list indices must be integers, not {index.typeName}")
  | .bytes xs, index =>
    match asInt index with
    | some integer =>
      match normIndex integer xs.size with
      | some position => .ok (.int (xs.getD position 0).toNat)
      | Option.none => .exn .indexErrorBytes
    | Option.none =>
      .exn (.typeError s!"byte indices must be integers or slices, not {typeNamePrefix index.typeName 200}")
  | .tuple xs, index =>
    match asInt index with
    | some i =>
      match normIndex i xs.size with
      | some n => .ok (xs.getD n .none)
      | Option.none => .exn .indexErrorTuple
    | Option.none =>
      .exn (.typeError s!"tuple indices must be integers, not {index.typeName}")
  | .ntuple _ _ xs, index =>
    -- namedtuple subscripting IS tuple subscripting (tuple.__getitem__ —
    -- the error message names 'tuple', exactly as CPython's does)
    match asInt index with
    | some i =>
      match normIndex i xs.size with
      | some n => .ok (xs.getD n .none)
      | Option.none => .exn .indexErrorTuple
    | Option.none =>
      .exn (.typeError s!"tuple indices must be integers, not {index.typeName}")
  | .str s, index =>
    match asInt index with
    | some i =>
      match normIndex i s.length with
      | some n => .ok (.str (String.singleton (s.toList.getD n ' ')))
      | Option.none => .exn .indexErrorString
    | Option.none =>
      .exn (.typeError s!"string indices must be integers, not {index.typeName}")
  | v, _ => .exn (.typeError s!"'{v.typeName}' object is not subscriptable")

/-! ## The string tier (H5 strings, docs/memory-model.md §string semantics)

Pure, fuel-free helpers: strings are immutable values, so the whole tier
has VALUE semantics — no heap, no aliasing, `worldInv`-trivial. The
case-mapping methods (`swapcase`/`isupper`) are in tier for ASCII
strings only: Lean core's `Char.isUpper`/`toLower`/… provide the ASCII
maps, and this tier adds the exact one-code-point Latin-1 case ranges;
characters outside that table remain loud because CPython consults the
full Unicode tables. `index` and slicing are code-point-exact for every
string.

Simp-set doctrine (the `sortInts`/`heapEq` freeze family): the DISPATCH
layers (`sliceVal`, `strCallPlan`) are in `py_simp`/`interpUnfolds`, the
VALUE workers (`strSlice`, `strSwapcase`, `strIsUpper`, `strIndex` and
their helpers) are deliberately OUT — symbolic goals keep the compact
`strSlice s l u st` handle, and concrete proofs rewrite through one
kernel-checked `have … := by rfl` fact per worker application instead of
thousands of character-level simp steps (concrete runs — `#py_check`,
the differential harness — reduce through the kernel/evaluator and never
consult simp sets). -/

/- Latin-1 input guard for the case-mapping methods. -/
def strLatin1 (s : String) : Bool :=
  s.toList.all (fun c => c.toNat < 256)

def latin1Upper (c : Char) : Bool :=
  c.isUpper || (192 ≤ c.val.toNat && c.val.toNat ≤ 214) ||
    (216 ≤ c.val.toNat && c.val.toNat ≤ 222)

def latin1Lower (c : Char) : Bool :=
  c.isLower || c.val.toNat == 181 || c.val.toNat == 223 ||
    (224 ≤ c.val.toNat && c.val.toNat ≤ 246) ||
    (248 ≤ c.val.toNat && c.val.toNat ≤ 255)

def latin1Alpha (c : Char) : Bool := latin1Upper c || latin1Lower c

def latin1SwapChar (c : Char) : Option (List Char) :=
  if latin1Upper c then some [Char.ofNat (c.val.toNat + 32)]
  else if latin1Lower c then
    if c.val.toNat == 181 then some [Char.ofNat 924]
    else if c.val.toNat == 223 then some ['S', 'S']
    else if c.val.toNat == 255 then some [Char.ofNat 376]
    else some [Char.ofNat (c.val.toNat - 32)]
  else some [c]

def latin1UpperChar (c : Char) : Option (List Char) :=
  if latin1Lower c then
    if c.val.toNat == 181 then some [Char.ofNat 924]
    else if c.val.toNat == 223 then some ['S', 'S']
    else if c.val.toNat == 255 then some [Char.ofNat 376]
    else some [Char.ofNat (c.val.toNat - 32)]
  else some [c]

/-- `swapcase` on one Latin-1 character, including CPython's multi-character
case mappings for sharp s. -/
def swapChar (c : Char) : Char :=
  if c.isUpper then c.toLower else if c.isLower then c.toUpper else c

/-- `s.swapcase()` for the admitted Latin-1 input table. -/
def strSwapcase (s : String) : Res RVal :=
  if strLatin1 s then
    match s.toList.mapM latin1SwapChar with
    | some css => .ok (.str (String.ofList css.flatten))
    | Option.none => .unsupported "swapcase() of a Latin-1 character is outside the case table"
  else .unsupported
    "swapcase() outside the Latin-1 case table is outside the tier (Unicode case tables; docs/memory-model.md §string semantics)"

/-- `s.isupper()`: at least one cased character and no lowercase one
(CPython's definition over the admitted Latin-1 table). -/
def strIsUpper (s : String) : Res RVal :=
  if strLatin1 s then
    .ok (.bool (s.toList.any latin1Alpha &&
                s.toList.all (fun c => !latin1Alpha c || latin1Upper c)))
  else .unsupported
    "isupper() outside the Latin-1 case table is outside the tier (Unicode case tables; docs/memory-model.md §string semantics)"

/-- `s.islower()` (the mirror of `strIsUpper` — H6: sunfish's
`value()` capture check `q.islower()`). -/
def strIsLower (s : String) : Res RVal :=
  if strLatin1 s then
    .ok (.bool (s.toList.any latin1Alpha &&
                s.toList.all (fun c => !latin1Alpha c || latin1Lower c)))
  else .unsupported
    "islower() outside the Latin-1 case table is outside the tier (Unicode case tables; docs/memory-model.md §string semantics)"

/-- `s.upper()` for the admitted Latin-1 input table — H6: sunfish's
`value()` capture lookup `pst[q.upper()]`. -/
def strUpper (s : String) : Res RVal :=
  if strLatin1 s then
    match s.toList.mapM latin1UpperChar with
    | some css => .ok (.str (String.ofList css.flatten))
    | Option.none => .unsupported "upper() of a Latin-1 character is outside the case table"
  else .unsupported
    "upper() outside the Latin-1 case table is outside the tier (Unicode case tables; docs/memory-model.md §string semantics)"

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

/-! `str.join` consumes an iterable without running user code between items.
The supported sequence and heap containers are already represented by the
runtime, so this worker can read them directly; generators and sets retain
their stateful/hash-order refusal. -/
def strJoinList (sep : String) : List RVal → Res RVal
  | [] => .ok (.str "")
  | v :: rest =>
    match v with
    | .str first =>
      let rec go (acc : String) : List RVal → Res String
        | [] => .ok acc
        | x :: xs =>
          match x with
          | .str text => go (acc ++ sep ++ text) xs
          | _ => .exn (.typeError
              s!"sequence item {rest.length - xs.length}: expected str instance, {x.typeName} found")
      go first rest >>= fun text => .ok (.str text)
    | _ => .exn (.typeError
        s!"sequence item 0: expected str instance, {v.typeName} found")

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

/-- Search at most `limit` positions in a string.  The returned index is
relative to the supplied list; callers add the normalized start bound. -/
def strFindLimited (hay needle : List Char) : Nat → Option Nat
  | 0 => if needle.isPrefixOf hay then some 0 else Option.none
  | n + 1 =>
    if needle.isPrefixOf hay then some 0
    else
      match hay with
      | [] => Option.none
      | _ :: rest => (strFindLimited rest needle n).map (· + 1)

/-- `s.index(sub, start[, end])`: normalize the bounds like a forward
slice, then search only positions whose complete match lies before `end`.
The needle type is checked by the caller before this worker, matching
CPython's validation order. -/
def strIndexBounds (s sub : String) (start stop : RVal) : Res RVal :=
  match asSliceIdx start, asSliceIdx stop with
  | some ls, some le =>
    let len : Int := s.length
    let lo := match ls with | some i => sliceAdj i len true | Option.none => 0
    let hi := match le with | some i => sliceAdj i len true | Option.none => len
    if hi < lo then .exn (.valueError "substring not found")
    else
      let span := (hi - lo).toNat
      let needleLen := sub.length
      if needleLen > span then .exn (.valueError "substring not found")
      else
        match strFindLimited (s.toList.drop lo.toNat) sub.toList (span - needleLen) with
        | some i => .ok (.int (lo.toNat + i))
        | Option.none => .exn (.valueError "substring not found")
  | _, _ => .exn (.typeError "slice indices must be integers or None or have an __index__ method")

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

/-- Collect `n` elements starting at index `i`, stepping by `step` — the
`strSliceChars` shape over runtime values (every visited index in range
by construction; `getD`'s default unreachable). -/
def seqSliceElems (xs : Array RVal) : Nat → Int → Int → List RVal
  | 0, _, _ => []
  | n + 1, i, step => xs.getD i.toNat .none :: seqSliceElems xs n (i + step) step

/-- `xs[lower:upper:step]` on a value tuple (pass 3): CPython slice
semantics, the `strSlice` validation VERBATIM (step first — `TypeError`
for a non-index, `ValueError` for 0 — then lower, then upper; the
duplication is deliberate: `strSlice` is a frozen proof-layer worker and
must stay byte-identical). Result: a PLAIN tuple. -/
def seqSliceValues (xs : Array RVal) (lv uv sv : RVal) : Res (List RVal) :=
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
          let len : Int := xs.size
          let pos := 0 < step
          let start := match l with
            | some i => sliceAdj i len pos
            | Option.none => if pos then 0 else len - 1
          let stop := match u with
            | some i => sliceAdj i len pos
            | Option.none => if pos then len else -1
          .ok (seqSliceElems xs (sliceCount start stop step) start step)

def seqSlice (xs : Array RVal) (lv uv sv : RVal) : Res RVal :=
  seqSliceValues xs lv uv sv >>= fun values =>
    .ok (.tuple values.toArray)

def seqSliceList (xs : Array RVal) (lv uv sv : RVal) : Res RVal :=
  seqSliceValues xs lv uv sv >>= fun values =>
    .ok (.listV values.toArray)

def bytesSlice (xs : Array UInt8) (lv uv sv : RVal) : Res RVal :=
  let values := xs.toList.map (fun byte => .int byte.toNat)
  seqSliceValues values.toArray lv uv sv >>= fun selected =>
    .ok (.bytes (selected.map (fun value =>
      match value with
      | .int integer => UInt8.ofNat integer.toNat
      | _ => 0)).toArray)

/-- `container[l:u:st]` — the slice RECEIVER dispatch (the components
have already evaluated: CPython builds the slice object before
`BINARY_SUBSCR` looks at the receiver). STRINGS and value lists are handled
by pure workers; heap-list receivers are copied by the monadic runner into a
fresh list object. Tuple/namedtuple slices remain immediate values; a
non-subscriptable receiver is the faithful
`TypeError`. -/
def sliceVal (v lv uv sv : RVal) : Res RVal :=
  match v with
  | .str s => strSlice s lv uv sv
  | .bytes xs => bytesSlice xs lv uv sv
  | .ref _ =>
    .unsupported "slicing a heap object is outside the tier (a list slice allocates; docs/memory-model.md §string semantics)"
  | .listV xs => seqSliceList xs lv uv sv
  -- pass 3 (docs/memory-model.md §module-init execution): tuple slices
  -- are IN-MODEL allocation-free (tuples are immediate values), so the
  -- H5 refusal reason never applied to them; CPython's tuple.__getitem__
  -- exactly, and a namedtuple slice is a PLAIN tuple (the class does not
  -- survive slicing).
  | .tuple xs => seqSlice xs lv uv sv
  | .ntuple _ _ xs => seqSlice xs lv uv sv
  | .rangeV .. =>
    .unsupported "slicing a range is outside the tier (CPython yields a range; docs/memory-model.md §module-init execution)"
  | v => .exn (.typeError s!"'{v.typeName}' object is not subscriptable")

/-- Heap-aware slice dispatch. Heap-list slices allocate a fresh list object;
all value receivers reuse the pure worker above. -/
def sliceValH (h : Heap) (v lv uv sv : RVal) : Res (Heap × RVal) :=
  match v with
  | .ref a =>
      match Heap.get? h a with
      | some (.list xs) =>
          seqSliceValues xs lv uv sv >>= fun values =>
            .ok (h.push (.list values.toArray), .ref h.size)
      | _ => sliceVal v lv uv sv >>= fun r => .ok (h, r)
  | _ => sliceVal v lv uv sv >>= fun r => .ok (h, r)

/-- The decision of a method CALL on a str receiver (H5 strings) — the
`ntupleCallPlan` discipline: a PURE plan decided from the attribute name
alone, BEFORE argument evaluation. Everything outside the tier trio
refuses loudly — never a fake `AttributeError`: CPython's str carries
~45 real methods (`upper`/`split`/`join`/…) plus the dunder protocol,
and guessing which names exist would be silently wrong. -/
inductive StrPlan where
  | swapcase | isupper | islower | upper | index | join
  | refuse (msg : String)
deriving Repr, Inhabited, BEq

/-- Resolve `s.attr(…)` for a str receiver (see `StrPlan`). -/
def strCallPlan (attr : String) : StrPlan :=
  if attr == "swapcase" then .swapcase
  else if attr == "isupper" then .isupper
  else if attr == "islower" then .islower
  else if attr == "upper" then .upper
  else if attr == "index" then .index
  else if attr == "join" then .join
  else .refuse
    s!"method call '.{attr}' on a str is outside the tier ('swapcase'/'isupper'/'islower'/'upper'/'index'/'join' only; docs/memory-model.md §string semantics)"

/-! ## The dict tier (H1-proper, docs/memory-model.md)

Fuel-free heap helpers over the bounds-checked access primitives
(`Heap.get?`/`Heap.update`, Runtime.lean). A dangling address is an
interpreter invariant violation — unreachable from well-formed worlds —
and reports loudly (`danglingMsg`), never a silent fallback. -/

/-- §3c-i-a: a view call whose receiver is not a dict. The fused form is
admitted only over a real dict; anything else keeps the tier's refusal rather
than inventing an `AttributeError` for a receiver that may legitimately have
`.keys` in some later tier. -/
def viewRecvMsg : String :=
  "'.keys()'/'.values()'/'.items()' on a non-dict receiver is outside the tier (docs/memory-model.md §dict iteration)"

/-- §del: `del o[k]` where `o` is not a dict. The ingestion rewrite is
SYNTACTIC — it lowers `del o[k]` for ANY receiver — so the receiver's type is
decided HERE, exactly as it is for the view builtins. The refusal is honest
rather than a guessed exception: for a LIST CPython SUCCEEDS (item deletion,
a tier this model does not have), for a `str` it raises `TypeError`, and
inventing either would be answering for a receiver whose behaviour has not
been measured. `dict_lab::del_nondict_still_loud` is the witness. -/
def delRecvMsg : String :=
  "'del o[k]' on a non-dict receiver is outside the tier (dict item deletion only; docs/memory-model.md §the del statement)"

/-- §del: `del o.attr` on a non-instance receiver.  Builtins have no mutable
instance dictionary in this tier; closure attributes are left loud because
CPython permits user-assigned function attributes and a fabricated
`AttributeError` would be wrong. -/
def attrDelRecvMsg : String :=
  "'del o.attr' on a non-instance receiver is outside the tier (instance attribute deletion only; docs/memory-model.md §the del statement)"

/-- The loud report for a dangling address (unreachable from WF worlds). -/
def danglingMsg : String :=
  "internal: dangling heap address (heap well-formedness violation — report this)"

mutual
  /-- Is this runtime value usable as a dict key? Hashability, not
  immutability (docs/memory-model.md §dict semantics): scalars, including
  finite floats, are hashable; a tuple iff its elements are; lists are
  unhashable; a ref's
  hashability depends on its referent — every H1 heap object is a dict,
  which is unhashable (H3 instances revisit this arm, heap parameter and
  all). -/
  def hashableKey : RVal → Bool
    | .none | .ellipsis | .bool _ | .int _ | .str _ | .bytes _ => true
    | .float value => !value.isNaN && !value.isInf
    | .tuple xs => hashableKeyList xs.toList
    -- a namedtuple hashes as a tuple (tuple.__hash__): hashable iff its
    -- elements are — sunfish's `(pos, depth, root)` keys stay in tier
    | .ntuple _ _ xs => hashableKeyList xs.toList
    | .listV _ => false
    -- ranges ARE hashable in CPython — `false` routes to `keyRefusal`,
    -- whose range predicate keeps the refusal LOUD (never a fake
    -- unhashable `TypeError`)
    | .rangeV .. => false
    | .ref _ => false

  /-- Elementwise `hashableKey`. -/
  def hashableKeyList : List RVal → Bool
    | [] => true
    | v :: vs => hashableKey v && hashableKeyList vs
end

/-- CPython's type name in `unhashable type: '…'` messages. A `.ref` names
its referent's type — every H1 heap object is a dict. (H2: superseded by
the heap-resolving `RVal.typeNameH` in every reachable message position;
retained as pure vocabulary. `typeNameH` itself MOVED verbatim above the
range block on 2026-08-16 — `rangeMake` needs it and Lean has no forward
references; §rendering's other members are unchanged.) -/
def RVal.unhashName : RVal → String
  | .ref _ => "dict"
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
    | .ellipsis, .ellipsis => true
    | .bool a, .bool b => a == b
    | .bool a, .int m => (if a then (1 : Int) else 0) == m
    | .int n, .bool b => n == (if b then (1 : Int) else 0)
    | .int n, .int m => n == m
    | .float a, .float b => a.eqv b
    | .float a, .int n => a.eqInt n
    | .int n, .float a => a.eqInt n
    | .float a, .bool b => a.eqInt (if b then 1 else 0)
    | .bool b, .float a => a.eqInt (if b then 1 else 0)
    | .str s, .str t => s == t
    | .bytes left, .bytes right => left == right
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
      | some (.dictView ..) => true
      | some (.instance _ _) => true
      | some (.generator ..) => true
      | some (.cell _) => true
      | some (.closure ..) => true  -- identity hash, like instances: refuse
      | some (.pyset _) => false    -- sets are UNHASHABLE: the faithful TypeError path
      | _ => false
    | .tuple xs => keyHasInstanceRefList h xs.toList
    | .ntuple _ _ xs => keyHasInstanceRefList h xs.toList
    -- hashable in CPython (start/stop/step hash) — loud, never a fake
    -- unhashable TypeError (pass 3)
    | .rangeV .. => true
    | _ => false

  /-- Elementwise `keyHasInstanceRef`. -/
  def keyHasInstanceRefList (h : Heap) : List RVal → Bool
    | [] => false
    | v :: vs => keyHasInstanceRef h v || keyHasInstanceRefList h vs
end

mutual
  /-- The type CPython NAMES in `unhashable type: '…'` — the offending
  COMPONENT, not the key. MEASURED on 3.9.19, and the model had it wrong:
  `{(1, [2]): 0}` is `unhashable type: 'list'`, not `'tuple'`, because
  `tuple.__hash__` hashes its elements and the first element to raise is
  the one whose message escapes. So this mirrors `hashableKey`'s recursion
  arm for arm and reports the first member that fails; `none` means the
  key IS hashable and no message is owed. -/
  def unhashableName? (h : Heap) : RVal → Option String
    | .none | .bool _ | .int _ | .str _ | .bytes _ => Option.none
    | .tuple xs => unhashableNameList? h xs.toList
    | .ntuple _ _ xs => unhashableNameList? h xs.toList
    | v => some (RVal.typeNameH h v)

  /-- Left to right, first failure wins — CPython's hashing order. -/
  def unhashableNameList? (h : Heap) : List RVal → Option String
    | [] => Option.none
    | v :: vs =>
      match unhashableName? h v with
      | some n => some n
      | Option.none => unhashableNameList? h vs
end

/-- The outcome when a probe/key fails `hashableKey`: a dict/list
referent (or a value-list) is CPython's faithful `TypeError`; a key
containing an INSTANCE ref is hashable in CPython (identity hash +
identity `__eq__`) but instance dict keys are outside the H3 tier —
loud, never a fake `TypeError`.

The named type is the OFFENDING COMPONENT (`unhashableName?`), which for
a flat key is the key's own type and for a tuple is the member that
actually failed. `getD` supplies the key's own name for the arm the
caller's precondition makes unreachable — `keyRefusal` is only reached
when `hashableKey k = false`, and then the search always finds one. -/
def keyRefusal (h : Heap) (k : RVal) : Res α :=
  if k.hasNonFiniteFloat then
    .unsupported "non-finite float dictionary and set keys are outside the tier"
  else if keyHasInstanceRef h k then
    .unsupported "a class instance or generator as a dict key (identity hash) is outside the tier (docs/memory-model.md)"
  else
    .exn (.typeError
      s!"unhashable type: '{(unhashableName? h k).getD (RVal.typeNameH h k)}'")

/-- First entry whose stored key equals `k` (insertion order). -/
def dictFind : List (RVal × RVal) → RVal → Option RVal
  | [], _ => Option.none
  | (k', v') :: rest, k => if keyEq k' k then some v' else dictFind rest k

/-- The keys of a dict, in INSERTION ORDER — CPython's specified iteration
order since 3.7, which `entries` already is (a store replaces a present
key's value in place and appends an absent one, so the array IS the
insertion sequence).

This serves the DRAINING consumers only (`list`/`tuple`/`sorted`/`sum`/
`max`/`min`/`set`/`any`/`all`, §L53 rung 3b). They are sound where the
live cursor is delicate for one structural reason: they consume the keys
with NO user code running in between, so none of the three mutation
regimes the census measured (value update, size change, same-size key-set
churn) can arise inside them — docs/memory-model.md §dict iteration. -/
def dictKeys (es : Array (RVal × RVal)) : Array RVal := es.map Prod.fst

/-- §3c-i-b: the ELEMENT SEQUENCE a dict view presents, by kind — the keys,
the values, or the `(key, value)` pairs, all in insertion order. -/
def dictViewElems (es : Array (RVal × RVal)) (kind : DictViewKind) : Array RVal :=
  match kind with
  | .keys => es.map Prod.fst
  | .values => es.map Prod.snd
  | .items => es.map (fun kv => .tuple #[kv.1, kv.2])

/-- Resolve the dictionary retained by a live view. A non-dictionary target
is an invariant failure, never an empty view. -/
def dictViewEntries (h : Heap) (a : Addr) : Res (Array (RVal × RVal)) :=
  match Heap.get? h a with
  | some (.dict es _) => .ok es
  | _ => .unsupported danglingMsg

def strJoinH (h : Heap) (sep : String) : RVal → Res RVal
  | .str text => strJoinList sep (strCharVals text)
  | .bytes xs => strJoinList sep (bytesIntVals xs)
  | .tuple xs => strJoinList sep xs.toList
  | .ntuple _ _ xs => strJoinList sep xs.toList
  | .listV xs => strJoinList sep xs.toList
  | .rangeV lo hi step => rangeVals lo.toInt hi.toInt step.toInt >>= strJoinList sep
  | .ref a =>
    match Heap.get? h a with
    | some (.list xs) => strJoinList sep xs.toList
    | some (.dict es _) => strJoinList sep (dictKeys es).toList
    | some (.dictView da kind) =>
      dictViewEntries h da >>= fun es => strJoinList sep (dictViewElems es kind).toList
    | some (.generator ..) =>
      .unsupported "str.join() over a generator is outside the tier (consuming a generator is a stateful read)"
    | some (.pyset _) =>
      .unsupported "str.join() over a set is outside the tier (hash order; docs/memory-model.md)"
    | some (.instance _ _) | some (.closure ..) | some (.cell _) | Option.none =>
      .exn (.typeError "can only join an iterable")
  | _ => .exn (.typeError "can only join an iterable")

/-- §3c-i-b: the kind a synthetic view builtin stands for (`Ast.lean`
§the dict-view ingestion rewrite emits these names). -/
def dictViewBuiltinKind : String → Option DictViewKind
  | "<dictkeys>" => some .keys
  | "<dictvalues>" => some .values
  | "<dictitems>" => some .items
  | _ => Option.none

/-- §3a THE DICT CURSOR'S STEP DECISION, as a PURE PLAN.

The free-scrutinee discipline is not decoration here: AGENTS.md records that
`execGen` MUST fork on a pure plan (`genPlan`'s precedent), because with the
match inline the equation compiler splits the arm per constructor and
`simp only [execGen]` never fires at a symbolic frame. The same reason gives
the two cursors — `execGen`'s and the script shell's — ONE decision instead of
two `if` chains that could drift.

The three regimes are §L53's measurements against CPython 3.9.19:
`resized` is the faithful `RuntimeError`, `rekeyed` is LOUD (CPython's answer
depends on its entries-array layout), `yield` is the key at the cursor. -/
inductive DictStep where
  /-- The size changed: `RuntimeError: dictionary changed size during iteration`. -/
  | resized
  /-- Same size, different `shapeVersion` — a key-set change. Never guessed. -/
  | rekeyed
  /-- What the cursor yields at this step — the key, the value, or the
  `(key, value)` pair, per the view kind. -/
  | yieldVal (v : RVal)
  /-- The cursor ran off the end. -/
  | done
deriving Repr, Inhabited, BEq

/-- The plan, from what the step FINDS (`es`, `sv'`) against what the loop
STARTED with (`n`, `sv`), at cursor `i`. A value update of an existing key
bumps neither `size` nor `shapeVersion` (`dictStore` grows the version on
insertion only), so it slips past both guards — exactly as CPython allows. -/
def dictStep (es : Array (RVal × RVal)) (sv' i n sv : Nat)
    (kind : DictViewKind) : DictStep :=
  if es.size ≠ n then .resized
  else if sv' ≠ sv then .rekeyed
  else if h : i < es.size then
    .yieldVal (match kind with
               | .keys => es[i].1
               | .values => es[i].2
               | .items => .tuple #[es[i].1, es[i].2])
  else .done

/-- §3c-i-a: is this iterable expression a DICT VIEW CALL, and of which kind?

**Fusion is CONTROL: only the call site can tell `list(d.keys())` from
`k = d.keys()`.** A view is a LIVE object (docs/backlog/python-completeness.md
2026-08-23-pycomplete-8/9), so a pure worker that answered a snapshot would be
measurably wrong the moment the view outlived the call — which is why this
recognizer is syntactic, sits at the `for` dispatch, and admits ONLY the
zero-argument call shape. Anything else keeps evaluating normally and refuses
where it always did. -/
def dictViewCall : Expr → Option (Expr × DictViewKind)
  | .call (.attribute d "keys" _) args kw Option.none _ =>
      if args.isEmpty && kw.isEmpty then some (d, .keys) else Option.none
  | .call (.attribute d "values" _) args kw Option.none _ =>
      if args.isEmpty && kw.isEmpty then some (d, .values) else Option.none
  | .call (.attribute d "items" _) args kw Option.none _ =>
      if args.isEmpty && kw.isEmpty then some (d, .items) else Option.none
  | _ => Option.none

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

/-- §del: remove the entry whose key is `keyEq`-equal to `k`, if present.
Answers the remaining entries and whether a key was FOUND — the caller turns
`false` into CPython's `KeyError`.

Deletion does NOT hold the slot: a later reinsertion appends, which is
`dictStore`'s existing behaviour and is what CPython measures
(`d = {1:'a',2:'b',3:'c'}; del d[2]; d[2]='z'` lists `[1, 3, 2]`). So the
entries array stays exactly "the insertion sequence", the invariant every
cursor in this file reads. -/
def dictDelete : List (RVal × RVal) → RVal → List (RVal × RVal) × Bool
  | [], _ => ([], false)
  | (k', v') :: rest, k =>
    if keyEq k' k then (rest, true)
    else
      match dictDelete rest k with
      | (rest', found) => ((k', v') :: rest', found)

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

def dictPairValues (h : Heap) : RVal → Option (List RVal)
  | .tuple xs => some xs.toList
  | .ntuple _ _ xs => some xs.toList
  | .listV xs => some xs.toList
  | .str s => some (strCharVals s)
  | .bytes xs => some (bytesIntVals xs)
  | .ref a =>
      match Heap.get? h a with
      | some (.list xs) => some xs.toList
      | _ => Option.none
  | _ => Option.none

def dictPair (h : Heap) (index : Nat) (v : RVal) : Res (RVal × RVal) :=
  match dictPairValues h v with
  | Option.none => .exn (.typeError
      s!"cannot convert dictionary update sequence element #{index} to a sequence")
  | some xs =>
      match xs with
      | [k, value] => .ok (k, value)
      | _ => .exn (.valueError
          s!"dictionary update sequence element #{index} has length {xs.length}; 2 is required")

def dictPairs (h : Heap) : Nat → List RVal → Res (List (RVal × RVal))
  | _, [] => .ok []
  | index, v :: rest => do
      let pair ← dictPair h index v
      let pairs ← dictPairs h (index + 1) rest
      return pair :: pairs

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
  | some (.dictView ..) =>
    .exn (.typeError s!"'{RVal.typeNameH h (.ref a)}' object is not subscriptable")
  | some (.instance _ _) => .exn (.typeError "'object' object is not subscriptable")
  | some (.generator ..) => .exn (.typeError "'generator' object is not subscriptable")
  | some (.cell _) => .unsupported cellInternal
  | some (.closure ..) => .exn (.typeError "'function' object is not subscriptable")
  | some (.pyset _) => .exn (.typeError "'set' object is not subscriptable")
  | Option.none => .unsupported danglingMsg

/-- `del o[k]` on a heap object — the heap half of the `<dictdel>` rewrite.

**THE `shapeVersion` BUMP IS THE LOAD-BEARING HALF, and it is unconditional
here.** A removal is always a KEY-SET change, and the cursor's SIZE guard
cannot see one on its own: `del d[x]` followed by `d[y] = v` in the same loop
body leaves `es.size` exactly as it was, so size — the only guard that fires
today — stays silent and the churn would be walked as if nothing happened.
`shapeVersion` is what makes that regime detectable, so deletion increments it
even though `heapStore` increments only on GROWTH. The two together are what
`dictStep`'s `rekeyed` arm reads.

A non-dict receiver is the caller's business, not this worker's: it answers
`Option.none` and the arm decides, because the rewrite is SYNTACTIC and admits
`del o[k]` for any `o`. -/
def heapDelete (h : Heap) (a : Addr) (k : RVal) : Option (Res Heap) :=
  match Heap.get? h a with
  | some (.dict es ver) =>
    some (if hashableKey k then
      match dictDelete es.toList k with
      | (_, false) => .exn .keyError
      | (es', true) =>
        match Heap.update h a (.dict es'.toArray (ver + 1)) with
        | some h' => .ok h'
        | Option.none => .unsupported danglingMsg
    else keyRefusal h k)
  | some (.list xs) =>
    some (match asInt k with
      | some i =>
        match normIndex i xs.size with
        | some n =>
          match Heap.update h a (.list ((xs.toList.eraseIdx n).toArray)) with
          | some h' => .ok h'
          | Option.none => .unsupported danglingMsg
        | Option.none => .exn .indexErrorAssign
      | Option.none =>
        .exn (.typeError
          s!"list indices must be integers or slices, not {RVal.typeNameH h k}"))
  | _ => Option.none

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
      | Option.none => .exn .indexErrorAssign
    | Option.none =>
      .exn (.typeError s!"list indices must be integers, not {RVal.typeNameH h k}")
  -- H3: no `__setitem__` can exist (dunder guard) — faithful refusal.
  | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
  | some (.instance _ _) =>
    .exn (.typeError "'object' object does not support item assignment")
  | some (.generator ..) =>
    .exn (.typeError "'generator' object does not support item assignment")
  | some (.cell _) => .unsupported cellInternal
  | some (.closure ..) =>
    .exn (.typeError "'function' object does not support item assignment")
  | some (.pyset _) =>
    .exn (.typeError "'set' object does not support item assignment")
  | Option.none => .unsupported danglingMsg

/-- `len(o)` on a heap object: dict entry count / list length; an
instance has no `__len__` (dunder guard) — the faithful `TypeError`. -/
def heapLen (h : Heap) (a : Addr) : Res RVal :=
  match Heap.get? h a with
  | some (.dict es _) => .ok (.int es.size)
  | some (.list xs) => .ok (.int xs.size)
  | some (.dictView da _) =>
    do let es ← dictViewEntries h da; return .int es.size
  | some (.instance _ _) => .exn (.typeError "object of type 'object' has no len()")
  | some (.generator ..) => .exn (.typeError "object of type 'generator' has no len()")
  | some (.cell _) => .unsupported cellInternal
  | some (.closure ..) => .exn (.typeError "object of type 'function' has no len()")
  | some (.pyset xs) => .ok (.int xs.size)
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
  | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
  | some (.instance _ _) =>
    .unsupported "internal: '.get' dispatch reached an instance receiver (method dispatch owns instances — report this)"
  | some (.generator ..) => .exn .attributeError
  | some (.cell _) => .unsupported cellInternal
  | some (.closure ..) => .exn .attributeError  -- functions have no .get
  | some (.pyset _) => .exn .attributeError     -- sets have no .get
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
  | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
  | some (.instance _ _) =>
    .unsupported "internal: '.append' dispatch reached an instance receiver (method dispatch owns instances — report this)"
  | some (.generator ..) => .exn .attributeError
  | some (.cell _) => .unsupported cellInternal
  | some (.closure ..) => .exn .attributeError
  | some (.pyset _) => .exn .attributeError    -- sets have no .append
  | Option.none => .unsupported danglingMsg

/-- `lst.pop()` / `lst.pop(i)` (H2): remove and return the element at `i`
(default `-1`, the last; negatives from the end); an out-of-range or
empty pop is a faithful `IndexError`. `dict.pop` is a REAL CPython method
(with different semantics) — loud, not an `AttributeError`. -/
def heapPop (h : Heap) (a : Addr) (i : Option Int) : Res (Heap × RVal) :=
  match Heap.get? h a with
  | some (.list xs) =>
    if xs.isEmpty then .exn .indexErrorPopEmpty else
    match normIndex (i.getD (-1)) xs.size with
    | some n =>
      match Heap.update h a (.list ((xs.toList.eraseIdx n).toArray)) with
      | some h' => .ok (h', xs.getD n .none)
      | Option.none => .unsupported danglingMsg
    | Option.none => .exn .indexErrorPop
  | some (.dict _ _) =>
    .unsupported "'.pop' on a dict is outside the tier (dict.pop lands with the dict-method tier)"
  | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
  | some (.instance _ _) =>
    .unsupported "internal: '.pop' dispatch reached an instance receiver (method dispatch owns instances — report this)"
  | some (.generator ..) => .exn .attributeError
  | some (.cell _) => .unsupported cellInternal
  | some (.closure ..) => .exn .attributeError
  | some (.pyset _) =>
      .unsupported "set.pop() is outside the tier (it removes an ARBITRARY element — hash order; docs/memory-model.md)"
  | Option.none => .unsupported danglingMsg

/-- `lst.insert(i, x)` (the §2.5 residue — docs/memory-model.md
§`list.insert`): insert `x` before position `i`, CPython's `ins1`
CLAMPING rule — a negative `i` counts from the end and floors at 0
(`Int.toNat` of a negative), `i` beyond the end appends (`take`/`drop`
saturate at `size`; core `List.insertIdx` is NOT used — it silently
DROPS an out-of-range insert, the opposite of the clamp). Never an
`IndexError`. The call's value is `None`; the mutation is visible
through every alias. Growth is ONE element per fuel-costing call —
append's discipline, no `seqBudget` interaction (the budget guards
single-step materialization). -/
def heapInsert (h : Heap) (a : Addr) (i : Int) (v : RVal) : Res Heap :=
  match Heap.get? h a with
  | some (.list xs) =>
    let n : Nat := (if i < 0 then i + xs.size else i).toNat
    match Heap.update h a (.list ((xs.toList.take n ++ v :: xs.toList.drop n).toArray)) with
    | some h' => .ok h'
    | Option.none => .unsupported danglingMsg
  | some (.dict _ _) => .exn .attributeError  -- 'dict' object has no attribute 'insert'
  | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
  | some (.instance _ _) =>
    .unsupported "internal: '.insert' dispatch reached an instance receiver (method dispatch owns instances — report this)"
  | some (.generator ..) => .exn .attributeError
  | some (.cell _) => .unsupported cellInternal
  | some (.closure ..) => .exn .attributeError
  | some (.pyset _) => .exn .attributeError    -- sets have .add, not .insert
  | Option.none => .unsupported danglingMsg

/-! `list += iterable` keeps the receiver's address and extends it in place.
The augmented-assignment arm uses this worker for heap-backed list
attributes.  The value-side list/tuple/string inventory is deterministic;
stateful heap iterators and hash-order containers stay loud rather than
silently choosing an iteration protocol. -/
def heapListExtendValues (h : Heap) : RVal → Res (List RVal)
  | .listV xs => .ok xs.toList
  | .tuple xs => .ok xs.toList
  | .ntuple _ _ xs => .ok xs.toList
  | .str s => .ok (strCharVals s)
  | .bytes xs => .ok (bytesIntVals xs)
  | .rangeV lo hi step => rangeVals lo.toInt hi.toInt step.toInt
  | .ref b =>
      match Heap.get? h b with
      | some (.list xs) => .ok xs.toList
      | some (.dict ..) =>
          .unsupported "augmented list assignment from a heap dict is outside the tier (dict iteration is live)"
      | some (.dictView ..) =>
          .unsupported "augmented list assignment from a dictionary view is outside the tier"
      | some (.generator ..) =>
          .unsupported "augmented list assignment from a generator is outside the tier (the iterator is stateful)"
      | some (.pyset _) =>
          .unsupported "augmented list assignment from a set is outside the tier (iteration is hash order)"
      | some (.instance ..) =>
          .exn (.typeError "'object' object is not iterable")
      | some (.cell _) => .unsupported cellInternal
      | some (.closure ..) => .exn (.typeError "'function' object is not iterable")
      | none => .unsupported danglingMsg
  | v => .exn (.typeError s!"'{RVal.typeNameH h v}' object is not iterable")

def heapListExtend (h : Heap) (a : Addr) (v : RVal) : Res Heap :=
  match Heap.get? h a with
  | some (.list xs) =>
      match heapListExtendValues h v with
      | .ok ys =>
          match Heap.update h a (.list (xs.toList ++ ys).toArray) with
          | some h' => .ok h'
          | none => .unsupported danglingMsg
      | .exn e => .exn e
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg
  | some _ => .unsupported "augmented repetition receiver is not a list"
  | none => .unsupported danglingMsg

def heapListAugAssign (h : Heap) (a : Addr) (op : BinOp) (v : RVal) : Res Heap :=
  if op == .add then heapListExtend h a v
  else .unsupported "augmented assignment to a heap-valued attribute is outside the tier (docs/memory-model.md §bound() end-to-end)"

/-- `o.attr = v` on a heap object (H3: mutable self — the attribute
store). Instances update their attribute table in place (`Env.set`
semantics: replace-in-place or append — CPython `__dict__` insertion
order); a dict/list has no writable attributes — the faithful
`AttributeError` (no `__slots__`/instance dict on builtins). -/
def heapAttrStore (h : Heap) (a : Addr) (attr : String) (v : RVal) : Res Heap :=
  match Heap.get? h a with
  | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
  | some (.instance ci attrs) =>
    match Heap.update h a (.instance ci (Env.set attrs.toList attr v).toArray) with
    | some h' => .ok h'
    | Option.none => .unsupported danglingMsg
  | some (.dict _ _) => .exn .attributeError
  | some (.list _) => .exn .attributeError
  -- a generator's attributes (`gi_frame`, …) are all read-only
  | some (.generator ..) => .exn .attributeError
  | some (.cell _) => .unsupported cellInternal
  | some (.closure ..) =>
      .unsupported "attribute stores on a function object are outside the tier (CPython allows them; a fake AttributeError would be wrong)"
  | some (.pyset _) => .exn .attributeError  -- sets have no writable attributes
  | Option.none => .unsupported danglingMsg

/-- `del o.attr` on a heap object.  Only ordinary instances carry mutable
attribute dictionaries in the admitted class tier; deleting an absent
attribute is the faithful `AttributeError`, while unsupported receiver
protocols remain loud. -/
def heapAttrDelete (h : Heap) (a : Addr) (attr : String) : Res Heap :=
  match Heap.get? h a with
  | some (.instance ci attrs) =>
    match Env.lookup attrs.toList attr with
    | some _ =>
      match Heap.update h a (.instance ci (Env.remove attrs.toList attr).toArray) with
      | some h' => .ok h'
      | Option.none => .unsupported danglingMsg
    | Option.none => .exn .attributeError
  | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
  | some (.dict _ _) => .exn .attributeError
  | some (.list _) => .exn .attributeError
  | some (.generator ..) => .exn .attributeError
  | some (.cell _) => .unsupported cellInternal
  | some (.closure ..) =>
      .unsupported "attribute deletion on a function object is outside the tier (CPython allows it; a fake AttributeError would be wrong)"
  | some (.pyset _) => .exn .attributeError
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
    | some (.dictView da _) =>
      do let es ← dictViewEntries h da; return es.size != 0
    | some (.instance _ attrs) =>
      match Env.lookup attrs.toList instanceBoolMarker with
      | some (.bool b) => .ok b
      | _ => .ok true
    -- a generator object is always truthy (no `__bool__`/`__len__`)
    | some (.generator ..) => .ok true
    | some (.cell _) => .unsupported cellInternal
    | some (.closure ..) => .ok true
    | some (.pyset xs) => .ok (xs.size != 0)
    | Option.none => .unsupported danglingMsg
  | v => truthy v

/-- A decided pure truthiness lifts to every heap (`truthy`'s only `.ref`
arm is `unsupported`, which never decides). -/
theorem truthyH_of_truthy {h : Heap} {v : RVal} {b : Bool}
    (ht : truthy v = .ok b) : truthyH h v = .ok b := by
  cases v <;> simp_all [truthy, truthyH]

def boolCastArgs (heap : Heap) : List RVal → Res RVal
  | [] => .ok (.bool false)
  | [value] => do
    let result ← truthyH heap value
    return .bool result
  | values => .exn (.typeError s!"bool expected at most 1 argument, got {values.length}")

def divmodArgs : List RVal → Res RVal
  | [numerator, divisor] =>
    match asInt numerator, asInt divisor with
    | some numeratorValue, some divisorValue =>
      if divisorValue = 0 then .exn .zeroDivisionError
      else .ok (.tuple #[.int (Int.fdiv numeratorValue divisorValue),
        .int (Int.fmod numeratorValue divisorValue)])
    | _, _ =>
      match numerator, divisor with
      | .float _, _ | _, .float _ => do
        let (quotient, remainder) ← evalFloatDivmod .floatDivmodZeroDivisionError numerator divisor
        return .tuple #[.float quotient, .float remainder]
      | .ref _, _ | _, .ref _ =>
        .unsupported "divmod() nonnumeric operand protocols remain unmodelled"
      | _, _ =>
        .exn (.typeError s!"unsupported operand type(s) for divmod(): '{numerator.typeName}' and '{divisor.typeName}'")
  | values => .exn (.typeError s!"divmod expected 2 arguments, got {values.length}")

/-- Binary modular exponentiation with a structural fuel bound. The exponent
is halved at each step, so the fixed shift budget bounds work while avoiding
materializing the enormous unmodded power. -/
def powModFuel : Nat → Nat → Int → Int → Int → Int
  | 0, _, _, _, acc => acc
  | fuel + 1, exponent, base, modulus, acc =>
    if exponent = 0 then acc
    else
      let nextAcc := if exponent % 2 = 1 then Int.emod (acc * base) modulus else acc
      powModFuel fuel (exponent / 2) (Int.emod (base * base) modulus) modulus nextAcc

def powMod (base exponent modulus : Int) : Int :=
  powModFuel shiftBudget exponent.toNat (Int.emod base modulus) modulus
    (Int.emod 1 modulus)

/-/ Extended Euclid for modular inverses. The remainder operands stay
nonnegative because the caller normalises the base and requires a positive
modulus; the coefficient may be signed. -/
def modInverseFuel : Nat → Int → Int → Int → Int → Option (Int × Int)
  | 0, _, _, _, _ => Option.none
  | fuel + 1, oldR, r, oldS, s =>
      if r = 0 then
        some (oldR, oldS)
      else
        let q := Int.fdiv oldR r
        modInverseFuel fuel r (Int.emod oldR r) s (oldS - q * s)

def modInverse (base modulus : Int) : Option Int :=
  match modInverseFuel shiftBudget (Int.emod base modulus) modulus 1 0 with
  | some (gcd, coefficient) =>
      if gcd = 1 then some (Int.emod coefficient modulus) else Option.none
  | Option.none => Option.none

/-- The three-argument integer `pow` slice. Positive moduli use Python's
nonnegative remainder; negative exponents use a bounded extended-Euclid
modular inverse, while non-integral protocol cases stay loud. -/
def powModArgs : List RVal → Res RVal
  | [base, exponent, modulus] =>
    match asInt base, asInt exponent, asInt modulus with
    | some x, some y, some m =>
      if m = 0 then
        .exn (.valueError "pow() 3rd argument cannot be 0")
      else if m < 0 then
        .unsupported "pow() with a negative modulus is outside the tier"
      else if y < 0 then
        if y.natAbs > shiftBudget then
          .unsupported "pow() modular exponent beyond shiftBudget is outside the tier"
        else
          match modInverse x m with
          | some inverse => .ok (.int (powMod inverse y.natAbs m))
          | Option.none => .exn (.valueError "base is not invertible for the given modulus")
      else if y.natAbs > shiftBudget then
        .unsupported "pow() modular exponent beyond shiftBudget is outside the tier"
      else
        .ok (.int (powMod x y m))
    | _, _, _ =>
      .exn (.typeError "pow() 3rd argument not allowed unless all arguments are integers")
  | values => .exn (.typeError s!"pow() expected 2 or 3 arguments, got {values.length}")

/-- Read the reserved literal-equality marker from an instance referent.
The marker is internal-only; ordinary instance attributes never use this
unspellable name. -/
def instanceEqMarkerH (h : Heap) : RVal → Option Bool
  | .ref a =>
      match Heap.get? h a with
      | some (.instance _ attrs) =>
          match Env.lookup attrs.toList instanceEqMarker with
          | some (.bool b) => some b
          | _ => none
      | _ => none
  | _ => none

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
        match instanceEqMarkerH h (.ref x), instanceEqMarkerH h (.ref y) with
        | some result, _ => .ok result
        | none, some result => .ok result
        | none, none =>
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
            | some (.dictView da .keys), some (.dictView db .keys) =>
                if da == db then .ok true
                else .unsupported "dictionary view set comparison is outside the tier"
            | some (.dictView _ .values), some (.dictView _ .values) => .ok false
            | some (.dictView ..), some _ | some _, some (.dictView ..) =>
                .unsupported "dictionary view set comparison is outside the tier"
            | some _, some _ => .ok false   -- dict vs list: cross-type `==`
            | _, _ => .unsupported danglingMsg
      | .ref x, _ =>
        match instanceEqMarkerH h (.ref x) with
        | some result => .ok result
        | none => .ok false
      | _, .ref y =>
        match instanceEqMarkerH h (.ref y) with
        | some result => .ok result
        | none => .ok false
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

/-- `dict_items.__contains__` accepts only two-element tuples, hashes the key
before lookup, and compares the stored value. The hash check is observable:
`([unhashable], value) in d.items()` raises before any equality scan. -/
def dictItemContainsList (h : Heap) (fuel : Nat)
    (es : Array (RVal × RVal)) : List RVal → Res Bool
  | [key, value] =>
    if hashableKey key then
      match dictFind es.toList key with
      | some stored => heapEq h fuel [] stored value
      | Option.none => .ok false
    else keyRefusal h key
  | _ => .ok false

def dictItemContains (h : Heap) (fuel : Nat) (es : Array (RVal × RVal))
    (probe : RVal) : Res Bool :=
  match probe with
  | .tuple xs => dictItemContainsList h fuel es xs.toList
  | .ntuple _ _ xs => dictItemContainsList h fuel es xs.toList
  | _ => .ok false

/-- `k in o` on a heap object. Dicts: key membership (unhashable probes
raise, empty dict included — pure `keyEq`, keys are hashable). Lists
(H2): the fueled `==` scan (`heapContainsScan`). -/
def heapContains (h : Heap) (fuel : Nat) (a : Addr) (k : RVal) : Res Bool :=
  match Heap.get? h a with
  | some (.dict es _) =>
    if hashableKey k then .ok (dictFind es.toList k).isSome
    else keyRefusal h k
  | some (.list xs) => heapContainsScan h fuel k xs.toList
  | some (.dictView da kind) =>
    do
      let es ← dictViewEntries h da
      match kind with
      | .keys =>
        if hashableKey k then .ok (dictFind es.toList k).isSome
        else keyRefusal h k
      | .values => heapContainsScan h fuel k (dictViewElems es .values).toList
      | .items => dictItemContains h fuel es k
  -- H3: no `__contains__`/`__iter__`/`__getitem__` (dunder guard) —
  -- the faithful `TypeError`.
  | some (.instance _ _) =>
    .exn (.typeError "argument of type 'object' is not iterable")
  | some (.generator ..) =>
    -- `x in gen` CONSUMES the generator in CPython: a membership test
    -- with a side effect, which this pure helper cannot express — loud,
    -- never a wrong answer (docs/memory-model.md §generator semantics)
    .unsupported "'in' on a generator CONSUMES it (a stateful membership test) — outside the tier"
  | some (.cell _) => .unsupported cellInternal
  | some (.closure ..) =>
    .exn (.typeError "argument of type 'function' is not iterable")
  | some (.pyset xs) =>
    -- H7+ sets: MEMBERSHIP is the admitted surface (order-independent);
    -- the probe rides the KEY doctrine — CPython HASHES it before any
    -- comparison, so an unhashable probe raises, empty set included
    if hashableKey k then heapContainsScan h fuel k xs.toList
    else keyRefusal h k
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
  | .bytes values =>
    match a with
    | .bytes probe => .ok (bytesContains values.toList probe.toList)
    | probe =>
      match asInt probe with
      | some integer =>
        if 0 ≤ integer && integer < 256 then
          .ok (values.contains (UInt8.ofNat integer.toNat))
        else .exn (.valueError "byte must be in range(0, 256)")
      | none => .exn (.typeError s!"a bytes-like object is required, not '{typeNamePrefix (RVal.typeNameH h probe) 100}'")
  | .tuple xs => heapContainsScan h fuel a xs.toList
  | .ntuple _ _ xs => heapContainsScan h fuel a xs.toList
  | .rangeV lo hi step =>
      .ok (rangeContains lo.toInt hi.toInt step.toInt a)
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
    else if a.isEllipsis || b.isEllipsis then .ok (a.isEllipsis && b.isEllipsis)
    else
      match a, b with
      | .ref x, .ref y => .ok (x == y)
      | .ref _, _ => .ok false
      | _, .ref _ => .ok false
      | .bool x, .bool y => .ok (x == y)
      | .int x, .int y =>
          if smallIntIdentity x && smallIntIdentity y then .ok (x == y)
          else .unsupported "'is' between 'int' and 'int' (identity is not value-determined) is outside the tier"
      | .bool _, .int _ | .int _, .bool _ => .ok false
      | a, b => .unsupported s!"'is' between '{a.typeName}' and '{b.typeName}' (identity is not value-determined) is outside the tier"
  | .isNot =>
    if a.isNone || b.isNone then .ok (!(a.isNone && b.isNone))
    else if a.isEllipsis || b.isEllipsis then .ok (!(a.isEllipsis && b.isEllipsis))
    else
      match a, b with
      | .ref x, .ref y => .ok (x != y)
      | .ref _, _ => .ok true
      | _, .ref _ => .ok true
      | .bool x, .bool y => .ok (x != y)
      | .int x, .int y =>
          if smallIntIdentity x && smallIntIdentity y then .ok (x != y)
          else .unsupported "'is not' between 'int' and 'int' (identity is not value-determined) is outside the tier"
      | .bool _, .int _ | .int _, .bool _ => .ok true
      | a, b => .unsupported s!"'is not' between '{a.typeName}' and '{b.typeName}' (identity is not value-determined) is outside the tier"
  | .inOp => valContains h fuel a b
  | .notIn => do let e ← valContains h fuel a b; return !e
  | op => evalCompareOp op a b

/-- Unary operators over the heap: `not d` is dict truthiness; `-`, `+`
and `~` stay pure (a `.ref` operand is refused there). -/
def evalUnaryOpH (h : Heap) (op : UnaryOp) (v : RVal) : Res RVal :=
  match op with
  | .not => do let b ← truthyH h v; return .bool (!b)
  | .usub => evalUnaryOp .usub v
  | .uadd => evalUnaryOp .uadd v
  | .invert => evalUnaryOp .invert v

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
  | .bytes _, .ref address => .exn (.typeError s!"byte indices must be integers or slices, not {typeNamePrefix (RVal.typeNameH h (.ref address)) 200}")
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
    -- §L53 rung 3b: sorted() drains, so no mutation window exists — the
    -- keys in insertion order are all it needs (and the sort makes the
    -- order unobservable anyway)
    | some (.dict es _) =>
      (match (if desc then Option.none else asIntList (dictKeys es).toList) with
       | some ns =>
          .ok (h.push (.list (((sortInts ns).map RVal.int).toArray)), .ref h.size)
       | Option.none => do
          return (h.push (.list (← sortByLt desc (dictKeys es).toList).toArray), .ref h.size))
    | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
    | some (.instance _ _) =>
        .exn (.typeError "'object' object is not iterable")
    | some (.generator ..) =>
        .unsupported "sorted() over a generator DRAINS it (a stateful read) — outside the tier (docs/memory-model.md §generator semantics)"
    | some (.cell _) => .unsupported cellInternal
    | some (.closure ..) => .exn (.typeError "'function' object is not iterable")
    | some (.pyset xs) =>
      (match (if desc then Option.none else asIntList xs.toList) with
       | some ns =>
          .ok (h.push (.list (((sortInts ns).map RVal.int).toArray)), .ref h.size)
       | Option.none => do
          return (h.push (.list (← sortByLt desc xs.toList).toArray), .ref h.size))
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
        -- §L53 rung 3b: ranges over the KEYS, order-independent
        | some (.dict es _) =>
          (match asIntList (dictKeys es).toList with
           | some (n :: rest) => .ok (.int (foldExtremum isMax n rest))
           | some [] =>
               .exn (.valueError s!"{if isMax then "max" else "min"}() arg is an empty sequence")
           | Option.none =>
               extremumOf isMax (if isMax then "max" else "min") (dictKeys es).toList)
        | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
        | some (.instance _ _) =>
            .exn (.typeError "'object' object is not iterable")
        | some (.generator ..) =>
            .unsupported s!"{if isMax then "max" else "min"}() over a generator DRAINS it (a stateful read) — outside the tier"
        | some (.cell _) => .unsupported cellInternal
        | some (.closure ..) =>
            .exn (.typeError "'function' object is not iterable")
        | some (.pyset _) =>
            .unsupported s!"{if isMax then "max" else "min"}() over a set is outside the tier (hash-order drain; docs/memory-model.md)"
        | Option.none => .unsupported danglingMsg)
     | v => extremumVal isMax [v])
  | vs => extremumVal isMax vs

/-! ### Closure CELLS (H7 cells, docs/memory-model.md §nested defs and
closures)

CPython closes over VARIABLES, not values: a local the enclosing frame
REBINDS after the `def` lives in a CELL, and the nested body reads that
cell when it RUNS. The tier models a cell as what it is — a heap slot —
and addresses it from the frame's env under a key no Python identifier
can spell:

* the enclosing frame keeps its ordinary plain binding of `x` (so every
  existing read, write and lemma about frames is untouched) AND a
  DIRECTORY entry `"<cell>x" ↦ .ref a`, created by the `def`;
* the closure's captured env carries both the ordinary binding and the
  DIRECTORY entry, so the `def` stores a location alongside its current
  value;
* `cellsFor` resolves those entries at the CALL, from the live locals of
  the frame that is calling — which the tier admits only when that IS
  the defining frame — and hands the body the ordinary binding plus the
  live cell directory. `envGet` follows the directory for reads and
  assignments update the slot, which is the late binding and the whole
  difference from snapshot-at-def.

The extractor decides which captures are cells and admits only the
fragment these three rules model exactly — a closure whose name never
escapes the defining frame, and, for a GENERATOR, whose celled names are
all written before the first call (a resume reads the cell, and the tier
refreshes at the call). Everything else keeps the loud refusal. -/

/-- The env key a CELL for `x` is filed under. `<` and `>` cannot occur
in a Python identifier, so the directory can never collide with a name
the extractor emits. -/
def cellKey (x : String) : String := "<cell>" ++ x

/-- Is this env key a cell DIRECTORY entry? -/
def isCellKey (k : String) : Bool := "<cell>".isPrefixOf k

/-- The Python name a cell key names (identity on non-cell keys). -/
def cellName (k : String) : String := (k.toList.drop 6).asString

def cellStore (h : Heap) (a : Addr) (v : RVal) : Res Heap :=
  match Heap.get? h a with
  | some (.cell _) =>
      match Heap.update h a (.cell (some v)) with
      | some h' => .ok h'
      | none => .unsupported danglingMsg
  | _ => .unsupported cellInternal

/-- Allocate (or REUSE) this frame's cells for a `def`'s late-bound
captures. Reuse is what makes a `def` in a LOOP correct: one frame, one
cell, every closure it creates sharing it — exactly CPython. A cell
starts holding the name's CURRENT binding when it has one (a capture
written before the def) and EMPTY when it does not (`guard` in the
shipped `bound()`, assigned below its own `def`). -/
def allocCells (st : FrameState) : List String → FrameState
  | [] => st
  | c :: cs =>
    if isCellKey c then
      match Env.lookup st.locals c with
      | some _ => allocCells st cs
      | Option.none =>
        let a := st.world.heap.size
        let init : Obj := .cell (Env.lookup st.locals (cellName c))
        allocCells
          { st with
            world := { st.world with heap := st.world.heap.push init },
            locals := Env.set st.locals c (.ref a) } cs
    else allocCells st cs

/-- Read a closure's CELLS at the CALL — the late binding, and the whole
difference from snapshot-at-def.

The tier admits a late-bound capture only for a closure whose name never
ESCAPES the frame that defined it, so the calling frame IS that frame and
its live locals are the cell's content. The slot is consulted to confirm
the directory is live (a broken one refuses loudly, never resolves), and
a name the frame does not bind — never assigned, or `del`eted — is left
OUT of the callee env, so the body's read is CPython's free-variable
`NameError` through the existing arm.

The slot's stored CONTENT is the shared value for direct scalar
`nonlocal` reads and writes. Under the escape admission the defining
frame remains the authority for resolving the directory, so escaped
closures still refuse. Relaxing that admission is where a separate
refresh proof at escaped-call sites would be needed. -/
def cellsFor (h : Heap) (env : Env) : REnv → Res REnv
  | [] => .ok []
  | (k, v) :: rest =>
    if isCellKey k then
      match v with
      | .ref a =>
        match Heap.get? h a with
        | some (.cell _) =>
          match Env.lookup env (cellName k) with
          | some x =>
              (cellsFor h env rest) >>= fun cs =>
                .ok ((cellName k, x) :: (k, v) :: cs)
          | Option.none =>
            if (Env.lookup env k).isSome then cellsFor h env rest
            else .unsupported s!"closure cell '{cellName k}' is not visible from the calling frame — a closure with a LATE-BOUND capture called outside the frame that defined it is outside the tier (docs/memory-model.md §nested defs and closures)"
        | _ => .unsupported cellInternal
      | _ => .unsupported cellInternal
    else (cellsFor h env rest) >>= fun cs => .ok ((k, v) :: cs)

/-- A capture list with NO cell keys allocates nothing — the snapshot
tier's frame, unchanged. The decidable side condition is what keeps every
pre-cells consumer a one-liner. -/
theorem allocCells_cellFree : ∀ (st : FrameState) (caps : List String),
    caps.all (fun c => !isCellKey c) = true → allocCells st caps = st := by
  intro st caps
  induction caps generalizing st with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro hall
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hall
    rw [allocCells]
    simp only [hall.1, Bool.false_eq_true, if_false]
    exact ih st (by simpa using hall.2)

/-- …and it resolves to itself. -/
theorem cellsFor_cellFree : ∀ (h : Heap) (env : Env) (cap : REnv),
    cap.all (fun p => !isCellKey p.1) = true → cellsFor h env cap = .ok cap := by
  intro h env cap
  induction cap with
  | nil => intro _; rfl
  | cons kv rest ih =>
    intro hall
    obtain ⟨k, v⟩ := kv
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hall
    simp only [cellsFor, hall.1, Bool.false_eq_true, if_false,
      ih (by simpa using hall.2)]
    rfl

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

/-- Deduplicate by VALUE equality, first occurrence kept (H7+ set
construction, docs/memory-model.md): membership and `len` are
order-blind, so the retained order is unobservable through the admitted
surface. Elements ride the dict-KEY doctrine — `hashableKey` gates, an
unhashable element is `keyRefusal`'s answer (faithful `TypeError` for
lists/dicts/sets, loud for identity-hashed instances); equality is the
fueled heap scan. -/
def setDedup (h : Heap) (fuel : Nat) (acc : List RVal) :
    List RVal → Res (List RVal)
  | [] => .ok acc
  | v :: vs => do
    if hashableKey v then
      let dup ← heapContainsScan h fuel v acc
      if dup then setDedup h fuel acc vs
      else setDedup h fuel (acc ++ [v]) vs
    else keyRefusal h v

/-! ### Set-like dictionary-key algebra

Dictionary key views and sets share Python's set algebra.  The first admitted
operation is `&`: both operands are already hashable collections, so their
membership relation is the pure `keyEq` relation used by dictionary keys and
set construction.  The result is a fresh set object; its retained order is
not observable by the admitted set surface, and consumers such as `sorted`
immediately impose their own order. -/

def setLikeRefH (h : Heap) : RVal → Bool
  | .ref a =>
    match Heap.get? h a with
    | some (.pyset _) => true
    | some (.dictView _ .keys) => true
    | _ => false
  | _ => false

def setLikeElemsH (h : Heap) : RVal → Res (List RVal)
  | .ref a =>
    match Heap.get? h a with
    | some (.pyset xs) => .ok xs.toList
    | some (.dictView da .keys) => do
        let es ← dictViewEntries h da
        return (dictKeys es).toList
    | _ => .unsupported "set algebra requires a set or dictionary key view"
  | _ => .unsupported "set algebra requires a set or dictionary key view"

def setKeyMember (needle : RVal) : List RVal → Bool
  | [] => false
  | value :: rest => if keyEq value needle then true else setKeyMember needle rest

def setIntersectionKeys (left right : List RVal) : List RVal :=
  left.foldr (init := []) fun value acc =>
    if setKeyMember value right then value :: acc else acc

def evalBinOpH (h : Heap) (op : BinOp) (a b : RVal) : Res (Heap × RVal) :=
  if op == .bitAnd && setLikeRefH h a && setLikeRefH h b then
    let left := setLikeElemsH h a
    let right := setLikeElemsH h b
    match left, right with
    | .ok xs, .ok ys =>
      let h' := h.push (.pyset (setIntersectionKeys xs ys).toArray)
      .ok (h', .ref h.size)
    | .unsupported msg, _ | _, .unsupported msg => .unsupported msg
    | .timeout, _ | _, .timeout => .timeout
    | .exn e, _ | _, .exn e => .exn e
  else
    match evalBinOp op a b with
    | .ok value => .ok (h, value)
    | .exn e => .exn e
    | .timeout => .timeout
    | .unsupported msg => .unsupported msg

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
      | .bytes xs =>
        let values := bytesIntVals xs
        if values.length = names.length then .ok (bindAll env names values)
        else if names.length < values.length then
          .exn (.valueError s!"too many values to unpack (expected {names.length})")
        else
          .exn (.valueError
            s!"not enough values to unpack (expected {names.length}, got {values.length})")
      | .rangeV lo hi step =>
          rangeVals lo.toInt hi.toInt step.toInt >>= fun values =>
          let xs := values.toArray
          if xs.size = names.length then .ok (bindAll env names xs.toList)
          else if names.length < xs.size then
            .exn (.valueError s!"too many values to unpack (expected {names.length})")
          else
            .exn (.valueError
              s!"not enough values to unpack (expected {names.length}, got {xs.size})")
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
       | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
       | some (.instance _ _) =>
         -- no `__iter__` can exist (dunder guard) — faithful
         .exn (.typeError "cannot unpack non-iterable object object")
       | some (.generator ..) =>
         .unsupported "unpacking a generator DRAINS it (a stateful read) — outside the tier (docs/memory-model.md §generator semantics)"
       | some (.cell _) => .unsupported cellInternal
       | some (.closure ..) =>
         .exn (.typeError "cannot unpack non-iterable function object")
       | some (.pyset _) =>
         .unsupported "unpacking a set is outside the tier (hash order; docs/memory-model.md)"
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

/-- Unpack an already-evaluated RHS into exactly `n` element values —
`assignTo`'s tuple-target arity/type discipline factored out so the
HEAP-THREADING store path (pass 4: tuple targets with attribute
elements) shares one set of faithful errors. A heap LIST unpacks as an
eager snapshot (CPython), everything else exactly as `assignToH`. -/
def unpackSeq (h : Heap) (n : Nat) : RVal → Res (List RVal)
  | .bytes values =>
    if values.size = n then .ok (bytesIntVals values)
    else if n < values.size then
      .exn (.valueError s!"too many values to unpack (expected {n})")
    else
      .exn (.valueError s!"not enough values to unpack (expected {n}, got {values.size})")
  | .listV xs | .tuple xs | .ntuple _ _ xs =>
    if xs.size = n then .ok xs.toList
    else if n < xs.size then
      .exn (.valueError s!"too many values to unpack (expected {n})")
    else
      .exn (.valueError
        s!"not enough values to unpack (expected {n}, got {xs.size})")
  | .ref a =>
    (match Heap.get? h a with
     | some (.list xs) =>
       if xs.size = n then .ok xs.toList
       else if n < xs.size then
         .exn (.valueError s!"too many values to unpack (expected {n})")
       else
         .exn (.valueError
           s!"not enough values to unpack (expected {n}, got {xs.size})")
     | some (.dict _ _) =>
       .unsupported "unpacking a dict iterates its keys — outside the tier (live dict iteration; docs/memory-model.md)"
     | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
     | some (.instance _ _) => .exn (.typeError "cannot unpack non-iterable object object")
     | some (.generator ..) =>
       .unsupported "unpacking a generator DRAINS it (a stateful read) — outside the tier (docs/memory-model.md §generator semantics)"
     | some (.cell _) => .unsupported cellInternal
     | some (.closure ..) => .exn (.typeError "cannot unpack non-iterable function object")
     | some (.pyset _) =>
       .unsupported "unpacking a set is outside the tier (hash order; docs/memory-model.md)"
     | Option.none => .unsupported danglingMsg)
  | .str _ => .unsupported "unpacking a str is outside the v0 tier"
  | .rangeV lo hi step =>
    rangeVals lo.toInt hi.toInt step.toInt >>= fun values =>
    let xs := values.toArray
    if xs.size = n then .ok xs.toList
    else if n < xs.size then
      .exn (.valueError s!"too many values to unpack (expected {n})")
    else
      .exn (.valueError s!"not enough values to unpack (expected {n}, got {xs.size})")
  | v => .exn (.typeError s!"cannot unpack non-iterable {v.typeName} object")

/-! Starred unpacking consumes the supported eager iterables, then splits the
prefix and suffix around a fresh list-valued middle. -/
def unpackAllStar (h : Heap) : RVal → Res (List RVal)
  | .bytes values => .ok (bytesIntVals values)
  | .listV xs | .tuple xs | .ntuple _ _ xs => .ok xs.toList
  | .str s => .ok (strCharVals s)
  | .rangeV lo hi step =>
      rangeVals lo.toInt hi.toInt step.toInt
  | .ref a =>
      match Heap.get? h a with
      | some (.list xs) => .ok xs.toList
      | some (.dict _ _) => .unsupported "unpacking a dict iterates its keys — outside the tier (live dict iteration; docs/memory-model.md)"
      | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
      | some (.instance _ _) => .exn (.typeError "cannot unpack non-iterable object object")
      | some (.generator ..) => .unsupported "unpacking a generator DRAINS it (a stateful read) — outside the tier (docs/memory-model.md §generator semantics)"
      | some (.cell _) => .unsupported cellInternal
      | some (.closure ..) => .exn (.typeError "cannot unpack non-iterable function object")
      | some (.pyset _) => .unsupported "unpacking a set is outside the tier (hash order; docs/memory-model.md)"
      | Option.none => .unsupported danglingMsg
  | v => .exn (.typeError s!"cannot unpack non-iterable {v.typeName} object")

def unpackSeqStar (h : Heap) (before after : Nat) (v : RVal) :
    Res (List RVal × List RVal × List RVal) :=
  unpackAllStar h v >>= fun xs =>
    let need := before + after
    if xs.length < need then
      .exn (.valueError s!"not enough values to unpack (expected at least {need}, got {xs.length})")
    else
      let tailCount := xs.length - before
      let middleCount := tailCount - after
      .ok (xs.take before, (xs.drop before).take middleCount,
        (xs.drop before).drop middleCount)

/-- Store unpacked values into tuple-target ELEMENTS left to right,
threading the HEAP (pass 4, docs/memory-model.md §bound() end-to-end:
`self.tp_score, self.tp_move, self.history = …`). Element tier: plain
names bind; an attribute element stores through a LOCAL-name receiver
holding a `.ref` (sunfish's `self.x`); anything else refuses loudly
(a general receiver would need expression evaluation mid-store). -/
def unpackStoreH (h : Heap) (env : Env) :
    List Expr → List RVal → Res (Heap × Env)
  | [], [] => .ok (h, env)
  | .name id _ :: es, v :: vs => unpackStoreH h (Env.set env id v) es vs
  | .attribute (.name rid _) attr _ :: es, v :: vs =>
    (match Env.lookup env rid with
     | some (.ref a) =>
       (heapAttrStore h a attr v) >>= fun h' => unpackStoreH h' env es vs
     | some _ => .exn .attributeError
     | Option.none =>
       .unsupported s!"tuple-target attribute store through non-local receiver '{rid}' is outside the tier")
  | e :: _, _ :: _ =>
    .unsupported s!"tuple-unpack target element '{e.kindName}' (beyond plain names and local-receiver attributes) is outside the tier"
  | _, _ => .unsupported "internal: unpack arity mismatch after unpackSeq (report this)"

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

/-- Resolve a method through the narrow single-base inheritance chain.  The
chain is bounded by the class-table size so malformed hand-built modules
cannot loop; ingested modules additionally reject unresolved/forward bases. -/
def classMethodQnameFuel (m : Module) : Nat → ClassId → String → Option String
  | 0, _, _ => Option.none
  | fuel + 1, ci, attr =>
    match getClass? m ci with
    | Option.none => Option.none
    | some c =>
      if c.methods.toList.contains attr then
        some (c.name ++ "." ++ attr)
      else
        match c.base with
        | Option.none => Option.none
        | some b =>
          match findClass m b with
          | some (bi, _) => classMethodQnameFuel m fuel bi attr
          | Option.none => Option.none

def classMethodQname (m : Module) (ci : ClassId) (attr : String) : Option String :=
  classMethodQnameFuel m m.classes.size ci attr

def reprArgsH (m : Module) (h : Heap) (vs : List RVal) : Res RVal :=
  match vs with
  | [.ref a] =>
      match Heap.get? h a with
      | some (.instance ci _) =>
          match classMethodQname m ci "__repr__" with
          | some qname =>
              match findFunction m qname with
              | some f =>
                  match FunctionDefn.reprLiteral f with
                  | some s => .ok (.str s)
                  | none => reprArgs h vs
              | none => reprArgs h vs
          | none => reprArgs h vs
      | _ => reprArgs h vs
  | _ => reprArgs h vs


/-- Whether an instance attribute store is permitted by the class's
`__slots__` declaration.  A class without a recognized declaration keeps
the ordinary instance dictionary.  `__dict__` explicitly restores that
dictionary alongside any named slots; inheritance and weak-reference
descriptors remain outside this narrow class-storage slice. -/
def classSlotAllowsAttr (m : Module) (ci : ClassId) (attr : String) : Bool :=
  match getClass? m ci with
  | some c =>
    match c.slots with
    | Option.none => true
    | some names => names.contains "__dict__" || names.contains attr
  | Option.none => false

/-- Module-aware instance attribute store.  The older `heapAttrStore` keeps
its module-free contract for proof walkers and hand-built heap lemmas; the
interpreter calls this wrapper so a recognized `__slots__` class cannot gain
an implicit instance dictionary. -/
def heapAttrStoreClass (m : Module) (h : Heap) (a : Addr) (attr : String)
    (v : RVal) : Res Heap :=
  match Heap.get? h a with
  | some (.instance ci _) =>
    if classSlotAllowsAttr m ci attr then
      heapAttrStore h a attr v
    else
      .exn .attributeError
  | _ => heapAttrStore h a attr v

/-- Module-aware instance attribute deletion.  A recognized `__slots__`
declaration permits deletion only for declared slots (or `__dict__`). -/
def heapAttrDeleteClass (m : Module) (h : Heap) (a : Addr) (attr : String) : Res Heap :=
  match Heap.get? h a with
  | some (.instance ci _) =>
    if classSlotAllowsAttr m ci attr then
      heapAttrDelete h a attr
    else
      .exn .attributeError
  | _ => heapAttrDelete h a attr

/-- Tuple-target attribute stores with the class-storage check threaded
through the same left-to-right heap path as `unpackStoreH`.  The original
module-free helper remains available to the payload-blind proof layer. -/
def unpackStoreHM (m : Module) (h : Heap) (env : Env) :
    List Expr → List RVal → Res (Heap × Env)
  | [], [] => .ok (h, env)
  | .name id _ :: es, v :: vs => unpackStoreHM m h (Env.set env id v) es vs
  | .attribute (.name rid _) attr _ :: es, v :: vs =>
    match Env.lookup env rid with
    | some (.ref a) =>
      (heapAttrStoreClass m h a attr v) >>= fun h' =>
        unpackStoreHM m h' env es vs
    | some _ => .exn .attributeError
    | Option.none =>
      .unsupported s!"tuple-target attribute store through non-local receiver '{rid}' is outside the tier"
  | .subscript (.name rid _) (.constant c _) _ :: es, v :: vs =>
    match Env.lookup env rid with
    | some (.ref a) =>
      (heapStore h a (Const.toRVal c) v) >>= fun h' =>
        unpackStoreHM m h' env es vs
    | some (.listV _) =>
      .unsupported "tuple-target subscript store to a boundary list is outside the tier"
    | some _ => .exn (.typeError "tuple-target subscript store requires a heap object")
    | Option.none =>
      .unsupported s!"tuple-target subscript store through non-local receiver '{rid}' is outside the tier"
  | .subscript (.name rid _) _ _ :: _, _ :: _ =>
    .unsupported s!"tuple-target subscript key through '{rid}' is outside the tier"
  | e :: _, _ :: _ =>
    .unsupported s!"tuple-unpack target element '{e.kindName}' (beyond plain names and local-receiver attributes) is outside the tier"
  | _, _ => .unsupported "internal: unpack arity mismatch after unpackSeq (report this)"

/-- CPython obtains the iterator before rejecting a string or bytes start,
without requesting an element. In-tier instances have no iteration protocol. -/
def sumRejectedStart (program : Module) (heap : Heap) (iterable : RVal)
    (message : String) : Res RVal :=
  let rejected := Res.exn (.typeError message)
  match iterable with
  | .str _ | .bytes _ | .tuple _ | .ntuple .. | .listV _ | .rangeV .. => rejected
  | .ref address =>
    match Heap.get? heap address with
    | some (.list _) | some (.dict ..) | some (.pyset _) | some (.generator ..) => rejected
    | some (.closure ..) => .exn (.typeError "'function' object is not iterable")
    | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
    | some (.instance classId _) =>
      match getClass? program classId with
      | some classDef =>
        .exn (.typeError s!"'{typeNamePrefix classDef.name 200}' object is not iterable")
      | none => .unsupported "sum() iterable has an unknown instance class id"
    | some (.cell _) => .unsupported cellInternal
    | none => .unsupported danglingMsg
  | value => .exn (.typeError s!"'{value.typeName}' object is not iterable")

def bytesOperandCheck (program : Module) (heap : Heap) (operand : RVal)
    (formatName : String → String) : Res Unit :=
  match operand with
  | .ref address =>
    match Heap.get? heap address with
    | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
    | some (.instance classId _) =>
      match getClass? program classId with
      | some classDef => .exn (.typeError (formatName classDef.name))
      | none => .unsupported "bytes operand has an unknown instance class id"
    | some (.cell _) => .unsupported cellInternal
    | none => .unsupported danglingMsg
    | _ => .ok ()
  | _ => .ok ()

def checkBytesIndex (program : Module) (heap : Heap) (container index : RVal) : Res Unit :=
  match container with
  | .bytes _ => bytesOperandCheck program heap index fun name =>
      s!"byte indices must be integers or slices, not {typeNamePrefix name 200}"
  | _ => .ok ()

def checkBytesCompare (program : Module) (heap : Heap) (op : CmpOp)
    (probe container : RVal) : Res Unit :=
  match op, container with
  | .inOp, .bytes _ | .notIn, .bytes _ =>
    bytesOperandCheck program heap probe fun name =>
      s!"a bytes-like object is required, not '{typeNamePrefix name 100}'"
  | _, _ => .ok ()

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

/- The one rendering protocol admitted by the tier is a literal-returning
`__repr__`; every other dunder remains outside the default-protocol slice. -/
def hasUnsupportedDunder (m : Module) (c : ClassDefn) : Bool :=
  c.methods.toList.any fun n =>
    dunderShaped n && n != "__init__" &&
      match n with
      | "__repr__" =>
          match findFunction m (c.name ++ ".__repr__") with
          | some f => f.reprLiteral.isNone
          | none => true
      | "__bool__" =>
          match findFunction m (c.name ++ ".__bool__") with
          | some f => f.boolLiteral.isNone
          | none => true
      | "__eq__" =>
          match findFunction m (c.name ++ ".__eq__") with
          | some f => f.eqLiteral.isNone
          | none => true
      | _ => true

def instanceAttrs (m : Module) (ci : ClassId) : Array (String × RVal) :=
  let boolAttrs :=
    match classMethodQname m ci "__bool__" with
    | some qname =>
        match findFunction m qname with
        | some f =>
            match f.boolLiteral with
            | some b => #[(instanceBoolMarker, .bool b)]
            | none => #[]
        | none => #[]
    | none => #[]
  let eqAttrs :=
    match classMethodQname m ci "__eq__" with
    | some qname =>
        match findFunction m qname with
        | some f =>
            match f.eqLiteral with
            | some b => #[(instanceEqMarker, .bool b)]
            | none => #[]
        | none => #[]
    | none => #[]
  boolAttrs ++ eqAttrs

/-- The default-protocol guard includes inherited dunders.  A subclass of a
class defining `__eq__`, for example, is not an identity-only instance even
when the subclass body has no dunder of its own. -/
def classHasExtraDunderFuel (m : Module) : Nat → ClassId → Bool
  | 0, _ => true
  | fuel + 1, ci =>
    match getClass? m ci with
    | Option.none => true
    | some c =>
      if hasUnsupportedDunder m c then true
      else match c.base with
        | Option.none => false
        | some b =>
          match findClass m b with
          | some (bi, _) => classHasExtraDunderFuel m fuel bi
          | Option.none => true

def classHasExtraDunder (m : Module) (ci : ClassId) : Bool :=
  classHasExtraDunderFuel m m.classes.size ci

/- Namedtuple subclasses are represented as immediate tuple values, so their
custom protocol methods cannot be carried by an instance heap marker. Keep
all such dunders loud at that boundary. -/
def hasNtupleExtraDunder (c : ClassDefn) : Bool :=
  c.methods.toList.any fun n => dunderShaped n && n != "__init__"

def hasContextProtocol (c : ClassDefn) : Bool :=
  c.methods.toList.contains "__enter__"
    && c.methods.toList.contains "__exit__"

def hasContextExtraDunder (c : ClassDefn) : Bool :=
  c.methods.toList.any fun n =>
    dunderShaped n && n != "__init__" && n != "__enter__" && n != "__exit__"

/-- `__repr__` is harmless for a context manager whose instance never enters
the rendering surface: instance representation still refuses loudly. Other
extra dunders can change operations decided by the default-protocol tier. -/
def hasContextUnsupportedDunder (c : ClassDefn) : Bool :=
  c.methods.toList.any fun n =>
    dunderShaped n && n != "__init__" && n != "__enter__" && n != "__exit__" && n != "__repr__"

def findContextClass (m : Module) (name : String) : Option (Nat × ClassDefn) :=
  match findClass m name with
  | some (ci, c) =>
      if c.ok && !c.isExc && c.ntBase.isNone && hasContextProtocol c
          && !hasContextUnsupportedDunder c then
        some (ci, c)
      else Option.none
  | Option.none => Option.none

def withExitArgs (exceptionType : Bool) (a : Addr) : Array RVal :=
  if exceptionType then
    #[.ref a, .str "exception", .none, .none]
  else
    #[.ref a, .none, .none, .none]

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
  | some (.dictView ..) => .refuse "dictionary view operation is outside the tier"
  | some (.instance ci attrs) =>
    (match Env.lookup attrs.toList attr with
     | some v => .value v
     | Option.none =>
       match getClass? m ci with
       | Option.none => .dangling
       | some _ =>
         if (classMethodQname m ci attr).isSome then .boundMethod else .missing)
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
  | dictGet | dictView (kind : DictViewKind) | listAppend | listPop
  -- the §2.5 residue (docs/memory-model.md §`list.insert`): the
  -- clamping-index list MUTATOR
  | listInsert
  -- pass 5 (docs/memory-model.md §search()'s first blockers): the dict
  -- MUTATOR `.clear()` — entries emptied, shape version bumped
  | dictClear
  | refuse (msg : String)
  | dangling
deriving Repr, Inhabited, BEq

/-- Resolve `x.attr(…)` against the heap: instances dispatch through
their CLASS (any attr — user methods; instance data attributes in call
position are loud; missing is the faithful pre-args `AttributeError`);
dicts admit `.get`/`.clear`, lists `.append`/`.pop`/`.insert` (the
builtin method tier). -/
def attrCallPlan (m : Module) (h : Heap) (a : Addr) (attr : String) :
    AttrPlan :=
  match Heap.get? h a with
  | some (.dictView ..) => .refuse "dictionary view operation is outside the tier"
  | some (.instance ci attrs) =>
    (match Env.lookup attrs.toList attr with
     | some _ => .instAttrValue
     | Option.none =>
       match getClass? m ci with
       | Option.none => .dangling
       | some _ =>
         match classMethodQname m ci attr with
         | some qname => .instMethod qname
         | Option.none => .attrMissing)
  | some (.dict _ _) =>
    if attr == "get" then .dictGet
    else if attr == "clear" then .dictClear
    else if attr == "keys" then .dictView .keys
    else if attr == "values" then .dictView .values
    else if attr == "items" then .dictView .items
    else .refuse s!"method call '.{attr}' on a dict is outside the tier (dict '.get'/'.clear' only; docs/memory-model.md)"
  | some (.list _) =>
    if attr == "append" then .listAppend
    else if attr == "pop" then .listPop
    else if attr == "insert" then .listInsert
    else .refuse s!"method call '.{attr}' on a list is outside the tier (list '.append'/'.pop'/'.insert' only; docs/memory-model.md)"
  | some (.generator ..) =>
    -- `send`/`throw`/`close` are REAL generator methods with
    -- resumption/finalization semantics the tier does not model, and
    -- guessing which other names exist would be silently wrong: loud,
    -- never a fake `AttributeError`
    .refuse s!"method call '.{attr}' on a generator is outside the tier (send/throw/close and finalization are deliberately out; docs/memory-model.md §generator semantics)"
  | some (.cell _) => .refuse cellInternal
  | some (.closure ..) =>
    .refuse s!"method call '.{attr}' on a function object is outside the tier (docs/memory-model.md §nested defs and closures)"
  | some (.pyset _) =>
    .refuse s!"method call '.{attr}' on a set is outside the tier (add/remove/pop/… mutate or drain in hash order; docs/memory-model.md)"
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
    | .formattedValue expression reprConversion _ => do
        let (heapAfter, value) ← evalGlobalExpr h gs fuel expression
        let result ← formatValueH heapAfter value reprConversion
        return (heapAfter, result)
    | .formattedValueAscii expression _ => do
        let (heapAfter, value) ← evalGlobalExpr h gs fuel expression
        let result ← asciiValH heapAfter value
        return (heapAfter, result)
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

def withItemBindsG : WithItem → Option (List String)
  | { target := none, .. } => some []
  | { target := some target, .. } => targetBindsG target

def withItemsBindsG : List WithItem → Option (List String)
  | [] => some []
  | item :: rest =>
    match withItemBindsG item, withItemsBindsG rest with
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
    | .unpackAssign .. => []
    | .augAssign t _ _ _ => t.g1TargetStores
    | .whileLoop _ b o _ | .ifStmt _ b o _ =>
      Stmt.g1StoresList b.toList ++ Stmt.g1StoresList o.toList
    | .forStmt t _ b o _ =>
      t.g1TargetStores ++ Stmt.g1StoresList b.toList ++ Stmt.g1StoresList o.toList
    -- exceptions tier: body AND handler can both store (the handler runs
    -- from the body's retained state)
    | .tryStmt b _ hnd _ _ =>
      Stmt.g1StoresList b.toList ++ Stmt.g1StoresList hnd.toList
    | .withStmt items body _ _ =>
      (items.toList.map fun item =>
        (item.target.map Expr.g1TargetStores).getD []).flatten
        ++ Stmt.g1StoresList body.toList
    -- Pass 0 (§import forms): an import stores through no target
    | .importFrom .. => []
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
    | .unpackAssign before star after _ _ => some (before.toList ++ [star] ++ after.toList)
    | .augAssign t _ _ _ => targetBindsG t
    -- H7: a nested def binds its NAME (its body is its own scope)
    | .defStmt name _ _ _ _ _ _ _ _ => some [name]
    -- Class definitions are represented in the ordered top-level stream by
    -- a marker so script mode can execute creation at the right source
    -- position; the marker still binds its class name for static poisoning
    -- and clock/module-init analyses.
    | .unsupported "ClassDef" name _ => some [name]
    | .forStmt t _ b o _ =>
      match targetBindsG t, Stmt.g1BindsList b.toList, Stmt.g1BindsList o.toList with
      | some a, some c, some d => some (a ++ c ++ d)
      | _, _, _ => Option.none
    | .whileLoop _ b o _ | .ifStmt _ b o _ =>
      match Stmt.g1BindsList b.toList, Stmt.g1BindsList o.toList with
      | some c, some d => some (c ++ d)
      | _, _ => Option.none
    -- pass 5: an un-lowered `yield from` binds nothing (the genexp's
    -- target is its own scope; the lowered form is an ordinary `for`)
    | .ret .. | .exprStmt .. | .yieldStmt .. | .yieldFromStmt .. => some []
    | .pass _ | .brk _ | .cont _ => some []
    -- exceptions tier: `raise` binds nothing; a try binds what its body
    -- and handler can bind (an over-approximation, the poisoning
    -- direction — either may have run partially)
    | .raiseStmt .. => some []
    -- the tail batch: `assert` binds nothing (it tests and may raise)
    | .assertStmt .. => some []
    -- the tail batch, MEASURED (docs/backlog.md §del RECONCILED): `del`
    -- CHANGES its targets, and this census feeds `globalsDirty`'s poison
    -- set — with `[]` the rollback after the init-exec refusal (empty
    -- init locals, so the arm always misses there) would resurface the
    -- deleted name's STALE static binding. The recorded "`[]`" note is
    -- superseded by this measurement.
    | .delStmt ns _ => some ns.toList
    | .withStmt items body _ _ =>
      match withItemsBindsG items.toList, Stmt.g1BindsList body.toList with
      | some a, some b => some (a ++ b)
      | _, _ => Option.none
    | .tryStmt b _ hnd _ _ =>
      match Stmt.g1BindsList b.toList, Stmt.g1BindsList hnd.toList with
      | some c, some d => some (c ++ d)
      | _, _ => Option.none
    -- Pass 0 (§import forms): no import form is ever bind-invisible.
    -- The names form OVER-reports its names — Pass 0 binds nothing (the
    -- raise fires before any binding), the future modeled-module arm
    -- will bind, and over-reporting is the poisoning-safe direction: it
    -- is what makes `moduleClockOk`'s clause (2) fail on
    -- `from x import time`. Star is unanalysable by fiat (its bind set
    -- is unknowable without a module), so a top-level star import fails
    -- the clock census too — a from-import can NOT open a path around
    -- the trace-clock discipline.
    | .importFrom _ names star _ =>
      if star then Option.none else some names.toList
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

/-- Statements the init pipeline will ATTEMPT to EXECUTE when the pure
fold refuses them (pass 3, docs/memory-model.md §module-init execution).
The static fold marks DIVERGENCE at the first such statement: a
successful attempt commits allocations the pure fold never sees, so
later static ref bindings would carry addresses into the wrong heap.
`.unsupported` statements (imports …) are NOT candidates — `execStmt`
refuses them and the attempt rolls back, so no divergence is possible.
A refused ASSIGN is also a candidate; its trigger is dynamic (the fold's
own refusal), handled in `globalsStep`'s assign arm. -/
def g1ExecCandidate : Stmt → Bool
  | .defStmt .. => true
  | .forStmt .. => true
  | .ifStmt .. => true
  | .whileLoop .. => true
  | .augAssign .. => true
  | .exprStmt (.constant ..) _ => false
  | .exprStmt .. => true
  -- exceptions tier: top-level raise/try are attempted (a raise `.exn`
  -- rolls back and poisons — the fold's recorded `.exn` imprecision)
  | .raiseStmt .. => true
  -- the tail batch: an `assert` can RAISE, so the fold must attempt it
  -- rather than skip it — the same reason `raise` is a candidate.
  | .assertStmt .. => true
  -- del RECONCILED: the exec attempt always refuses at init (empty init
  -- locals), so candidacy routes it to the rollback that POISONS the
  -- targets (`g1Binds` above) — skipping it would keep them stale.
  | .delStmt .. => true
  | .tryStmt .. => true
  | .withStmt .. => true
  -- Pass 0 (§import forms): a top-level `importFrom` IS a candidate.
  -- The "imports are not candidates" note above is about `.unsupported`
  -- statements, which execStmt REFUSES (no divergence possible); this
  -- one RAISES, and a raising candidate takes the fold's recorded
  -- `.exn` rollback-and-poison path. (The guarded try was already a
  -- candidate.)
  | .importFrom .. => true
  | _ => false

mutual
  /-- Is this RHS HEAP-PURE against the accumulator: constants,
  statically-clean names whose values are REF-FREE, and operators over
  those — no subscript, attribute, call, display, slice. Post-divergence
  the static fold values a binding only under this predicate: a ref
  result would carry a fold-heap address into the (different) live heap,
  and a heap-READING scalar could contradict a live mutation the
  syntactic store scan missed. -/
  def g1HeapPure (acc : GlobalsAcc) : Expr → Bool
    | .constant .. => true
    | .name id _ =>
      (match lookupG acc id with
       | some (some v) => RVal.refFree v
       | _ => false)
    | .binOp l _ r _ => g1HeapPure acc l && g1HeapPure acc r
    | .unaryOp _ e _ => g1HeapPure acc e
    | .formattedValue value _ _ => g1HeapPure acc value
    | .formattedValueAscii value _ => g1HeapPure acc value
    | .boolOp _ vs _ => g1HeapPureList acc vs.toList
    | .compare l _ cs _ => g1HeapPure acc l && g1HeapPureList acc cs.toList
    | .ifExp t b o _ => g1HeapPure acc t && g1HeapPure acc b && g1HeapPure acc o
    | .tuple es _ => g1HeapPureList acc es.toList
    | _ => false

  /-- Elementwise `g1HeapPure`. -/
  def g1HeapPureList (acc : GlobalsAcc) : List Expr → Bool
    | [] => true
    | e :: es => g1HeapPure acc e && g1HeapPureList acc es
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

/-- Post-divergence binding gate (pass 3): value the binding only when
the RHS was heap-pure AND every bound value is ref-free — else poison
(the live view serves the read). Pre-divergence this is the identity. -/
def g1DivGate (diverged : Bool) (acc : GlobalsAcc) (rhs : Expr)
    (bs : List (String × Option RVal)) : List (String × Option RVal) :=
  if !diverged then bs
  else if g1HeapPure acc rhs
      && bs.all (fun b => (b.2.map RVal.refFree).getD true) then bs
  else bs.map (fun b => (b.1, (Option.none : Option RVal)))

/-- One module-level statement's effect on the init heap and the globals.
`(h, acc, analysable)`: `analysable = false` once a statement's binding
set could not be determined. A failed RHS binds its names out-of-tier AND
discards its partial allocations (the original heap rides through — no
refs escape a refusal); everything out of tier goes to `globalsDirty`. -/
def globalsStep (h : Heap) (acc : GlobalsAcc) (analysable diverged : Bool)
    (s : Stmt) : Heap × GlobalsAcc × Bool × Bool :=
  match s with
  | .assign tgts rhs _ =>
    match tgts.toList with
    | [.name id _] =>
      match evalGlobalExpr h (resolvedG acc) globalFuel rhs with
      | .ok (h', v) =>
        (h', g1DivGate diverged acc rhs [(id, some v)] ++ acc, analysable, diverged)
      | .exn _ => (h, (id, Option.none) :: acc, analysable, diverged)
      | _ =>
        -- fold refusal: the init pipeline will ATTEMPT this assign, so
        -- the heaps may diverge from here on
        (h, (id, Option.none) :: acc, analysable, true)
    | [.tuple es _] =>
      match targetNamesG es.toList with
      | some ids =>
        match evalGlobalExpr h (resolvedG acc) globalFuel rhs with
        | .ok (h', .tuple vs) =>
          if ids.length == vs.size then
            (h', g1DivGate diverged acc rhs
              ((ids.zip (vs.toList.map some)).reverse) ++ acc, analysable, diverged)
          else (h, ids.map (·, Option.none) ++ acc, analysable, diverged)
        | .ok (h', .listV vs) =>
          if ids.length == vs.size then
            (h', g1DivGate diverged acc rhs
              ((ids.zip (vs.toList.map some)).reverse) ++ acc, analysable, diverged)
          else (h, ids.map (·, Option.none) ++ acc, analysable, diverged)
        | .exn _ => (h, ids.map (·, Option.none) ++ acc, analysable, diverged)
        | _ => (h, ids.map (·, Option.none) ++ acc, analysable, true)
      | Option.none =>
        match globalsDirty h acc analysable s with
        | (h', acc', an') => (h', acc', an', diverged || g1ExecCandidate s)
    | _ =>
      match globalsDirty h acc analysable s with
      | (h', acc', an') => (h', acc', an', diverged || g1ExecCandidate s)
  | .pass _ => (h, acc, analysable, diverged)
  -- Class definitions are ordered markers in the script stream.  Closed
  -- function calls do not execute class creation, so module initialization
  -- treats the marker as a definition-only no-op; script mode handles the
  -- marker in its own executor.
  | .unsupported "ClassDef" _ _ => (h, acc, analysable, diverged)
  -- a bare expression binds nothing; `globalsDirty` records that it can
  -- still STORE (and the recorded call-mutation gap in the section
  -- comment above)
  | s =>
    match globalsDirty h acc analysable s with
    | (h', acc', an') => (h', acc', an', diverged || g1ExecCandidate s)

/-- Fold `globalsStep` over the top-level statements (source order). -/
def globalsFold (h : Heap) (acc : GlobalsAcc) (analysable diverged : Bool) :
    List Stmt → Heap × GlobalsAcc × Bool × Bool
  | [] => (h, acc, analysable, diverged)
  | s :: rest =>
    match globalsStep h acc analysable diverged s with
    | (h', acc', analysable', diverged') =>
      globalsFold h' acc' analysable' diverged' rest

/-- The whole module-init result: the init heap, the accumulator, the
ANALYSABLE flag and the DIVERGED flag — a pure function of the module
(fixed `globalFuel`). -/
def moduleInit (m : Module) : Heap × GlobalsAcc × Bool × Bool :=
  globalsFold #[] [] true false m.topLevel.toList

/-- The module's constant globals: `(bindings, analysable)` — the static
name-resolution table (see the section comment for why static reads are
faithful, and for what the two independent facts mean). -/
def moduleGlobals (m : Module) : GlobalsAcc × Bool :=
  ((moduleInit m).2.1, (moduleInit m).2.2.1)

/-! ### The trace clock (pass 6 — docs/memory-model.md §the trace clock)

Time as an INPUT: `World.clock` is a finite trace of opaque integer
readings, and evaluating exactly `time.time()` pops the next one. The
admission is decided by the pure `isClockCall` below; everything failing
it — `time` as a bare value, `time.sleep`, any other attribute, args,
kwargs, a shadowed or rebound `time` — takes the pre-existing paths
(poisoned-binding refusal / faithful errors) verbatim. -/

/-- Is this top-level statement the exact benign clock import? -/
def stmtIsClockImport : Stmt → Bool
  | .unsupported "Import" "import time" _ => true
  | _ => false

/-- The clock CENSUS: the module's poisoned `time` binding provably IS
the benign import's. Requires (1) some top-level `import time`; (2)
every OTHER top-level statement bind-analysable and binding/storing
anything but `time` (an unanalysable statement fails the census — it
might bind it); (3) no function or class subtree carrying `global` (the
extractor-recorded `has_global`, the namedtuple census's discipline — a
`global time` rebinding at call time would make the trace silently
shadowable). -/
def moduleClockOk (m : Module) : Bool :=
  m.topLevel.any stmtIsClockImport
    && m.topLevel.all (fun s =>
         stmtIsClockImport s ||
           (match s.g1Binds with
            | some bs => !(bs.contains "time") && !(s.g1Stores.contains "time")
            | Option.none => false))
    && m.functions.all (fun f => !f.hasGlobal)
    && m.classes.all (fun c => !c.hasGlobal)

/-- The receiver-side fork of the clock admission: the receiver is
literally the NAME `time`, UNSHADOWED at the consultation point — not in
frame locals, statically POISONED (the benign-import binding's state in
the G1 table), absent from the live view — in a module whose census
passes. Kept SEPARATE from the `attr == "time"` test (see `isClockCall`)
so the fragment proofs never need to open this match at a symbolic
receiver. -/
def clockRecvOk (m : Module) (st : FrameState) : Expr → Bool
  | .name tn _ =>
      tn == "time"
        && (Env.lookup st.locals tn).isNone
        && (match lookupG (moduleGlobals m).1 tn with
            | some Option.none => true
            | _ => false)
        && (Env.lookup st.world.globals tn).isNone
        && moduleClockOk m
  | _ => false

/-- The trace-clock admission (docs/memory-model.md §the trace clock),
decided BEFORE the receiver evaluates. The `attr == "time"` conjunct is
FIRST and OUTSIDE the receiver match, so the fork collapses at a SYMBOLIC
receiver and world as soon as the attribute is known not to be `time` —
which is exactly what the heap-free fragment's meta-theorems (`worldInv`,
`fuelMono`) consume. `time` is deliberately outside `heapFreeAttr` (a
clock read CONSUMES a reading, so it changes the world), which is what
makes `isClockCall_of_heapFreeAttr` hold for every whitelisted call. -/
def isClockCall (m : Module) (st : FrameState) (recv : Expr)
    (attr : String) : Bool :=
  attr == "time" && clockRecvOk m st recv

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

/-- A reserved environment key marks a name declared `global` in the current
frame.  Python identifiers cannot contain `<`, so the marker cannot collide
with source bindings.  Keeping the declaration in the ordinary environment
avoids changing `FrameState` (and the proof-facing call signatures) while
letting every expression and target consult the same lexical fact. -/
def globalMarker (id : String) : String := "<global>" ++ id

def globalDeclared (locals : Env) (id : String) : Bool :=
  (Env.lookup locals (globalMarker id)).isSome

/-- A script-level deletion of the runner-supplied `__name__` uncovers the
BUILTINS module's own `__name__` value (`"builtins"`). The marker lives in the
threaded module environment so both function and script name resolution can
override the static `scriptNameBinding` without changing the public frame type.
It is unspellable by Python source. -/
def deletedModuleDunderMarker (id : String) : String :=
  "<deleted-module-dunder>" ++ id

/-! ### PEP 526 value-less annotations

`x: T` in a function body does not execute a value store, but it DOES make
`x` a local for the whole frame.  A dynamic environment therefore needs one
small piece of frame metadata: a reserved marker for each such declaration.
The marker is deliberately kept in `Env` (like `globalMarker`) so the proof
surface and the public frame type do not change.  A later ordinary assignment
shadows the marker in lookup order; a read while the marker is still the first
binding raises the faithful `UnboundLocalError`.

The extractor leaves observed declarations as `Unsupported "AnnAssign:no-value"`
nodes.  Their source text is enough to recover the plain target name, while
the recursive walker makes declarations in a branch/loop local from function
entry, as CPython's symbol-table pass requires.  Function definitions are
scope boundaries and are intentionally not descended into here. -/

def unboundLocalMarker (id : String) : String := "<unbound-local>" ++ id

def hasUnboundLocal (locals : Env) (id : String) : Bool :=
  (Env.lookup locals (unboundLocalMarker id)).isSome

def annNoValueName (text : String) : Option String :=
  match text.splitOn ":" with
  | name :: _ =>
      let name := name.trim
      if name == "" then Option.none else some name
  | [] => Option.none

mutual
  partial def stmtUnboundLocalNames : Stmt → List String
    | .unsupported "AnnAssign:no-value" text _ =>
        (annNoValueName text).toList
    | .delStmt names _ => names.toList
    | .whileLoop _ body orelse _ | .ifStmt _ body orelse _ =>
        (body.toList.map stmtUnboundLocalNames).flatten
          ++ (orelse.toList.map stmtUnboundLocalNames).flatten
    | .forStmt _ _ body orelse _ =>
        (body.toList.map stmtUnboundLocalNames).flatten
          ++ (orelse.toList.map stmtUnboundLocalNames).flatten
    | .tryStmt body _ handler _ _ =>
        (body.toList.map stmtUnboundLocalNames).flatten
          ++ (handler.toList.map stmtUnboundLocalNames).flatten
    | .withStmt _ body _ _ =>
        (body.toList.map stmtUnboundLocalNames).flatten
    | .defStmt name .. => [name]
    | _ => []

  partial def stmtUnboundLocalNamesList : List Stmt → List String
    | [] => []
    | s :: ss => stmtUnboundLocalNames s ++ stmtUnboundLocalNamesList ss
end

def directRaiseName : Stmt → Option String
  | .raiseStmt (some (.name id _)) _ _ => some id
  | _ => Option.none

def directAssignName : Stmt → Option String
  | .assign #[.name id _] _ _ => some id
  | _ => Option.none

def hasDirectAssignAfter (id : String) : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      match directAssignName stmt with
      | some name => name == id || hasDirectAssignAfter id rest
      | none => hasDirectAssignAfter id rest

def lateRaiseNames : List Stmt → List String
  | [] => []
  | stmt :: rest =>
      let tail := lateRaiseNames rest
      match directRaiseName stmt with
      | some id =>
          if hasDirectAssignAfter id rest then id :: tail else tail
      | none => tail

def markUnboundLocals (body : List Stmt) (env : Env) : Env :=
  (stmtUnboundLocalNamesList body ++ lateRaiseNames body).foldl
    (fun env id => Env.set env (unboundLocalMarker id) RVal.none) env

/-- Extract names from the extractor's retained `Unsupported Global` text.
The declaration has no runtime action; its names are the compile-time scope
fact consumed by the call frame. -/
def globalNamesText (text : String) : List String :=
  ((String.ofList (text.toList.drop 6)).splitOn ",").map String.trim
    |>.filter (· != "")

def nonlocalNamesText (text : String) : List String :=
  ((String.ofList (text.toList.drop 8)).splitOn ",").map String.trim
    |>.filter (· != "")

def globalNamesBody (body : Array Stmt) : List String :=
  (body.toList.filterMap fun s => match s with
    | .unsupported "Global" text _ => some (globalNamesText text)
    | _ => none).flatten

def globalMarkedEnv (body : Array Stmt) : Env :=
  (globalNamesBody body).map (fun id => (globalMarker id, RVal.none))

def mkCallEnvGlobals (params : Array Param) (args : Array RVal)
    (body : Array Stmt) (hasGlobal : Bool) : Env :=
  let env := if hasGlobal then globalMarkedEnv body ++ mkCallEnv params args
    else mkCallEnv params args
  markUnboundLocals body.toList env

def globalCallEnv (w : World) (params : Array Param) (args : Array RVal)
    (body : Array Stmt) (hasGlobal : Bool) : Env :=
  let env := if hasGlobal then
      let names := globalNamesBody body
      let values := names.filterMap fun id =>
        match Env.lookup w.globals id with
        | some v => some (id, v)
        | none => none
      globalMarkedEnv body ++ values ++ mkCallEnv params args
    else mkCallEnv params args
  markUnboundLocals body.toList env

/-- The first global slice admits only direct statements.  A global name in a
loop/compound target, unpack, or attribute needs a frame-aware target walker;
that shape stays loud until it has one, while direct scalar reads/writes are
fully stateful. -/
def globalSimpleBody : Array Stmt → Bool :=
  (·.toList.all fun s => match s with
    | .unsupported "Global" _ _ => true
    | .assign #[.name _ _] _ _ => true
    | .augAssign (.name _ _) _ _ _ => true
    | .ret .. | .exprStmt .. | .pass _ => true
    | _ => false)

/-- First keyword name bound twice, if any. CPython rejects a repeated
literal keyword (`f(a=1, a=2)`) at COMPILE time, so ingestion never ships
one — the guard keeps hand-built modules loud, never guessing an error
class CPython would not have reached. -/
def kwFindDup : List (String × RVal) → Option String
  | [] => Option.none
  | (k, _) :: rest => if rest.any (·.1 == k) then some k else kwFindDup rest

/-! ### The arity `TypeError`, in CPython's own two shapes

Until 2026-08-16 every arity failure got ONE canonical message — the
`takes … but … were given` form — on the recorded ground that "the
harness compares exception CLASS names, so one canonical message serves
both". Library mode's message tier made that shortcut a WRONG FACT: too
FEW arguments is a different sentence in CPython, with a different
subject and a list of the parameters it did not get. All of the grammar
below was measured live on 3.9.19, never read off a doc page. -/

/-- CPython's parameter-name list: `'a'` | `'a' and 'b'` |
`'a', 'b', and 'c'` — the Oxford comma appears from THREE on (measured to
five). -/
def quoteNamesTail : List String → String
  | [] => ""
  | [a] => s!"and '{a}'"
  | a :: rest => s!"'{a}', " ++ quoteNamesTail rest

@[inherit_doc quoteNamesTail]
def quoteNames : List String → String
  | [] => ""
  | [a] => s!"'{a}'"
  | [a, b] => s!"'{a}' and '{b}'"
  | a :: rest => s!"'{a}', " ++ quoteNamesTail rest

/-- The arity `TypeError`'s text. `ps` is the callee's parameter list as
(name, has-a-default) IN ORDER — enough for both shapes and independent of
`Param`, which is what lets a namedtuple's synthetic `__new__` use the
same builder.

TOO MANY (`given` exceeds the parameter count) is the TAKES form, and it
has three graduations, all measured: `takes 1 positional argument` is
singular; `but 1 was given` is singular independently; and a callee with
defaults says `takes from L to N positional arguments` — plural even when
`L`/`N` are 0 and 1.

Otherwise it is the MISSING form, which names the defaultless parameters
the call did not reach: `missing 2 required positional arguments: 'j' and
'prom'`. Reached only from a failing `arityOk`, so the list is non-empty
by the caller's precondition. -/
def arityErrorMsg (callee : String) (ps : List (String × Bool)) (given : Nat) : String :=
  let n := ps.length
  let required := (ps.filter (fun p => !p.2)).length
  if given > n then
    (if required == n then
       s!"{callee}() takes {n} positional argument" ++ (if n == 1 then "" else "s")
     else
       s!"{callee}() takes from {required} to {n} positional arguments")
      ++ s!" but {given} " ++ (if given == 1 then "was" else "were") ++ " given"
  else
    let missing := (ps.drop given).filter (fun p => !p.2) |>.map Prod.fst
    s!"{callee}() missing {missing.length} required positional argument"
      ++ (if missing.length == 1 then "" else "s") ++ ": " ++ quoteNames missing

/-- `arityErrorMsg` over a real parameter array. -/
def paramArity (params : Array Param) : List (String × Bool) :=
  params.toList.map fun p => (p.arg, p.default.isSome)

/-- `arityErrorMsg` for a NAMEDTUPLE constructor, and the two corrections
it carries are both measured. CPython 3.9's `namedtuple` builds `__new__`
by `eval`ing a LAMBDA, so the callee it names is `<lambda>` and not the
class; and that lambda's first parameter is `_cls`, so both counts are one
higher than the field count. `Move(1)` is
`<lambda>() missing 2 required positional arguments: 'j' and 'prom'`, and
`Move(1,2,3,4)` is `<lambda>() takes 4 positional arguments but 5 were
given`. -/
def ntArityErrorMsg (fields : Array String) (given : Nat) : String :=
  arityErrorMsg "<lambda>"
    (("_cls", false) :: fields.toList.map (fun f => (f, false))) (given + 1)

/-- Keyword construction for a namedtuple. CPython implements the constructor
through a synthetic `<lambda>` with `_cls` followed by the fields, so the
ordinary positional arity message above applies after the hidden parameter is
accounted for. -/
def mergeNtKw (fields : Array String) (pos : List RVal)
    (kws : List (String × RVal)) : Res (Array RVal) :=
  let names := fields.toList
  match kwFindDup kws with
  | some k =>
    .unsupported s!"duplicate keyword argument '{k}' (unreachable through ingestion — CPython rejects it at compile time)"
  | Option.none =>
    if pos.length > fields.size then
      .exn (.typeError (ntArityErrorMsg fields pos.length))
    else match kws.find? (fun kv => !names.contains kv.1) with
    | some (k, _) =>
      .exn (.typeError s!"<lambda>() got an unexpected keyword argument '{k}'")
    | Option.none =>
      match kws.find? (fun kv => (names.take pos.length).contains kv.1) with
      | some (k, _) =>
        .exn (.typeError s!"<lambda>() got multiple values for argument '{k}'")
      | Option.none =>
        let missing := (names.drop pos.length).filter
          (fun n => (kws.find? (fun kv => kv.1 == n)).isNone)
        if !missing.isEmpty then
          .exn (.typeError
            (s!"<lambda>() missing {missing.length} required positional argument"
              ++ (if missing.length == 1 then "" else "s") ++ ": " ++ quoteNames missing))
        else
          .ok (pos ++ (names.drop pos.length).map (fun n =>
            match kws.find? (fun (kv : String × RVal) => kv.1 == n) with
            | some (_, v) => v
            | Option.none => .none)).toArray

/-- The names a keyword call leaves unfilled: no keyword supplies them
and they carry no default. In parameter order, which is the order
CPython's message lists them in. -/
def kwUnfilled (kws : List (String × RVal)) : List Param → List String
  | [] => []
  | p :: ps =>
    let rest := kwUnfilled kws ps
    if (kws.find? (·.1 == p.arg)).isSome || p.default.isSome then rest
    else p.arg :: rest

/-- The fill itself, TOTAL: reached only when `kwUnfilled` is empty, so
every parameter has a keyword or a default and no arm can fail. Splitting
the census from the fill is what lets the message name all the missing
names at once. -/
def fillKwSlotsGo (kws : List (String × RVal)) : List Param → List RVal
  | [] => []
  | p :: ps =>
    (match kws.find? (·.1 == p.arg) with
     | some (_, v) => v
     | Option.none => match p.default with
                      | some c => Const.toRVal c
                      | Option.none => .none)
      :: fillKwSlotsGo kws ps

/-- Fill the parameter slots AFTER the positional prefix (H6 keyword
merge): the keyword's value if given, else the literal default. ONE `TypeError` naming EVERY parameter left
unfilled, which is CPython's shape and not the per-parameter one this
raised until 2026-08-16: `def g(a, b, c)` called as `g(a=1)` is
`g() missing 2 required positional arguments: 'b' and 'c'`, measured — a
message naming only `'b'` states a fact that is not true of the call. -/
def fillKwSlots (fname : String) (kws : List (String × RVal))
    (ps : List Param) : Res (List RVal) :=
  match kwUnfilled kws ps with
  | [] => .ok (fillKwSlotsGo kws ps)
  | missing =>
    .exn (.typeError
      (s!"{fname}() missing {missing.length} required positional argument"
        ++ (if missing.length == 1 then "" else "s") ++ ": " ++ quoteNames missing))

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
    .exn (.typeError (arityErrorMsg fname (paramArity params) pos.length))
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
  | .bytes xs => .ok (.enumSeq i (bytesIntVals xs))
  | .tuple xs => .ok (.enumSeq i xs.toList)
  | .rangeV lo hi step => do return .enumSeq i (← rangeVals lo.toInt hi.toInt step.toInt)
  | .listV xs => .ok (.enumSeq i xs.toList)
  | .ntuple _ _ xs => .ok (.enumSeq i xs.toList)
  | .ref a =>
    (match Heap.get? h a with
     | some (.list _) => .ok (.enumList i a 0)
     | some (.dict es sv) => .ok (.enumDict i a 0 es.size sv .keys)
     | some (.generator ..) =>
         .unsupported "enumerate() over a generator is outside the tier (it would need a stepper inside the stepper; docs/backlog.md)"
     | some (.dictView da kind) =>
         (match Heap.get? h da with
          | some (.dict es sv) => .ok (.enumDict i da 0 es.size sv kind)
          | _ => .unsupported danglingMsg)
     | some (.instance _ _) => .exn (.typeError "'object' object is not iterable")
     | some (.cell _) => .unsupported cellInternal
     | some (.closure ..) => .exn (.typeError "'function' object is not iterable")
     | some (.pyset _) =>
        .unsupported "enumerate() over a set is outside the tier (hash order; docs/memory-model.md)"
     | Option.none => .unsupported danglingMsg)
  | v => .exn (.typeError s!"'{v.typeName}' object is not iterable")

/-- §iter: the initial frame of `iter(v)` — a heap DICT gets the live KEY
cursor and a heap LIST gets the live INDEX cursor.

WHY THE OTHER RECEIVERS REFUSE RATHER THAN ANSWER. CPython has a distinct
iterator TYPE per receiver — `list_iterator`, `str_iterator`,
`tuple_iterator`, `range_iterator`, `set_iterator`, `dict_keyiterator`, and
`iter(g) is g` for a generator — and each carries its own mutation regime.
The dict one is the flagship's (`del d[next(iter(d))]`, sunfish.py:541); the
list one is `list_iterator`, admitted here because it is a plain index cursor
with NO layout to guess (see `GenFrame.iterList`). The rest are an inch each,
and a REFUSAL where CPython answers is a witnessed capability gap, while a
guessed cursor is not.

Unlike `enumFrame` this worker has exactly ONE caller (the monadic rebuild's
`iter` arm): the trunk has no `iter` arm, so it never builds this frame and
never has to decide. That is the `forDict` arrangement, and it is why
§pycomplete-13's ruling (c) — declare the trunk's capability delta and
witness it — has nothing to rule on here. -/
def iterFrame (h : Heap) : RVal → Res GenFrame
  | .ref a =>
    (match Heap.get? h a with
     | some (.dict es sv) => .ok (.iterDict a 0 es.size sv)
     | some (.list _) => .ok (.iterList a 0)
     | some (.generator ..) =>
         .unsupported "iter() over a generator answers the generator ITSELF in CPython (`iter(g) is g`) — outside the tier"
     | some (.pyset _) =>
         .unsupported "iter() over a set is outside the tier (hash order; docs/memory-model.md)"
     | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
     | some (.instance _ _) => .exn (.typeError "'object' object is not iterable")
     | some (.cell _) => .unsupported cellInternal
     | some (.closure ..) => .exn (.typeError "'function' object is not iterable")
     | Option.none => .unsupported danglingMsg)
  | .str _ =>
      .unsupported "iter() over a str is outside the tier (CPython's `str_iterator` is its own cursor; docs/memory-model.md §dict iteration)"
  | .bytes xs => .ok (.iterBytes xs 0)
  | .tuple _ =>
      .unsupported "iter() over a tuple is outside the tier (CPython's `tuple_iterator` is its own cursor; docs/memory-model.md §dict iteration)"
  | .listV _ =>
      .unsupported "iter() over a boundary list is outside the tier (CPython's `list_iterator` is its own cursor; docs/memory-model.md §dict iteration)"
  | .ntuple .. =>
      .unsupported "iter() over a namedtuple is outside the tier (CPython's `tuple_iterator` is its own cursor; docs/memory-model.md §dict iteration)"
  | .rangeV .. =>
      .unsupported "iter() over a range is outside the tier (CPython's `range_iterator` is its own cursor; docs/memory-model.md §dict iteration)"
  | v => .exn (.typeError s!"'{v.typeName}' object is not iterable")

/-- §PEP 289 — a GENEXP's outermost iterator is created when the genexp OBJECT
is created, not when it is first stepped. The initial continuation of a
synthesized `<genexpr@n>` therefore carries the loop's cursor ALREADY, so the
size and `shapeVersion` it guards against are the ones current at creation.

**THIS IS A GENEXP RULE AND NOT A GENERATOR RULE, and the difference is
measured.** Calling a generator FUNCTION runs no code, so CPython has called no
`iter()` — mutate the dict between `g = gen(d)` and the first `next(g)` and
CPython iterates the MUTATED dict without complaint (measured: answers `1`,
drains `[1, 3]`). Making every generator eager would break that neighbour;
`gen_lab`'s mutation-after-create row is the witness that it did not.

**Only the OUTERMOST clause, and only a DICT receiver.** PEP 289 leaves inner
`for` clauses lazy (measured: `(x for x in d for y in boom())` constructs
without evaluating `boom`). And of the receivers only a dict carries a
snapshot — `forList` re-reads live, value sequences are immutable, `forGen`
holds no counts — so no other receiver can show the difference. Anything this
does not recognise falls through to the ordinary deferred continuation, which
is what every other generator gets. -/
def genInitCont (h : Heap) (qname : String) (env : Env) (body : List Stmt) :
    GenCont :=
  if qname.startsWith genExpPrefix then
    match body with
    | [.forStmt target (.name arg _) fbody orelse _] =>
      if arg == genExpArgName && orelse.isEmpty then
        (match Env.lookup env arg with
         | some (.ref a) =>
           (match Heap.get? h a with
            | some (.dict es sv) =>
                [.forDict target a 0 es.size sv .keys fbody.toList]
            | _ => [.block body])
         | _ => [.block body])
      else [.block body]
    | _ => [.block body]
  else [.block body]

/-- `itertools.count()` / `count(start)` / `count(start, step)`. -/
def countArgs : List RVal → Option (Int × Int)
  | [] => some (0, 1)
  | [s] => (asInt s).map (fun a => (a, 1))
  | [s, d] =>
    (match asInt s, asInt d with
     | some a, some b =>
       match s with
       | .bool _ => if b = 1 then some (a, b) else Option.none
       | _ => some (a, b)
     | _, _ => Option.none)
  | _ => Option.none

def countNumber (value : RVal) : Bool :=
  match value with
  | .int _ | .bool _ => true
  | .float _ => true
  | _ => false

/- The monadic iterator admits the immediate numeric inventory. Its state is
   kept as RVal so `count(True, 2)` yields `True` first and then integers, and
   `count(1, 0.5)` yields the integer first and then binary64 values. -/
def countArgsVal : List RVal → Option (RVal × RVal)
  | [] => some (.int 0, .int 1)
  | [start] =>
    if countNumber start then
      match start with
      | .bool b => some (.int (if b then 1 else 0), .int 1)
      | _ => some (start, .int 1)
    else Option.none
  | [start, step] =>
    if countNumber start && countNumber step then
      match start, step with
      | .bool b, .int 1 => some (.int (if b then 1 else 0), step)
      | .bool b, .bool true => some (.int (if b then 1 else 0), step)
      | _, _ => some (start, step)
    else Option.none
  | _ => Option.none

/-- Classify an integer-only count-frame admission miss without inventing
a nonnumeric exception for a valid floating-point counter. -/
def countRefusal (values : List RVal) : Res RVal :=
  if values.length > 2 then
    .exn (.typeError s!"count() takes at most 2 arguments ({values.length} given)")
  else if values.any (fun
      | .float number => number.isNaN
      | _ => false) then
    .unsupported "NaN payload/sign propagation in itertools.count requires an explicit floating-point oracle"
  else if values.any (fun
      | .float number => number.isInf
      | _ => false) then
    .unsupported "infinite floating-point stepping in itertools.count requires an explicit floating-point oracle"
  else if values.all (fun
      | .int _ | .bool _ | .float _ => true
      | _ => false) && values.any (fun
      | .float _ => true
      | _ => false) then
    .unsupported "float stepping in itertools.count is not yet modelled"
  else
    match values with
    | [.bool _, step] =>
      match asInt step with
      | some integer =>
        if integer != 1 then
          .unsupported "itertools.count with a bool start and non-unit step must preserve its first bool value; this is not yet modelled"
        else .exn (.typeError "a number is required")
      | Option.none => .exn (.typeError "a number is required")
    | _ => .exn (.typeError "a number is required")

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
  | .forDict .. :: k => some k
  | .forGen .. :: k => some k
  | .whileLoop .. :: k => some k
  -- a builtin-iterator frame is never a LOOP frame: it is the body of a
  -- generator object, so `break`/`continue` can never reach one (they
  -- unwind inside a body, and these frames have no body). Loud, not a
  -- silent pop.
  | .enumSeq .. :: _ | .enumList .. :: _ | .enumDict .. :: _
  | .iterDict .. :: _ | .iterList .. :: _ | .iterBytes .. :: _
  | .countFrom _ _ :: _ => Option.none
  | .countFromVal _ _ :: _ => Option.none

/-- `continue`: drop the pending blocks, KEEP the enclosing loop frame
(re-entering it takes the next element / re-tests). -/
def genContinue : GenCont → Option GenCont
  | [] => Option.none
  | .block _ :: k => genContinue k
  | k@(.forSeq ..  :: _) => some k
  | k@(.forList .. :: _) => some k
  | k@(.forDict .. :: _) => some k
  | k@(.forGen ..  :: _) => some k
  | k@(.whileLoop .. :: _) => some k
  | .enumSeq .. :: _ | .enumList .. :: _ | .enumDict .. :: _
  | .iterDict .. :: _ | .iterList .. :: _ | .iterBytes .. :: _
  | .countFrom _ _ :: _ => Option.none
  | .countFromVal _ _ :: _ => Option.none

mutual
  /-- Does this statement contain a `yield` in its own scope? The
  continuation walker delegates every yield-FREE statement to the
  ordinary `execStmt` (one source of truth for their semantics) and only
  opens the control constructs that can suspend. Structural, kernel
  computable. -/
  def Stmt.hasYield : Stmt → Bool
    | .yieldStmt .. => true
    -- pass 5: an UN-lowered `yield from` (the admitted shape was inlined
    -- at ingestion) is still a yield point syntactically — seen here so
    -- `genPlan` refuses it precisely instead of delegating
    | .yieldFromStmt .. => true
    | .whileLoop _ body orelse _ =>
        Stmt.hasYieldList body.toList || Stmt.hasYieldList orelse.toList
    | .forStmt _ _ body orelse _ =>
        Stmt.hasYieldList body.toList || Stmt.hasYieldList orelse.toList
    | .ifStmt _ body orelse _ =>
        Stmt.hasYieldList body.toList || Stmt.hasYieldList orelse.toList
    -- exceptions tier: a yield under `try` (either arm) makes the try
    -- SUSPENDABLE — seen here so `genPlan` can refuse it precisely
    | .tryStmt body _ handler _ _ =>
        Stmt.hasYieldList body.toList || Stmt.hasYieldList handler.toList
    | .withStmt _ body _ _ => Stmt.hasYieldList body.toList
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
    | .withStmt .. => .refuse "'with' in a generator body is outside the v0 tier"
    -- exceptions tier (docs/memory-model.md §exceptions): a `yield`
    -- under `try` would make the try a SUSPENDABLE construct needing
    -- its own GenFrame — refused in v0. A yield-free try never reaches
    -- this arm (`hasYield` is false, so it DELEGATES whole: its
    -- internal raise/catch is invisible to the frame stack).
    | .tryStmt .. =>
      .refuse "a 'yield' under 'try' would make the try suspendable (it would need its own generator frame) — outside the tier (docs/memory-model.md §exceptions)"
    -- pass 5: the admitted `yield from <genexp>` shape was INLINED at
    -- ingestion; whatever survives is outside the inlining admission
    | .yieldFromStmt .. =>
      .refuse "un-lowered 'yield from' (the iterable is not an admitted genexp, or the genexp's target occurs elsewhere in the body) — outside the tier (docs/memory-model.md §yield from)"
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

/-- **The attribute-CALL whitelist of the world-preservation fragment**
(2026-08-15, docs/backlog.md — the extension past `.get`-only).

Membership is decided from the attribute NAME alone, which is all syntax
knows; soundness is then per receiver kind, and every kind is covered:

* `.get` — the dict READ. The one member with a live `.ok` arm that
  touches the heap, and it only reads (`heapGet`).
* `swapcase`/`isupper`/`islower`/`upper`/`index`/`join` — the PURE str methods
  (H5 strings). Strings are immutable VALUES: each arm is argument
  evaluation followed by `Run.liftRes` on a total pure worker, so the
  world rides through untouched.
* `is_integer` — the zero-argument float predicate. It is a pure numeric
  query and returns `False` for NaN and infinities, matching CPython.

Every other receiver is vacuous for `.ok`-invariance rather than merely
unlikely, which is why this is sound and not optimistic. On a heap
receiver (`attrCallPlan`) the five str names miss `get`/`clear` on a
dict, miss `append`/`pop`/`insert` on a list, and refuse outright on a
generator/closure/set — and an INSTANCE receiver cannot dispatch at all,
because a heap-free module has no classes (`Module.heapFree_classes`), so
the plan is `.instAttrValue` (loud), `.attrMissing` (an exn) or
`.dangling` (loud). On a namedtuple receiver `ntupleCallPlan_heapFree`
gives the same. `time` is deliberately ABSENT: it is the trace-clock
call, which CONSUMES a reading and so changes the world. -/
def heapFreeAttr (attr : String) : Bool :=
  attr == "get" || attr == "swapcase" || attr == "isupper"
    || attr == "islower" || attr == "upper" || attr == "index" || attr == "join"
    || attr == "is_integer"

/-- A whitelisted attribute is not some OTHER name — the shape every
soundness step below wants (each `attrCallPlan`/`strCallPlan` branch is
killed by naming the literal it would need). -/
theorem heapFreeAttr_ne {attr s : String} (ha : heapFreeAttr attr = true)
    (hs : heapFreeAttr s = false) : ¬ ((attr == s) = true) := by
  intro hc
  have hEq : attr = s := eq_of_beq hc
  subst hEq
  rw [ha] at hs
  simp at hs

mutual
  /-- Does evaluating this expression provably preserve the world? -/
  def Expr.heapFree : Expr → Bool
    | .constant .. => true
    | .name .. => true
    -- the WALRUS preserves the WORLD (it binds a frame local, and a cell
    -- is only ever written at a closure CALL) — but `worldInv` has no
    -- case for it yet, so the honest answer to "PROVABLY preserves" is
    -- `false`. Conservative: it only shrinks the fragment.
    | .namedExpr .. => false
    -- `&` also serves dictionary-key/set algebra and can allocate a fresh
    -- set when both operands are heap references.  Evict it from the
    -- world-preservation fragment conservatively; integer `&` still runs
    -- normally, but its proof path is outside `worldInv`.
    | .binOp l op r _ => op != .bitAnd && l.heapFree && r.heapFree
    | .unaryOp _ e _ => e.heapFree
    | .formattedValue value _ _ => value.heapFree
    | .formattedValueAscii value _ => value.heapFree
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
    -- 2026-08-13 adds `print`: it MUTATES `World.stdout`, the one effect
    -- the interpreter performs, so the world-preservation fragment must
    -- exclude it exactly as it excludes the allocating calls.
    -- §iter adds `iter`: it ALLOCATES an `Obj.generator` (the key cursor).
    -- It is not enough that the TRUNK refuses it — `funsHeapFree` is also the
    -- guard `callNamePlan` reads to conclude that a local holding a `.ref` in
    -- a heap-free module must be a DICT (closures allocate, so there can be
    -- none). An `it = iter(d)` that left the fragment intact would make that
    -- conclusion false, and `it(0)` would name the wrong type in a faithful
    -- `TypeError`. The carve-out is the same one `enumerate` and `count` have.
    | .call (.name id _) args kwargs _ _ =>
      kwargs.isEmpty && (id != "sorted") && (id != "next") && (id != "enumerate")
        && (id != "count") && (id != "any") && (id != "all") && (id != "set")
        && (id != "print") && (id != "list") && (id != starListBuiltinName)
        && (id != "dict") && (id != "iter")
        -- `<lenmult>` may fall back to heap-backed multiplication, which
        -- allocates; keep it outside the conditional world-preservation
        -- fragment even when its immediate fast path is pure.
        && (id != lenMultBuiltinName)
        -- The synthetic f-string format call is pure, but its proof branch
        -- is conservatively kept outside this conditional fragment.
        && (id != fstringFormatBuiltinName)
        && Expr.heapFreeList args.toList
    | .call (.attribute recv attr _) args kwargs _ _ =>
      kwargs.isEmpty && heapFreeAttr attr && recv.heapFree
        && Expr.heapFreeList args.toList
    | .call f args kwargs _ _ =>
      kwargs.isEmpty && f.heapFree && Expr.heapFreeList args.toList
    | .list .. => false                 -- ALLOCATES (H2)
    | .tuple es _ => Expr.heapFreeList es.toList
    | .subscript v i _ => v.heapFree && i.heapFree
    | .dict .. => false                 -- ALLOCATES
    | .attribute v _ _ => v.heapFree    -- as a bare value: loud, never `.ok`
    | .ifExp t b o _ => t.heapFree && b.heapFree && o.heapFree
    -- Slices may allocate when the receiver is a heap list; syntax cannot
    -- distinguish that case from strings or value tuples, so every slice
    -- expression leaves the world-preservation fragment.
    | .slice _ _ _ _ _ => false
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
    | .unpackAssign .. => false
    | .ret Option.none _ => true
    | .ret (some e) _ => e.heapFree
    | .assign tgts v _ =>
      (match tgts.toList with
       | [.subscript ..] => false       -- MUTATES (`d[k] = v`)
       | [.attribute ..] => false       -- MUTATES (H3 `self.x = v`)
       -- pass 4: a tuple target stays in the fragment iff all-names
       -- (attribute elements store through the heap)
       | [.tuple elts _] => (targetNames elts).isSome
       | _ => true) && v.heapFree
    -- pass 4: an attribute-target `+=` STORES through the heap
    | .augAssign t _ v _ =>
      (match t with | .attribute .. => false | _ => true) && v.heapFree
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
    -- pass 5: an un-lowered `yield from` only ever refuses (both
    -- executors), but it only occurs in generator bodies, which already
    -- evict the module — OUT, conservative and simple (§yield from)
    | .yieldFromStmt _ _ => false
    -- exceptions tier: `raise` never decides `.ok` (its outcomes are
    -- `.exn`/`.unsupported`), so its `.ok`-invariance is vacuous — IN.
    -- `try` is OUT (as-built delta, docs/memory-model.md §exceptions):
    -- the handler resumes from the body's retained `.exn` STATE, about
    -- which the ok-only `worldInv` induction knows nothing.
    | .raiseStmt .. => true
    -- the tail batch: `assert` evaluates its subexpressions and either
    -- returns the input state untouched or raises — it allocates
    -- nothing and mutates nothing, so it is IN the fragment exactly
    -- when both subexpressions are.
    | .assertStmt t m _ => t.heapFree && (m.map Expr.heapFree).getD true
    -- the tail batch (docs/memory-model.md §the del statement):
    -- unconditionally IN — `del <name>` evaluates NO sub-expression,
    -- allocates nothing, and rewrites only `st.locals`, which is not a
    -- `World` field (the recorded design's pricing, verbatim).
    | .delStmt .. => true
    | .tryStmt .. => false
    | .withStmt .. => false
    -- Pass 0 (§import forms): IN by the `raiseStmt` argument — the arm
    -- allocates nothing and never decides `.ok` (worldInv is `.ok`-only,
    -- so invariance is vacuous). REVIEW POINT for the future
    -- modeled-module arm: a binding import must flip this to `false` or
    -- re-prove — recorded so it is a review point, not a surprise.
    | .importFrom .. => true
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
  | .tryStmt b _ hnd _ _ =>
      Stmt.hasGenDefList b.toList || Stmt.hasGenDefList hnd.toList
  | .withStmt _ body _ _ => Stmt.hasGenDefList body.toList
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

mutual
  /-- Can this expression ALLOCATE an `Obj.generator`? Only three shapes
  can, and none needs a generator `def`: a call of `enumerate`, `count` or
  `iter` (the H4 generator FRAMES `enumSeq`/`countFrom`/`iterDict`), and a
  generator EXPRESSION that survived lowering (an admitted one becomes a
  synthesized generator function, which `funsAnyGen` sees). `next(…)`
  STEPS a generator and never builds one; an `unsupported` node refuses
  at evaluation, so it allocates nothing.

  §iter ADDED THE THIRD, and this list is the reason the inch had to be
  censused rather than transliterated: `iter(d)` allocates exactly as
  `enumerate(d)` does, so a module whose only generator is one of these
  would otherwise be classified generator-FREE and the script shell's
  `for k in iter(d)` would report ordinary Python as an internal heap
  well-formedness violation — the 2026-08-13 incident below, replayed.

  FOUND 2026-08-13 by `tools/leanpy`: `moduleGenFree` used to claim that
  a module with no generator def can hold no generator object, on the
  argument that "`callIn` is the only allocator". It is not, so
  `for i, c in enumerate("PNB"):` in such a module hit the generator
  guard and reported ORDINARY PYTHON as `internal: … heap
  well-formedness violation — report this`. -/
  def Expr.genAllocFree : Expr → Bool
    | .constant .. => true
    | .name .. => true
    -- a walrus allocates nothing of its own; its VALUE decides
    | .namedExpr _ v _ => v.genAllocFree
    | .binOp l _ r _ => l.genAllocFree && r.genAllocFree
    | .unaryOp _ e _ => e.genAllocFree
    | .formattedValue value _ _ => value.genAllocFree
    | .formattedValueAscii value _ => value.genAllocFree
    | .boolOp _ vs _ => Expr.genAllocFreeList vs.toList
    | .compare l _ cs _ => l.genAllocFree && Expr.genAllocFreeList cs.toList
    | .call (.name id _) args kwargs _ _ =>
      (id != "enumerate") && (id != "count") && (id != "iter")
        && Expr.genAllocFreeList args.toList && Expr.genAllocFreeKw kwargs.toList
    | .call f args kwargs _ _ =>
      f.genAllocFree && Expr.genAllocFreeList args.toList
        && Expr.genAllocFreeKw kwargs.toList
    | .list es _ => Expr.genAllocFreeList es.toList
    | .tuple es _ => Expr.genAllocFreeList es.toList
    | .subscript v i _ => v.genAllocFree && i.genAllocFree
    | .dict ks vs _ => Expr.genAllocFreeList ks.toList && Expr.genAllocFreeList vs.toList
    | .attribute v _ _ => v.genAllocFree
    | .ifExp t b o _ => t.genAllocFree && b.genAllocFree && o.genAllocFree
    | .slice v l u st _ =>
      v.genAllocFree && l.genAllocFree && u.genAllocFree && st.genAllocFree
    | .genExp .. => false
    | .unsupported .. => true

  /-- Elementwise `Expr.genAllocFree`. -/
  def Expr.genAllocFreeList : List Expr → Bool
    | [] => true
    | e :: es => e.genAllocFree && Expr.genAllocFreeList es

  /-- `Expr.genAllocFree` over keyword-argument values (H6). -/
  def Expr.genAllocFreeKw : List (String × Expr) → Bool
    | [] => true
    | (_, e) :: rest => e.genAllocFree && Expr.genAllocFreeKw rest
end

mutual
  /-- `Expr.genAllocFree` over a statement's whole subtree; a nested
  generator `def` allocates when it is CALLED, so it counts too. -/
  def Stmt.genAllocFree : Stmt → Bool
    | .ret Option.none _ => true
    | .ret (some e) _ => e.genAllocFree
    | .assign tgts v _ => Expr.genAllocFreeList tgts.toList && v.genAllocFree
    | .unpackAssign _ _ _ v _ => v.genAllocFree
    | .augAssign t _ v _ => t.genAllocFree && v.genAllocFree
    | .whileLoop t b o _ =>
      t.genAllocFree && Stmt.genAllocFreeList b.toList && Stmt.genAllocFreeList o.toList
    | .forStmt t it b o _ =>
      t.genAllocFree && it.genAllocFree
        && Stmt.genAllocFreeList b.toList && Stmt.genAllocFreeList o.toList
    | .ifStmt t b o _ =>
      t.genAllocFree && Stmt.genAllocFreeList b.toList && Stmt.genAllocFreeList o.toList
    | .exprStmt e _ => e.genAllocFree
    | .yieldStmt e _ => e.genAllocFree
    | .yieldFromStmt v _ => v.genAllocFree
    | .defStmt _ _ _ _ _ isGen body _ _ =>
      !isGen && Stmt.genAllocFreeList body.toList
    | .raiseStmt exc cause _ =>
      (exc.map Expr.genAllocFree).getD true && (cause.map Expr.genAllocFree).getD true
    | .assertStmt t m _ =>
      t.genAllocFree && (m.map Expr.genAllocFree).getD true
    -- the tail batch: `del` has no subexpression and allocates nothing
    | .delStmt .. => true
    | .tryStmt b _ hnd _ _ =>
      Stmt.genAllocFreeList b.toList && Stmt.genAllocFreeList hnd.toList
    | .withStmt .. => false
    -- Pass 0: no subexpression, allocates nothing (it raises)
    | .importFrom .. => true
    | .pass _ | .brk _ | .cont _ => true
    | .unsupported .. => true

  /-- Elementwise `Stmt.genAllocFree`. -/
  def Stmt.genAllocFreeList : List Stmt → Bool
    | [] => true
    | s :: ss => Stmt.genAllocFree s && Stmt.genAllocFreeList ss
end

/-- Elementwise `Stmt.genAllocFreeList` over function bodies. LIST
recursion on purpose (`funsHeapFree`'s shape): `Array.all` does not
reduce in the kernel, and `Module.heapFree` is discharged by `rfl` at
concrete modules. -/
def funsGenAllocFree : List FunctionDefn → Bool
  | [] => true
  | f :: fs => Stmt.genAllocFreeList f.body.toList && funsGenAllocFree fs

/-- Can NO `Obj.generator` exist in any world of any run of this module?
Two independent ways one can appear, and both are excluded here: a
generator `def` (`funsAnyGen` — `callIn` allocates the suspended frame)
and a generator-FRAME builtin or a surviving generator expression
(`genAllocFree`, over the function bodies AND the top level, since
module init executes). The boundary thaw cannot build one.

The generator entry points test this and refuse LOUDLY when it holds,
which is what keeps `worldInv` free of a heap-side invariant — the arm is
unreachable, and reaching it would be an interpreter bug, not a silent
wrong answer. The `genAllocFree` conjuncts are the 2026-08-13 repair: the
old definition asserted the same unreachability from `funsAnyGen` alone,
which `enumerate`/`count` falsify (see `Expr.genAllocFree`). -/
def moduleGenFree (m : Module) : Bool :=
  !funsAnyGen m.functions.toList
    && funsGenAllocFree m.functions.toList
    && Stmt.genAllocFreeList m.topLevel.toList

mutual
  /-- No nested `def` (closure creation) anywhere in the statement —
  pass 3: the live-view call guard's second conjunct (a module whose TOP
  LEVEL creates closures can dispatch them through `World.globals`, so
  the heap-free fragment must exclude it). -/
  def Stmt.defFree : Stmt → Bool
    | .defStmt .. => false
    | .whileLoop _ b o _ | .ifStmt _ b o _ =>
      Stmt.defFreeList b.toList && Stmt.defFreeList o.toList
    | .forStmt _ _ b o _ =>
      Stmt.defFreeList b.toList && Stmt.defFreeList o.toList
    | .tryStmt b _ hnd _ _ =>
      Stmt.defFreeList b.toList && Stmt.defFreeList hnd.toList
    | .withStmt _ body _ _ => Stmt.defFreeList body.toList
    | _ => true

  /-- Elementwise `Stmt.defFree`. -/
  def Stmt.defFreeList : List Stmt → Bool
    | [] => true
    | s :: ss => Stmt.defFree s && Stmt.defFreeList ss
end

/-- No module-level closure can ever be created (pass 3): the top level
contains no nested def. With `funsHeapFree` this guards every closure
CALL arm — worldInv's argument kills the dispatch through the fragment. -/
def topLevelDefFree (m : Module) : Bool :=
  Stmt.defFreeList m.topLevel.toList

/-- Module-level heap freedom: every function body (nested calls then stay
inside the fragment), no classes (H3: instantiation ALLOCATES and
syntax cannot tell a class call from a function call, so any class evicts
the whole module from the fragment — conservative, sound; class-using
modules live on `CallsIn`), no GENERATOR defs (H4: the same argument —
`gen_moves()` allocates a suspended frame), and — pass 3 — a top level
with no nested defs (module init would otherwise create closures the
live-view call arms can dispatch). Other top-level statements stay
unconstrained — they run only at module init, before any public run
begins. -/
def Module.heapFree (m : Module) : Bool :=
  funsHeapFree m.functions.toList && m.classes.toList.isEmpty && moduleGenFree m
    && topLevelDefFree m

/-- The FOUR conjuncts of `Module.heapFree`, projected (H4 made it a
three-way `&&` and pass 3's `topLevelDefFree` made it a four-way one, so
the `Bool.and_eq_true ▸` idiom no longer lines up positionally — these
are the names to cite instead). -/
theorem Module.heapFree_funs {m : Module} (hm : m.heapFree = true) :
    funsHeapFree m.functions.toList = true := by
  simp only [Module.heapFree, Bool.and_eq_true] at hm; exact hm.1.1.1

@[inherit_doc Module.heapFree_funs]
theorem Module.heapFree_classes {m : Module} (hm : m.heapFree = true) :
    m.classes.toList.isEmpty = true := by
  simp only [Module.heapFree, Bool.and_eq_true] at hm; exact hm.1.1.2

@[inherit_doc Module.heapFree_funs]
theorem Module.heapFree_genFree {m : Module} (hm : m.heapFree = true) :
    moduleGenFree m = true := by
  simp only [Module.heapFree, Bool.and_eq_true] at hm; exact hm.1.2

@[inherit_doc Module.heapFree_funs]
theorem Module.heapFree_topDefFree {m : Module} (hm : m.heapFree = true) :
    topLevelDefFree m = true := by
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
    -- `moduleGenFree` gained the `genAllocFree` conjuncts (2026-08-13),
    -- so the projection needs the leading component by name
    simp only [moduleGenFree, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at this
    exact this.1.1
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

/-- In a heap-free module, a WHITELISTED attribute call (`heapFreeAttr`)
never reaches a class method or a MUTATING arm: the plan is `dictGet` (a
heap READ — reachable only for `.get` itself) or a decided refusal —
`worldInv`'s attribute-call case forks on this. The mutating arms die on
the literal comparisons (no whitelisted name is `clear`/`append`/`pop`/
`insert`), the instance method arm on `getClass?`.

Generalized 2026-08-15 from the `attr = "get"` form: the whitelist is now
six names, and the proof no longer needs to know WHICH — only that it is
not one of the four mutators (`heapFreeAttr_ne`). -/
theorem attrCallPlan_heapFree {m : Module} (hm : m.heapFree = true)
    (h : Heap) (a : Addr) {attr : String} (ha : heapFreeAttr attr = true) :
    attrCallPlan m h a attr = .dictGet ∨
    attrCallPlan m h a attr = .instAttrValue ∨
    attrCallPlan m h a attr = .dangling ∨
    (∃ msg, attrCallPlan m h a attr = .refuse msg) := by
  unfold attrCallPlan
  cases Heap.get? h a with
  | none => right; right; left; rfl
  | some o =>
    cases o with
    | cell v => right; right; right; exact ⟨_, rfl⟩
    | dictView da kind => right; right; right; exact ⟨_, rfl⟩
    | dict es ver =>
      by_cases hg : (attr == "get") = true
      · rw [if_pos hg]; left; rfl
      · rw [if_neg hg, if_neg (heapFreeAttr_ne ha (by decide : heapFreeAttr "clear" = false)),
          if_neg (heapFreeAttr_ne ha (by decide : heapFreeAttr "keys" = false)),
          if_neg (heapFreeAttr_ne ha (by decide : heapFreeAttr "values" = false)),
          if_neg (heapFreeAttr_ne ha (by decide : heapFreeAttr "items" = false))]
        right; right; right; exact ⟨_, rfl⟩
    | list xs =>
      rw [if_neg (heapFreeAttr_ne ha (by decide : heapFreeAttr "append" = false)),
          if_neg (heapFreeAttr_ne ha (by decide : heapFreeAttr "pop" = false)),
          if_neg (heapFreeAttr_ne ha (by decide : heapFreeAttr "insert" = false))]
      right; right; right; exact ⟨_, rfl⟩
    | generator qn lo k st => right; right; right; exact ⟨_, rfl⟩
    | closure nm ps ao lo' hg ig bd cap => right; right; right; exact ⟨_, rfl⟩
    | pyset xs => right; right; right; exact ⟨_, rfl⟩
    | «instance» ci attrs =>
      cases hv : Env.lookup attrs.toList attr with
      | some v => simp [hv]
      | none => simp [hv, getClass?_heapFree hm ci]

/-- A whitelisted attribute call is never the TRACE-CLOCK call: `time` is
deliberately outside `heapFreeAttr` (a clock read CONSUMES a reading, so
it changes the world). This is the `isClockCall` fork `worldInv`'s
attribute case must clear before it reaches the receiver match. -/
theorem isClockCall_of_heapFreeAttr {m : Module} {st : FrameState}
    {recv : Expr} {attr : String} (ha : heapFreeAttr attr = true) :
    isClockCall m st recv attr = false := by
  have hne : (attr == "time") = false := by
    cases hb : attr == "time" with
    | false => rfl
    | true => exact absurd hb (heapFreeAttr_ne ha (by decide))
  simp [isClockCall, hne]

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

/-- Pass 0 (docs/memory-model.md §import forms (Pass 0)): the PINNED
two-row handler-name match table — the recorded first extension of
handler resolution beyond admitted user classes, landed AT MINIMUM
WIDTH. Handler names `ImportError` and `ModuleNotFoundError` both match
the kind `.importError` (CPython's one relevant subclass edge, carried
as a table, never a hierarchy walk). Consulted at BOTH resolution sites
(execStmt's tryStmt arm; Script.lean's try shell), and only AFTER
`findClass` misses: a USER class named `ImportError` resolves first
(statically-first, the existing order) and matches only `.user cid`, so
`.importError` propagates through it — CPython's behavior too (an
admitted `class ImportError(Exception): pass` is a different class and
catches nothing builtin). Every other builtin exception name beyond the
admitted table, tuple patterns and `as` bindings keep today's refusals
verbatim; `raise ImportError` stays refused (`raise` admits
only admitted user classes, unchanged). -/
def importErrorHandlerMatch : String → Bool
  | "ImportError" | "ModuleNotFoundError" => true
  | _ => false

/- The extractor encodes a tuple of plain exception names in the existing
`excName` field, separated by `|` (Python identifiers cannot contain that
character). Keep the tuple admission and matching logic shared by the
function and script interpreters. -/
/- `String.splitOn` is implemented through an irreducible runtime helper, so
the kernel cannot reduce it on the literal handler names in loaded ASTs.
The extractor's encoding uses exactly one-character `|` separators; a small
structural scanner keeps the same behavior while remaining reducible for
proofs. -/
def excHandlerNamesAux : List Char → List Char → List String
  | [], rev => [String.ofList rev.reverse]
  | '|' :: rest, rev => String.ofList rev.reverse :: excHandlerNamesAux rest []
  | c :: rest, rev => excHandlerNamesAux rest (c :: rev)

def excHandlerNames (encoded : String) : List String :=
  excHandlerNamesAux encoded.toList []

def excHandlerTuple (encoded : String) : Bool :=
  (excHandlerNames encoded).length > 1

def excHandlerAdmitted (m : Module) (name : String) : Bool :=
  if (findNamedTuple m name).isSome then false
  else
    match findClass m name with
    | some (_, c) => c.isExc
    | none =>
      importErrorHandlerMatch name || admittedBuiltinExc.contains name

def excHandlerMatches (m : Module) (name : String) (e : PyErr) : Bool :=
  match findClass m name with
  | some (ci, c) =>
      if !c.isExc then false
      else
        match e with
        | .user cid _ | .userMessage cid _ _ => cid == ci
        | _ => false
  | none =>
      if importErrorHandlerMatch name then
        match e with | .importError _ => true | _ => false
      else if admittedBuiltinExc.contains name then
        builtinExcCatches name e || userExcCatches m name e
      else false

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
    | .namedExpr id v _ =>
      -- H7+ (docs/memory-model.md §the walrus operator): evaluate, BIND
      -- in the frame that is running, answer the same value. A celled
      -- name keeps its plain binding here — the cell is written at the
      -- closure call, which is the only place it can be observed.
      evalExpr m fuel st v ⤳ fun st r =>
      .ok { st with locals := Env.set st.locals id r } r
    | .name id _ =>
      -- Resolution order: local env → module globals (G1, thawed on read;
      -- a later `X = …` rebinding a `def` name wins, as in CPython) →
      -- module function table → builtins `len`/`sorted`/… → NameError —
      -- the last only when the globals are COMPLETE (no invisible
      -- top-level binder), else loudly unsupported.
      match Env.lookup st.locals id with
      | some v => .ok st v
      | Option.none =>
        if hasUnboundLocal st.locals id then
          .exn st (.unboundLocalError id)
        else match lookupG (moduleGlobals m).1 id with
        | some (some v) =>
          if id == "__name__" then
            match Env.lookup st.world.globals (deletedModuleDunderMarker id) with
            | some dv => .ok st dv
            | Option.none => .ok st v
          else
            .ok st v
        | some Option.none =>
          -- pass 3: a statically-POISONED name consults the LIVE view
          -- (World.globals) before refusing — sound because the dirty
          -- pass poisons exactly what init execution touches, and
          -- bit-identical on pre-pass worlds (a `resolvedG` globals
          -- cannot contain a poisoned name, so the lookup misses)
          (match Env.lookup st.world.globals id with
           | some v => .ok st v
           | Option.none =>
             .unsupported s!"module-level value of '{id}' is outside the G1 tier")
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
          else
            -- pass 3: during init execution the threaded module is the
            -- per-statement PREFIX VIEW, so names the running suffix has
            -- bound are statically ABSENT — the live view is consulted
            -- before the NameError decision (post-init it carries every
            -- binding, so the arm stays faithful there too)
            (match Env.lookup st.world.globals id with
             | some v => .ok st v
             | Option.none =>
               if id == "Ellipsis" then .ok st .ellipsis
               else if isPyBuiltinName id || isLoweredBuiltinName id then
                 .unsupported (unmodelledBuiltinMsg id)
               else if (moduleGlobals m).2 then
                 .exn st (.nameError id)
               else
                 .unsupported s!"name '{id}' may be bound by an out-of-tier module-level statement")
    | .binOp l op r _ =>
        evalExpr m fuel st l ⤳ fun st a =>
        evalExpr m fuel st r ⤳ fun st b =>
        if op == .bitAnd then
          Run.liftRes st (evalBinOpH st.world.heap op a b) ⤳ fun st hr =>
          .ok { st with world := { st.world with heap := hr.1 } } hr.2
        else
          Run.liftRes st (evalBinOp op a b)
    | .unaryOp op operand _ =>
        evalExpr m fuel st operand ⤳ fun st v =>
        Run.liftRes st (evalUnaryOpH st.world.heap op v)
    | .formattedValue expression reprConversion _ =>
        evalExpr m fuel st expression ⤳ fun nextState value =>
        Run.liftRes nextState (formatValueH nextState.world.heap value reprConversion)
    | .formattedValueAscii expression _ =>
        evalExpr m fuel st expression ⤳ fun nextState value =>
        Run.liftRes nextState (asciiValH nextState.world.heap value)
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
              if funsHeapFree m.functions.toList && topLevelDefFree m then
                .exn st (.typeError "'dict' object is not callable")
              else
                match Heap.get? st.world.heap a with
                | some (.cell _) => .unsupported cellInternal
                | some (.closure nm ps ao lo _ ig bd cap) =>
                  Run.liftRes st (cellsFor st.world.heap st.locals cap) ⤳ fun st cap' =>
                  Run.withLocals st.locals
                    (callClosure m fuel st.world nm ps ao lo ig bd cap' vs.toArray)
                | _ =>
                  -- constant message on purpose: `typeNameH` here whnf-storms
                  -- symbolic proofs (the recorded H2 finding); the CLASS is
                  -- what the harness compares
                  .exn st (.typeError "'dict' object is not callable")
          | some v =>
              evalExprs m fuel st args.toList ⤳ fun st _ =>
              .exn st (.typeError s!"'{v.typeName}' object is not callable")
          | Option.none =>
            if !funsHeapFree m.functions.toList && hasUnboundLocal st.locals fname then
              .exn st (.unboundLocalError fname)
            else match lookupG (moduleGlobals m).1 fname with
            | some (some (.ref _)) =>
                evalExprs m fuel st args.toList ⤳ fun st _ =>
                .exn st (.typeError "'dict' object is not callable")
            | some (some v) =>
                evalExprs m fuel st args.toList ⤳ fun st _ =>
                .exn st (.typeError s!"'{v.typeName}' object is not callable")
            | some Option.none =>
              -- pass 3: the poisoned-arm LIVE view — a module-level
              -- lambda (an exec-bound closure) is callable through it,
              -- the locals-arm dispatch verbatim (`funsHeapFree`-guarded)
              (match Env.lookup st.world.globals fname with
               | some (.ref a) =>
                   evalExprs m fuel st args.toList ⤳ fun st vs =>
                   if funsHeapFree m.functions.toList && topLevelDefFree m then
                     .exn st (.typeError "'dict' object is not callable")
                   else
                     (match Heap.get? st.world.heap a with
                      | some (.cell _) => .unsupported cellInternal
                      | some (.closure nm ps ao lo _ ig bd cap) =>
                        Run.liftRes st (cellsFor st.world.heap st.locals cap) ⤳ fun st cap' =>
                        Run.withLocals st.locals
                          (callClosure m fuel st.world nm ps ao lo ig bd cap' vs.toArray)
                      | _ => .exn st (.typeError "'dict' object is not callable"))
               | some v =>
                   evalExprs m fuel st args.toList ⤳ fun st _ =>
                   .exn st (.typeError s!"'{v.typeName}' object is not callable")
               | Option.none =>
                 .unsupported s!"calling module-level '{fname}' (out-of-G1-tier value) is outside the tier")
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
                else if c.isExc then
                  -- exceptions tier: an exception class is a NAME to raise
                  -- and match, never an instantiable object — building the
                  -- instance as a VALUE would need inspectable payload
                  -- state the class-identity representation forgoes
                  .unsupported s!"calling exception class '{fname}' (an exception INSTANCE as a value) is outside the tier — exception classes are raised and matched by name (docs/memory-model.md §exceptions)"
                else match c.ntBase with
                | some nt =>
                  -- VALUE-LIKE SUBCLASS instantiation (H5, sunfish's
                  -- `class Position(namedtuple(…))`): construction IS
                  -- namedtuple construction — an IMMEDIATE value carrying
                  -- the SUBCLASS name, no allocation, no `__init__` run
                  -- (one on the immutable self is loud, never wrong).
                  if !c.ok then
                    .unsupported s!"class '{fname}' uses unsupported features besides its namedtuple base — instantiation is outside the tier"
                  else if (if c.methods.toList.contains "__enter__"
                              && c.methods.toList.contains "__exit__"
                           then c.methods.toList.any fun n =>
                             dunderShaped n && n != "__init__"
                               && n != "__enter__" && n != "__exit__" && n != "__repr__"
                           else hasNtupleExtraDunder c) then
                    .unsupported s!"class '{fname}' defines dunder methods beyond __init__ — implicit-protocol dispatch is outside the H3 tier"
                  else if (findFunction m (fname ++ ".__init__")).isSome then
                    .unsupported s!"'__init__' on the namedtuple subclass '{fname}' (immutable self) is outside the tier"
                  else
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    if vs.length == nt.fields.size then
                      .ok st (.ntuple nt.name nt.fields vs.toArray)
                    else
                      .exn st (.typeError (ntArityErrorMsg nt.fields vs.length))
                | Option.none =>
                  if !c.ok then
                    .unsupported s!"class '{fname}' uses unsupported features (bases/metaclass/decorators/class-level statements) — instantiation is outside the H3 tier"
                  else if (if c.methods.toList.contains "__enter__"
                              && c.methods.toList.contains "__exit__"
                           then c.methods.toList.any fun n =>
                             dunderShaped n && n != "__init__"
                               && n != "__enter__" && n != "__exit__" && n != "__repr__"
                           else classHasExtraDunder m ci) then
                    .unsupported s!"class '{fname}' defines dunder methods beyond __init__ — implicit-protocol dispatch is outside the H3 tier"
                  else
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    let a := st.world.heap.size
                    let st' := { st with world :=
                      { st.world with heap := st.world.heap.push (.instance ci (instanceAttrs m ci)) } }
                    match classMethodQname m ci "__init__" with
                    | some initName =>
                      Run.withLocals st'.locals
                        (callIn m fuel st'.world initName
                          ((RVal.ref a :: vs).toArray)) ⤳ fun st'' r =>
                      match r with
                      | .none => .ok st'' (.ref a)
                      | r =>
                        -- CPython checks __init__'s result: non-None raises
                        .exn st'' (.typeError s!"__init__() should return None, not '{r.typeName}'")
                    | Option.none =>
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
                    .exn st (.typeError (ntArityErrorMsg nt.fields vs.length))
                | Option.none =>
                  if fname == fstringFormatBuiltinName then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [v, .str spec] => Run.liftRes st (formatSpecH v spec)
                    | [_, spec] =>
                      .exn st (.typeError s!"format() argument 2 must be str, not {spec.typeName}")
                    | _ => .exn st (.typeError s!"internal: {fstringFormatBuiltinName} expects two arguments")
                  else if fname == lenMultBuiltinName then
                    -- Ingestion lowers `len(sequence * count)` to this
                    -- synthetic call so the pure proof interpreter can
                    -- answer the length without constructing an over-budget
                    -- sequence.  Heap-backed operands still use the ordinary
                    -- stateful multiplication path, exactly as the runner.
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [left, right] =>
                      match sequenceMultLength left right with
                      | some result => Run.liftRes st result
                      | Option.none =>
                        Run.liftRes st (evalBinOpH st.world.heap .mult left right) ⤳ fun st hr =>
                        Run.liftRes { st with world := { st.world with heap := hr.1 } }
                          (lenValH hr.1 hr.2)
                    | _ => .exn st (.typeError s!"internal: {lenMultBuiltinName} expects two arguments")
                  else
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
                        | .bytes values =>
                          Run.liftRes st
                            (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") (bytesIntVals values)))
                        | .tuple xs =>
                          Run.liftRes st
                            (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") xs.toList))
                        | .ntuple _ _ xs =>
                          Run.liftRes st
                            (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") xs.toList))
                        | .listV xs =>
                          Run.liftRes st
                            (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") xs.toList))
                        | .rangeV lo hi step =>
                          Run.liftRes st
                            (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") (← rangeVals lo.toInt hi.toInt step.toInt)))
                        | .ref a =>
                          (match Heap.get? st.world.heap a with
                           | some (.list xs) =>
                             Run.liftRes st
                               (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") xs.toList))
                           -- §L53 rung 3b: scans the KEYS, short-circuiting
                           | some (.dict es _) =>
                             Run.liftRes st
                               (do return RVal.bool (← anyAllScan st.world.heap (fname == "all") (dictKeys es).toList))
                           | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
                           | some (.instance _ _) =>
                             .exn st (.typeError "'object' object is not iterable")
                           | some (.generator ..) =>
                             Run.withLocals st.locals (anyAllIter m fuel st.world a (fname == "all")) ⤳ fun st b =>
                             .ok st (.bool b)
                           | some (.cell _) => .unsupported cellInternal
                           | some (.closure ..) =>
                             .exn st (.typeError "'function' object is not iterable")
                           | some (.pyset _) =>
                             .unsupported s!"{fname}() over a set is outside the tier (recorded; docs/memory-model.md)"
                           | Option.none => .unsupported danglingMsg)
                        | v => .exn st (.typeError s!"'{v.typeName}' object is not iterable"))
                     | vs => .exn st (.typeError s!"{fname}() takes exactly one argument ({vs.length} given)"))
                  else if fname == "set" then
                    -- H7+ sets (the honest subset): construction from an
                    -- iterable, DEDUPLICATED by value equality (the
                    -- dict-key doctrine gates elements); a generator
                    -- argument DRAINS (`set` is outside `heapFree`).
                    -- Membership/len/truthiness are the only readers.
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [] =>
                       .ok { st with world :=
                               { st.world with heap := st.world.heap.push (.pyset #[]) } }
                         (.ref st.world.heap.size)
                     | [v] =>
                       (match v with
                        | .str t =>
                          Run.liftRes st (setDedup st.world.heap fuel [] (strCharVals t)) ⤳ fun st es =>
                          .ok { st with world :=
                                  { st.world with heap := st.world.heap.push (.pyset es.toArray) } }
                            (.ref st.world.heap.size)
                        | .bytes values =>
                          Run.liftRes st (setDedup st.world.heap fuel [] (bytesIntVals values)) ⤳ fun st es =>
                          .ok { st with world :=
                                  { st.world with heap := st.world.heap.push (.pyset es.toArray) } }
                            (.ref st.world.heap.size)
                        | .tuple xs =>
                          Run.liftRes st (setDedup st.world.heap fuel [] xs.toList) ⤳ fun st es =>
                          .ok { st with world :=
                                  { st.world with heap := st.world.heap.push (.pyset es.toArray) } }
                            (.ref st.world.heap.size)
                        | .ntuple _ _ xs =>
                          Run.liftRes st (setDedup st.world.heap fuel [] xs.toList) ⤳ fun st es =>
                          .ok { st with world :=
                                  { st.world with heap := st.world.heap.push (.pyset es.toArray) } }
                            (.ref st.world.heap.size)
                        | .listV xs =>
                          Run.liftRes st (setDedup st.world.heap fuel [] xs.toList) ⤳ fun st es =>
                          .ok { st with world :=
                                  { st.world with heap := st.world.heap.push (.pyset es.toArray) } }
                            (.ref st.world.heap.size)
                        | .rangeV lo hi step =>
                          Run.liftRes st (rangeVals lo.toInt hi.toInt step.toInt) ⤳ fun st xs =>
                          Run.liftRes st (setDedup st.world.heap fuel [] xs) ⤳ fun st es =>
                          .ok { st with world :=
                                  { st.world with heap := st.world.heap.push (.pyset es.toArray) } }
                            (.ref st.world.heap.size)
                        | .ref a =>
                          (match Heap.get? st.world.heap a with
                           | some (.list xs) =>
                             Run.liftRes st (setDedup st.world.heap fuel [] xs.toList) ⤳ fun st es =>
                             .ok { st with world :=
                                     { st.world with heap := st.world.heap.push (.pyset es.toArray) } }
                               (.ref st.world.heap.size)
                           | some (.pyset xs) =>
                             -- set(s): a fresh copy (already deduplicated)
                             .ok { st with world :=
                                     { st.world with heap := st.world.heap.push (.pyset xs) } }
                               (.ref st.world.heap.size)
                           | some (.generator ..) =>
                             Run.withLocals st.locals (drainIter m fuel st.world a) ⤳ fun st vals =>
                             Run.liftRes st (setDedup st.world.heap fuel [] vals) ⤳ fun st es =>
                             .ok { st with world :=
                                     { st.world with heap := st.world.heap.push (.pyset es.toArray) } }
                               (.ref st.world.heap.size)
                           -- §L53 rung 3b: the KEYS, already distinct under the
                           -- dict-key doctrine, so setDedup is a no-op that is
                           -- still RUN rather than assumed away
                           | some (.dict es _) =>
                             Run.liftRes st (setDedup st.world.heap fuel [] (dictKeys es).toList) ⤳ fun st ds =>
                             .ok { st with world :=
                                     { st.world with heap := st.world.heap.push (.pyset ds.toArray) } }
                               (.ref st.world.heap.size)
                           | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
                           | some (.instance _ _) =>
                             .exn st (.typeError "'object' object is not iterable")
                           | some (.cell _) => .unsupported cellInternal
                           | some (.closure ..) =>
                             .exn st (.typeError "'function' object is not iterable")
                           | Option.none => .unsupported danglingMsg)
                        | v => .exn st (.typeError s!"'{v.typeName}' object is not iterable"))
                     | vs => .exn st (.typeError s!"set expected at most 1 argument, got {vs.length}"))
                  else if fname == "abs" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [v] => Run.liftRes st (absVal v)
                    | _ => .exn st (.typeError s!"abs() takes exactly one argument ({vs.length} given)")
                  else if fname == "round" then
                    -- The one-argument integer/Boolean slice: CPython's
                    -- `round(int)` returns the same mathematical integer,
                    -- while `round(bool)` returns an `int`, not a `bool`.
                    -- Float and ndigits protocols remain loud until their
                    -- rounding oracle is modeled.
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [] => .exn st (.typeError "round() missing required argument 'number' (pos 1)")
                    | [v] =>
                      (match v with
                       | .int n => .ok st (.int n)
                       | .bool b => .ok st (.int (if b then 1 else 0))
                       | _ => .unsupported "round() over floats and non-integral values is outside the tier (the one-argument integer/Boolean slice is modeled)"
                      )
                    | _ => .unsupported "round() with ndigits is outside the tier"
                  else if fname == "int" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    Run.liftRes st (intCastArgs vs)
                  else if fname == "float" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    Run.liftRes st (floatCastArgsH st.world.heap vs)
                  else if fname == "bool" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    Run.liftRes st (boolCastArgs st.world.heap vs)
                  else if fname == "divmod" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    Run.liftRes st (divmodArgs vs)
                  else if fname == "pow" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [base, exponent] => Run.liftRes st (evalBinOp .pow base exponent)
                     | [base, exponent, modulus] =>
                       Run.liftRes st (powModArgs [base, exponent, modulus])
                     | vs =>
                       .exn st (.typeError s!"pow() expected 2 or 3 arguments, got {vs.length}"))
                  else if fname == "sum" then
                    -- pass 3 (docs/memory-model.md §module-init
                    -- execution): the element fold IS `evalBinOp .add`;
                    -- a str START is CPython's special-cased refusal; a
                    -- GENERATOR argument DRAINS — guarded on
                    -- `moduleGenFree` (the `max`/`min` discipline), so
                    -- `sum` stays in the heap-free fragment
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match sumArgs vs with
                     | Option.none =>
                       .exn st (.typeError s!"sum() takes at most 2 arguments ({vs.length} given)")
                     | some (v, start) =>
                       (match start with
                        | .str _ =>
                          Run.liftRes st (sumRejectedStart m st.world.heap v
                            "sum() can't sum strings [use ''.join(seq) instead]")
                        | .bytes _ =>
                          Run.liftRes st (sumRejectedStart m st.world.heap v
                            "sum() can't sum bytes [use b''.join(seq) instead]")
                        | start =>
                          (match v with
                           | .tuple xs => Run.liftRes st (sumFold start xs.toList)
                           | .ntuple _ _ xs => Run.liftRes st (sumFold start xs.toList)
                           | .listV xs => Run.liftRes st (sumFold start xs.toList)
                           | .str t => Run.liftRes st (sumFold start (strCharVals t))
                           | .bytes values => Run.liftRes st (sumFold start (bytesIntVals values))
                           | .rangeV lo hi step =>
                             Run.liftRes st (do sumFold start (← rangeVals lo.toInt hi.toInt step.toInt))
                           | .ref a =>
                             (match Heap.get? st.world.heap a with
                              | some (.list xs) => Run.liftRes st (sumFold start xs.toList)
                              | some (.generator ..) =>
                                if moduleGenFree m then
                                  .unsupported "sum() over a generator DRAINS it (a stateful read) — outside the tier"
                                else
                                  Run.withLocals st.locals (drainIter m fuel st.world a) ⤳ fun st vals =>
                                  Run.liftRes st (sumFold start vals)
                              -- §L53 rung 3b: sums the KEYS, order-independent
                              | some (.dict es _) =>
                                Run.liftRes st (sumFold start (dictKeys es).toList)
                              | some (.pyset _) =>
                                .unsupported "sum() over a set is outside the tier (hash order; docs/memory-model.md)"
                              | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
                              | some (.instance _ _) =>
                                .exn st (.typeError "'object' object is not iterable")
                              | some (.cell _) => .unsupported cellInternal
                              | some (.closure ..) =>
                                .exn st (.typeError "'function' object is not iterable")
                              | Option.none => .unsupported danglingMsg)
                           | v => .exn st (.typeError s!"'{v.typeName}' object is not iterable"))))
                  else if fname == "tuple" || fname == starTupleBuiltinName then
                    -- pass 3: the tuple CONSTRUCTOR — an immediate value
                    -- (no allocation): str/tuple/namedtuple(class-erased,
                    -- CPython)/boundary list/heap list(snapshot — CPython
                    -- copies)/range/generator(+`moduleGenFree` guard);
                    -- dict/set receivers stay loud (order doctrine)
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [] => .ok st (.tuple #[])
                     | [v] =>
                       (match v with
                        | .str t => .ok st (.tuple (strCharVals t).toArray)
                        | .bytes values => .ok st (.tuple (bytesIntVals values).toArray)
                        | .tuple xs => .ok st (.tuple xs)
                        | .ntuple _ _ xs => .ok st (.tuple xs)
                        | .listV xs => .ok st (.tuple xs)
                        | .rangeV lo hi step =>
                          Run.liftRes st (do return RVal.tuple (← rangeVals lo.toInt hi.toInt step.toInt).toArray)
                        | .ref a =>
                          (match Heap.get? st.world.heap a with
                           | some (.list xs) => .ok st (.tuple xs)
                           | some (.generator ..) =>
                             if moduleGenFree m then
                               .unsupported "tuple() over a generator DRAINS it (a stateful read) — outside the tier"
                             else
                               Run.withLocals st.locals (drainIter m fuel st.world a) ⤳ fun st vals =>
                               .ok st (.tuple vals.toArray)
                           -- §L53 rung 3b: the KEYS in insertion order (this arm
                           -- also serves `[*d]`, which lowers through tuple)
                           | some (.dict es _) =>
                             .ok st (.tuple (dictKeys es))
                           | some (.pyset _) =>
                             .unsupported "tuple() over a set is outside the tier (hash order; docs/memory-model.md)"
                           | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
                           | some (.instance _ _) =>
                             .exn st (.typeError "'object' object is not iterable")
                           | some (.cell _) => .unsupported cellInternal
                           | some (.closure ..) =>
                             .exn st (.typeError "'function' object is not iterable")
                           | Option.none => .unsupported danglingMsg)
                        | v => .exn st (.typeError s!"'{v.typeName}' object is not iterable"))
                     | vs => .exn st (.typeError s!"tuple expected at most 1 argument, got {vs.length}"))
                  else if fname == "list" || fname == starListBuiltinName then
                    -- 2026-08-13 (list comprehensions): the list
                    -- CONSTRUCTOR — `tuple`'s inventory of iterables,
                    -- but it ALLOCATES a fresh heap object, because
                    -- CPython's `list(x)` is always a NEW list and never
                    -- an alias. The call therefore leaves
                    -- `Expr.heapFree`, which is also what lets the
                    -- generator arm drain without the `moduleGenFree`
                    -- guard `tuple` needs. dict/set receivers stay loud
                    -- (order doctrine).
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [] => allocListRun st #[]
                     | [v] =>
                       (match v with
                        | .str t => allocListRun st (strCharVals t).toArray
                        | .bytes values => allocListRun st (bytesIntVals values).toArray
                        | .tuple xs => allocListRun st xs
                        | .ntuple _ _ xs => allocListRun st xs
                        | .listV xs => allocListRun st xs
                        | .rangeV lo hi step =>
                          Run.liftRes st (rangeVals lo.toInt hi.toInt step.toInt) ⤳ fun st xs =>
                          allocListRun st xs.toArray
                        | .ref a =>
                          (match Heap.get? st.world.heap a with
                           | some (.list xs) => allocListRun st xs
                           | some (.generator ..) =>
                             Run.withLocals st.locals (drainIter m fuel st.world a) ⤳ fun st vals =>
                             allocListRun st vals.toArray
                           -- §L53 rung 3b: the KEYS in insertion order
                           | some (.dict es _) => allocListRun st (dictKeys es)
                           | some (.pyset _) =>
                             .unsupported "list() over a set is outside the tier (hash order; docs/memory-model.md)"
                           | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
                           | some (.instance _ _) =>
                             .exn st (.typeError "'object' object is not iterable")
                           | some (.cell _) => .unsupported cellInternal
                           | some (.closure ..) =>
                             .exn st (.typeError "'function' object is not iterable")
                           | Option.none => .unsupported danglingMsg)
                        | v => .exn st (.typeError s!"'{v.typeName}' object is not iterable"))
                     | vs => .exn st (.typeError s!"list expected at most 1 argument, got {vs.length}"))
                  else if fname == "dict" then
                    -- 2026-08-13: the dict CONSTRUCTOR, positional forms.
                    -- `dict()` is the empty mapping and `dict(d)` is
                    -- CPython's shallow COPY (a fresh object, never an
                    -- alias — the whole point of writing it). Pair-sequence
                    -- inputs use the same ordered builder as dict
                    -- comprehensions; immediate and heap-backed list, tuple,
                    -- bytes, string, and namedtuple sequences are admitted.
                    -- The keyword form `dict(k=v, …)` is in the kwargs arm.
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [] => allocDictRun st #[]
                     | [v] =>
                       (match v with
                        | .ref a =>
                          (match Heap.get? st.world.heap a with
                           | some (.dict entries _) => allocDictRun st entries
                           | some (.list xs) =>
                             Run.liftRes st (dictPairs st.world.heap 0 xs.toList) ⤳ fun st items =>
                             Run.liftRes st (dictBuild st.world.heap [] items) ⤳ fun st entries =>
                             allocDictRun st entries.toArray
                           | some (.generator ..) =>
                             Run.withLocals st.locals (drainIter m fuel st.world a) ⤳ fun st vals =>
                             Run.liftRes st (dictPairs st.world.heap 0 vals) ⤳ fun st items =>
                             Run.liftRes st (dictBuild st.world.heap [] items) ⤳ fun st entries =>
                             allocDictRun st entries.toArray
                           | some (.pyset _) =>
                             .exn st (.typeError "cannot convert dictionary update sequence element #0 to a sequence")
                           | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
                           | some (.instance _ _) =>
                             .exn st (.typeError "'object' object is not iterable")
                           | some (.cell _) => .unsupported cellInternal
                           | some (.closure ..) =>
                             .exn st (.typeError "'function' object is not iterable")
                           | Option.none => .unsupported danglingMsg)
                        | v =>
                          (match dictPairValues st.world.heap v with
                           | some values =>
                             Run.liftRes st (dictPairs st.world.heap 0 values) ⤳ fun st items =>
                             Run.liftRes st (dictBuild st.world.heap [] items) ⤳ fun st entries =>
                             allocDictRun st entries.toArray
                           | Option.none => .exn st (.typeError s!"'{v.typeName}' object is not iterable")))
                     | vs => .exn st (.typeError s!"dict expected at most 1 argument, got {vs.length}"))
                  else if fname == "range" then
                    -- pass 3: an IMMEDIATE `rangeV` value (pure — no
                    -- allocation); arity/type/step-zero faithfulness in
                    -- `rangeMake`
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    Run.liftRes st (rangeMake st.world.heap vs)
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
                          -- the START argument's OWN type, through the heap:
                          -- this said `'str'` unconditionally until
                          -- 2026-08-16, so `enumerate(['a','b'], [])` named
                          -- 'str' where CPython names 'list' (measured). Same
                          -- wrong-fact class as `range`'s, found by the same
                          -- census. `rest = []` never reaches here (`enumStart`
                          -- answers `some 0`), so a singleton is the only
                          -- type-error shape.
                          (match rest with
                           | [bad] =>
                             .exn st (.typeError
                               s!"'{RVal.typeNameH st.world.heap bad}' object cannot be interpreted as an integer")
                           | _ => .exn st (.typeError s!"enumerate expected at most 2 arguments, got {vs.length}"))
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
                    (match countArgsVal vs with
                     | Option.none =>
                       Run.liftRes st (countRefusal vs)
                     | some (start, step) =>
                       let g : Obj :=
                         .generator "<count>" [] [.countFromVal start step] .suspended
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
                  else if fname == "ascii" || fname == "hex" || fname == "oct" || fname == "bin" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [v] =>
                      Run.liftRes st
                        (if fname == "ascii" then asciiValH st.world.heap v
                         else if fname == "hex" then hexVal v
                         else if fname == "oct" then octVal v else binVal v)
                    | vs => .exn st (.typeError s!"{fname}() takes exactly one argument ({vs.length} given)")
                  else if fname == "format" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    match vs with
                    | [] => .exn st (.typeError "format expected at least 1 argument, got 0")
                    | [v] => Run.liftRes st (strOfValH st.world.heap v)
                    | [v, .str spec] =>
                      if spec == "" then Run.liftRes st (strOfValH st.world.heap v)
                      else Run.liftRes st (formatSpecH v spec)
                    | [_, spec] =>
                      .exn st (.typeError s!"format() argument 2 must be str, not {spec.typeName}")
                    | vs => .exn st (.typeError s!"format expected at most 2 arguments, got {vs.length}")
                  else if fname == "str" then
                    -- pass 8 widened at §rendering: immediates as before,
                    -- containers/refs through printOne (CPython's two-level
                    -- str rule); loud on unrenderables and the 2+-argument
                    -- decoding form
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    (match vs with
                     | [] => .ok st (.str "")
                     | [v] => Run.liftRes st (strOfValH st.world.heap v)
                     | _ => .unsupported "str() with encoding/errors arguments is outside the tier (bytes decoding is not guessed; docs/memory-model.md §the cast tier)")
                  else if fname == "repr" then
                    evalExprs m fuel st args.toList ⤳ fun st vs =>
                    Run.liftRes st (reprArgsH m st.world.heap vs)
                  else if fname == "input" then
                    -- stdin is a RUNNER-boundary effect (§effects) — loud,
                    -- never a fake NameError (the recorded pass-4 gap)
                    .unsupported "input() is outside the tier (stdin is a runner-boundary effect; docs/memory-model.md §effects)"
                  else if fname == "print" then
                    -- THE ONE EFFECT (2026-08-13): stdout is `World` data
                    -- (docs/memory-model.md §effects), so `print` is an
                    -- ordinary builtin here — reached only after locals,
                    -- the module globals, `findFunction`/`findClass`/
                    -- namedtuples, so every shadow still wins. It RETURNS
                    -- `None`, appends one chunk (the runner boundary
                    -- prints chunks as lines), and refuses loudly on a
                    -- value whose `repr` the tier does not model.
                    evalExprs m fuel st (complexPrintArgs args.toList) ⤳ fun st vs =>
                    (match strOfArgs st.world.heap vs with
                     | some line =>
                       .ok { st with world :=
                               { st.world with stdout := st.world.stdout ++ [line] } } .none
                     | Option.none =>
                       .unsupported "print() of a value the tier cannot render EXACTLY: a set (hash order), an instance/closure/generator (identity), or a structure deeper than the repr budget — docs/memory-model.md §effects")
                  else if isModuleDunder fname then
                    .unsupported s!"module attribute '{fname}' is bound by the import machinery, not by a statement — outside the G1 tier"
                  else
                    -- pass 3: the absent-arm LIVE view (prefix views
                    -- during init; the full table post-init) — a live
                    -- closure dispatches (the locals-arm shape,
                    -- `funsHeapFree`-guarded), anything else is the
                    -- faithful not-callable TypeError; only a genuine
                    -- miss may be the NameError
                    (match Env.lookup st.world.globals fname with
                     | some (.ref a) =>
                         evalExprs m fuel st args.toList ⤳ fun st vs =>
                         if funsHeapFree m.functions.toList && topLevelDefFree m then
                           .exn st (.typeError "'dict' object is not callable")
                         else
                           (match Heap.get? st.world.heap a with
                            | some (.cell _) => .unsupported cellInternal
                            | some (.closure nm ps ao lo _ ig bd cap) =>
                              Run.liftRes st (cellsFor st.world.heap st.locals cap) ⤳ fun st cap' =>
                              Run.withLocals st.locals
                                (callClosure m fuel st.world nm ps ao lo ig bd cap' vs.toArray)
                            | _ => .exn st (.typeError "'dict' object is not callable"))
                     | some v =>
                         evalExprs m fuel st args.toList ⤳ fun st _ =>
                         .exn st (.typeError s!"'{v.typeName}' object is not callable")
                     | Option.none =>
                       if isPyBuiltinName fname || isLoweredBuiltinName fname then
                         .unsupported (unmodelledBuiltinMsg fname)
                       else if (moduleGlobals m).2 then
                         .exn st (.nameError fname)
                       else
                         .unsupported s!"name '{fname}' may be bound by an out-of-tier module-level statement")
        | .attribute recv attr _ =>
          -- ===== THE TRACE CLOCK (pass 6, docs/memory-model.md §the
          -- trace clock): the EXACT call shape `time.time()` on the
          -- unshadowed benign-import clock name consumes the next
          -- reading of the world's trace; an empty trace is the LOUD
          -- underrun refusal (fuel-independent — a spec error in the
          -- run's INPUT, never a silent 0). Decided BEFORE the receiver
          -- evaluates (receiver evaluation is the poisoned refusal);
          -- everything failing `isClockCall` takes the paths below
          -- verbatim. `time.time(args…)` evaluates the args then raises
          -- CPython's exact arity `TypeError` without consuming the trace. =====
          if isClockCall m st recv attr then
            match args.toList with
            | [] =>
              match st.world.clock with
              | [] =>
                .unsupported "clock trace underrun: time.time() has no next reading (the trace is an INPUT — docs/memory-model.md §the trace clock)"
              | t :: ts =>
                .ok { st with world := { st.world with clock := ts } } (.int t)
            | _ :: _ =>
              .exn st (.typeError s!"time.time() takes no arguments ({args.size} given)")
          else
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
               | [.str sub, start] => Run.liftRes st (strIndexBounds sv sub start .none)
               | [.str sub, start, stop] => Run.liftRes st (strIndexBounds sv sub start stop)
               | [_v, _] => .exn st (.typeError s!"must be str, not {RVal.typeNameH st.world.heap _v}")
               | [_v, _, _] => .exn st (.typeError s!"must be str, not {RVal.typeNameH st.world.heap _v}")
               | vs =>
                 if vs.length ≤ 3 then
                   .unsupported "str.index() with start/end arguments are outside the tier (docs/memory-model.md §string semantics)"
                 else .exn st (.typeError s!"index expected at most 3 arguments, got {vs.length}")
             | .join =>
               evalExprs m fuel st args.toList ⤳ fun st vs =>
               match vs with
               | [v] => Run.liftRes st (strJoinH st.world.heap sv v)
               | vs => .exn st (.typeError s!"str.join() takes exactly one argument ({vs.length} given)")
             | .refuse msg => .unsupported msg)
          | .float fv =>
            if attr == "is_integer" then
              evalExprs m fuel st args.toList ⤳ fun st vs =>
              match vs with
              | [] => .ok st (.bool (floatIsInteger fv))
              | vs => .exn st (.typeError s!"float.is_integer() takes no arguments ({vs.length} given)")
            else
              .exn st .attributeError
          | r =>
            .exn st .attributeError
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
                  | some (.cell _) => .unsupported cellInternal
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
                      match findNamedTuple m fname with
                      | some nt =>
                        evalExprs m fuel st args.toList ⤳ fun st vs =>
                        evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st kvs =>
                        Run.liftRes st
                          (mergeNtKw nt.fields vs
                            ((kwargs.toList.map (·.1)).zip kvs)) ⤳ fun st full =>
                        .ok st (.ntuple nt.tname nt.fields full)
                      | Option.none => .unsupported "internal: namedtuple keyword plan lost its definition (report this)"
                    else if fname == "dict" then
                      -- 2026-08-13: `dict(k=v, …)` — the keyword form is
                      -- the ONLY way to build a mapping whose keys are
                      -- identifiers, and CPython keeps the call's own
                      -- order (duplicate keywords are a SyntaxError, so
                      -- no insert can collide). Positional arguments
                      -- alongside keywords stay loud.
                      if !args.isEmpty then
                        .unsupported "dict(<iterable>, k=v, …) mixing a positional argument with keywords is outside the tier"
                      else
                        evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st kvs =>
                        allocDictRun st
                          ((kwargs.toList.map (fun kv => RVal.str kv.1)).zip kvs).toArray
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
                    else if fname == "float" || fname == "len" || fname == "bool" then
                      -- CPython's float, len, and bool constructors accept no keyword
                      -- arguments. Evaluate both argument lists before their
                      -- faithful TypeErrors, preserving Python's order.
                      evalExprs m fuel st args.toList ⤳ fun st _ =>
                      evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st _ =>
                      .exn st (.typeError (if fname == "float" then
                        "float() takes no keyword arguments"
                      else if fname == "len" then
                        "len() takes no keyword arguments"
                      else "bool() takes no keyword arguments"))
                    else if fname == "divmod" then
                      -- CPython's divmod constructor accepts no keyword
                      -- arguments. Evaluate both argument lists before its
                      -- faithful TypeError, preserving Python's order.
                      evalExprs m fuel st args.toList ⤳ fun st _ =>
                      evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st _ =>
                      .exn st (.typeError "divmod() takes no keyword arguments")
                    else if fname == "repr" || fname == "abs" || fname == "ord" || fname == "chr" || fname == "next" || fname == "ascii" || fname == "tuple" || fname == "list" || fname == "range" || fname == "int" || fname == "hex" || fname == "oct" || fname == "bin" then
                      -- CPython's repr, abs, ord, chr, next, ascii, tuple, list, range, hex, oct, and bin constructors accept no keyword;
                      -- int accepts base; its shared binder checks arity and keywords.
                      -- Evaluate both argument lists before validating the call.
                      evalExprs m fuel st args.toList ⤳ fun st vs =>
                      evalExprs m fuel st (kwargs.toList.map (·.2)) ⤳ fun st kvs =>
                      if fname == "int" then
                        Run.liftRes st (intCastArgs vs ((kwargs.toList.map (·.1)).zip kvs))
                      else
                      .exn st (.typeError (if fname == "repr" then
                        "repr() takes no keyword arguments"
                      else if fname == "abs" then
                        "abs() takes no keyword arguments"
                      else if fname == "ord" then
                        "ord() takes no keyword arguments"
                      else if fname == "chr" then
                        "chr() takes no keyword arguments"
                      else if fname == "next" then
                        "next() takes no keyword arguments"
                      else if fname == "ascii" then
                        "ascii() takes no keyword arguments"
                      else if fname == "tuple" then
                        "tuple() takes no keyword arguments"
                      else if fname == "list" then
                        "list() takes no keyword arguments"
                      else if fname == "range" then
                        "range() takes no keyword arguments"
                      else if fname == "hex" then
                        "hex() takes no keyword arguments"
                      else if fname == "oct" then
                        "oct() takes no keyword arguments"
                      else "bin() takes no keyword arguments"))
                    else if isBuiltinName fname then
                      .unsupported s!"builtin '{fname}' with keyword arguments is outside the H6 tier"
                    else if isModuleDunder fname then
                      .unsupported s!"module attribute '{fname}' is bound by the import machinery, not by a statement — outside the G1 tier"
                    else
                      -- pass 3: a keyword call of a LIVE module binding
                      -- (init execution's view) stays loud — never a
                      -- fake NameError for a name CPython bound
                      (match Env.lookup st.world.globals fname with
                       | some _ =>
                         .unsupported s!"calling the live module binding '{fname}' with keyword arguments is outside the tier (docs/memory-model.md §module-init execution)"
                       | Option.none =>
                         if isPyBuiltinName fname || isLoweredBuiltinName fname then
                           .unsupported (unmodelledBuiltinMsg fname)
                         else if (moduleGlobals m).2 then
                           .exn st (.nameError fname)
                         else
                           .unsupported s!"name '{fname}' may be bound by an out-of-tier module-level statement"))
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
                 | .dictView _ =>
                   .unsupported "dict view method calls with keyword arguments are outside the tier"
                 | .dictClear =>
                   .unsupported "dict.clear() with keyword arguments is outside the tier (clear takes no keyword arguments in CPython)"
                 | .listAppend =>
                   .unsupported "list.append() with keyword arguments is outside the tier (append is positional-only in CPython)"
                 | .listPop =>
                   .unsupported "list.pop() with keyword arguments is outside the tier (pop is positional-only in CPython)"
                 | .listInsert =>
                   .unsupported "list.insert() with keyword arguments is outside the tier (insert is positional-only in CPython)"
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
        Run.liftRes st (checkBytesIndex m st.world.heap c i) ⤳ fun st _ =>
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
        .exn st .attributeError
    | .ifExp t b o _ =>
        -- CPython: the test first, then EXACTLY ONE branch (lazy)
        evalExpr m fuel st t ⤳ fun st tv =>
        Run.liftRes st (truthyH st.world.heap tv) ⤳ fun st cond =>
        if cond then evalExpr m fuel st b else evalExpr m fuel st o
    | .slice v l u stp _ =>
        -- CPython order — receiver, slice components, then subscript
        -- application; heap-list receivers allocate their copy here.
        evalExpr m fuel st v ⤳ fun st cv =>
        evalExpr m fuel st l ⤳ fun st lv =>
        evalExpr m fuel st u ⤳ fun st uv =>
        evalExpr m fuel st stp ⤳ fun st sv =>
        Run.liftRes st (sliceValH st.world.heap cv lv uv sv) ⤳ fun st (h', r) =>
          .ok { st with world := { st.world with heap := h' } } r
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
    | .dictView _ =>
      .unsupported "dictionary view allocation is outside the proof tier"
    | .dictClear =>
      -- pass 5: the dict MUTATOR — entries := #[], shape version
      -- bumped (a live items()-iteration must see the change), `None`
      -- returned; wrong arity the faithful TypeError.
      evalExprs m fuel st args ⤳ fun st vs =>
      match vs with
      | [] =>
        (match Heap.get? st.world.heap a with
         | some (.dict _ ver) =>
           (match Heap.update st.world.heap a (.dict #[] (ver + 1)) with
            | some h' => .ok { st with world := { st.world with heap := h' } } .none
            | Option.none => .unsupported danglingMsg)
         | _ => .unsupported danglingMsg)
      | vs => .exn st (.typeError s!"clear() takes no arguments ({vs.length} given)")
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
    | .listInsert =>
      -- the §2.5 residue: clamping index (never IndexError), `None`
      -- returned; the coercion TypeError decided AFTER the arguments
      -- evaluate (pop's rule), the arity TypeError verbatim
      evalExprs m fuel st args ⤳ fun st vs =>
      match vs with
      | [i, v] =>
        (match asInt i with
         | some n =>
           Run.liftRes st (heapInsert st.world.heap a n v) ⤳ fun st h' =>
           .ok { st with world := { st.world with heap := h' } } .none
         | Option.none =>
           .exn st (.typeError s!"'{i.typeName}' object cannot be interpreted as an integer"))
      | vs => .exn st (.typeError s!"insert expected 2 arguments, got {vs.length}")
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
        Run.liftRes st (checkBytesCompare m st.world.heap op lhs rhs) ⤳ fun st _ =>
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
            Run.liftRes st (heapAttrStoreClass m st.world.heap a attr v) ⤳ fun st h' =>
            .ok { st with world := { st.world with heap := h' } } .next
          | _ => .exn st .attributeError
      | [.tuple elts sp] =>
          -- pass 4 (docs/memory-model.md §bound() end-to-end): a tuple
          -- target with ATTRIBUTE elements threads the heap store by
          -- store, CPython's left-to-right order (`self.a, self.b = …`);
          -- an all-NAME tuple keeps the pure `assignToH` path verbatim.
          if (targetNames elts).isSome then
            evalExpr m fuel st value ⤳ fun st v =>
            Run.liftRes st (assignToH st.world.heap st.locals (.tuple elts sp) v) ⤳ fun st env' =>
            .ok { st with locals := env' } .next
          else
            evalExpr m fuel st value ⤳ fun st v =>
            Run.liftRes st (unpackSeq st.world.heap elts.size v) ⤳ fun st xs =>
            Run.liftRes st (unpackStoreHM m st.world.heap st.locals elts.toList xs) ⤳ fun st he =>
            match he with
            | (h', env') =>
              .ok { st with world := { st.world with heap := h' },
                            locals := env' } .next
      | [t] =>
          -- CPython order: the value is evaluated before the store. H2:
          -- `assignToH` — unpacking from a heap list reads the heap.
          evalExpr m fuel st value ⤳ fun st v =>
          Run.liftRes st (assignToH st.world.heap st.locals t v) ⤳ fun st env' =>
          .ok { st with locals := env' } .next
      | _ => .unsupported "chained assignment (multiple targets) is outside the v0 tier"
    | .unpackAssign before star after value _ =>
      evalExpr m fuel st value ⤳ fun st v =>
      Run.liftRes st (unpackSeqStar st.world.heap before.size after.size v) ⤳
        fun st parts =>
          let (pre, mid, suf) := parts
          let a := st.world.heap.size
          let h' := st.world.heap.push (.list mid.toArray)
          let names := before.toList ++ [star] ++ after.toList
          let vals := pre ++ [.ref a] ++ suf
          .ok { st with world := { st.world with heap := h' },
                        locals := bindAll st.locals names vals } .next
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
      | .attribute recvE attr _ =>
        -- pass 4 (docs/memory-model.md §bound() end-to-end):
        -- `self.nodes += 1`. CPython order: receiver, attribute LOAD
        -- (an AttributeError fires before the value evaluates), value,
        -- binop, attribute STORE. Only IMMEDIATE old values are in tier
        -- — a heap-valued attribute's `+=` mutates in place through an
        -- alias and a boundary-list value would silently rebind: loud.
        evalExpr m fuel st recvE ⤳ fun st r =>
        (match r with
         | .ref a =>
           attrReadResult m st a attr ⤳ fun st old =>
           (match old with
            | .listV _ =>
                .unsupported "augmented assignment to a list-valued attribute ('+=' mutates in place, visible through aliases) is outside the tier"
            | .ref a2 =>
                evalExpr m fuel st value ⤳ fun st v =>
                Run.liftRes st (heapListAugAssign st.world.heap a2 op v) ⤳ fun st h' =>
                .ok { st with world := { st.world with heap := h' } } .next
            | old =>
                evalExpr m fuel st value ⤳ fun st v =>
                Run.liftRes st (evalBinOp op old v) ⤳ fun st res =>
                Run.liftRes st (heapAttrStoreClass m st.world.heap a attr res) ⤳ fun st h' =>
                .ok { st with world := { st.world with heap := h' } } .next)
         | _ => .exn st .attributeError)
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
        | .bytes xs => execFor m fuel st target (bytesIntVals xs) body.toList
        -- pass 3: `for` over a range MATERIALIZES (immutable — the
        -- snapshot IS the live semantics, and re-iteration is exact
        -- because each `for` materializes afresh)
        | .rangeV lo hi step =>
          Run.liftRes st (rangeVals lo.toInt hi.toInt step.toInt) ⤳ fun st xs =>
          execFor m fuel st target xs body.toList
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
    | .yieldFromStmt .. =>
        -- pass 5: the admitted shape was inlined at ingestion; an
        -- un-lowered `yield from` refuses with its reason, never a
        -- silent skip (docs/memory-model.md §yield from).
        .unsupported "un-lowered 'yield from' (the iterable is not an admitted genexp, or the genexp's target occurs elsewhere in the body) — outside the tier (docs/memory-model.md §yield from)"
    | .defStmt name params argsOk localsOk hasGlobal isGenerator body captures _ =>
      -- H7 (docs/memory-model.md §nested defs and closures): SNAPSHOT
      -- the captures from the current frame, ALLOCATE the closure
      -- object, bind the name. Under the extractor's never-rebound
      -- admission the snapshot IS CPython's cell.
      -- H7 cells: allocate/reuse this frame's cells FIRST, so the
      -- snapshot picks up the directory entries rather than values.
      let st := allocCells st captures.toList
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
    | .raiseStmt exc cause _ =>
      -- exceptions tier (docs/memory-model.md §exceptions): the admitted
      -- shape is `raise N` of an admitted exception class, resolved to
      -- its class IDENTITY — everything else refuses loudly. The name
      -- must resolve UNAMBIGUOUSLY to the class: any local/global/def
      -- shadow refuses (CPython would raise the shadow's value).
      (match cause with
       | some _ =>
         .unsupported "dynamic 'raise … from …' (exception chaining) is outside the tier (docs/memory-model.md §exceptions)"
       | Option.none =>
         match exc with
         | Option.none =>
           .unsupported "bare 'raise' (re-raise of the active exception) is outside the tier (docs/memory-model.md §exceptions)"
         | some (.name id _) =>
           if hasUnboundLocal st.locals id then
             .exn st (.unboundLocalError id)
           else
             match Env.lookup st.locals id with
             | some (.ref _) =>
               .unsupported s!"'raise {id}': a heap-backed exception value is outside the tier (docs/memory-model.md §exceptions)"
             | some _ =>
               .exn st (.typeError "exceptions must derive from BaseException")
             | Option.none =>
               if (lookupG (moduleGlobals m).1 id).isSome
                   || (Env.lookup st.world.globals id).isSome
                   || (findFunction m id).isSome then
                 .unsupported s!"'raise {id}': the name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
               else
                 (match findClass m id with
                  | some (ci, c) =>
                    if c.isExc then .exn st (.user ci c.name)
                    else
                      .unsupported s!"'raise {id}': only an admitted exception class (`class N(Exception): pass` or a measured direct builtin ancestor) can be raised — outside the tier (docs/memory-model.md §exceptions)"
                  | Option.none =>
                    if (findNamedTuple m id).isSome then
                      .exn st (.typeError "exceptions must derive from BaseException")
                    else if admittedBuiltinRaise.contains id then .exn st (.builtinException id)
                    else
                      .unsupported s!"'raise {id}': only an admitted exception class name can be raised — outside the tier (docs/memory-model.md §exceptions)")
         | some (.call (.name id _) args kwargs callUnsupported _) =>
           -- The measured proof-facing payload form is one positional
           -- string literal passed to an admitted exception class. Resolve
           -- the class before inspecting the literal, matching Python's
           -- callee-first order and the static shadow guard above. The
           -- monadic runner admits the wider expression form; keeping this
           -- pure literal slice here preserves the fuel-free proof geometry.
           if !kwargs.isEmpty || callUnsupported.isSome then
             .unsupported "'raise N(…)': keyword/starred constructor arguments are outside the tier (docs/memory-model.md §exceptions)"
           else if (Env.lookup st.locals id).isSome
               || (lookupG (moduleGlobals m).1 id).isSome
               || (Env.lookup st.world.globals id).isSome
               || (findFunction m id).isSome then
             .unsupported s!"'raise {id}': the name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
           else if (findClass m id).isSome then
             match findClass m id with
             | some (ci, c) =>
               if c.isExc then
                 match args.toList with
                 | [(.constant (.str msg) _)] =>
                   .exn st (.userMessage ci c.name msg)
                 | [_] =>
                   .unsupported s!"'raise {id}(…)': the measured constructor form requires one string argument — outside the tier (docs/memory-model.md §exceptions)"
                 | _ =>
                   .unsupported s!"'raise {id}(…)': the measured constructor form requires exactly one positional string argument — outside the tier (docs/memory-model.md §exceptions)"
               else
                 .unsupported s!"'raise {id}(…)': only an admitted exception class (`class N(Exception): pass` or a measured direct builtin ancestor) can be raised — outside the tier (docs/memory-model.md §exceptions)"
             | none =>
               .unsupported s!"'raise {id}(…)': user exception and namedtuple constructors with payloads are outside the tier (docs/memory-model.md §exceptions)"
           else if (findNamedTuple m id).isSome then
             .unsupported s!"'raise {id}(…)': user exception and namedtuple constructors with payloads are outside the tier (docs/memory-model.md §exceptions)"
           else if !isPyBuiltinName id then
             -- The callee name is resolved before constructor arguments.  An
             -- unknown name therefore raises the faithful NameError even
             -- when the constructor shape itself is outside the tier.
             .exn st (.nameError id)
           else
             match args.toList with
             | [(.constant (.str msg) _)] =>
               match builtinExcWithMessage id msg with
               | some e => .exn st e
               | none =>
                 if admittedBuiltinRaise.contains id then
                   .unsupported s!"'raise {id}(…)': only the measured one-string builtin exception constructors are admitted — outside the tier (docs/memory-model.md §exceptions)"
                 else
                   .unsupported s!"'raise {id}': only an admitted exception class name can be raised — outside the tier (docs/memory-model.md §exceptions)"
             | [_] =>
               .unsupported s!"'raise {id}(…)': the measured constructor form requires one string argument — outside the tier (docs/memory-model.md §exceptions)"
             | _ =>
               .unsupported s!"'raise {id}(…)': the measured constructor form requires exactly one positional string argument — outside the tier (docs/memory-model.md §exceptions)"
         | some _ =>
           .unsupported "'raise <expression>' (anything but an admitted exception class name) is outside the tier (docs/memory-model.md §exceptions)")
    | .assertStmt test msg _ =>
      -- the tail batch (docs/memory-model.md §the assert statement):
      -- CPython's `if not test: raise AssertionError(msg)`. The model
      -- runs without `-O`, so the test always evaluates; the MESSAGE is
      -- evaluated only on the failing path, which is CPython's laziness
      -- and is observable whenever it has an effect. The rendering is
      -- `printOne` — `print`'s own one-argument `str()` — so the two
      -- agree by construction and the unrenderable cases (a set or an
      -- instance) refuse LOUDLY here too.
      (evalExpr m fuel st test ⤳ fun st t =>
       Run.liftRes st (truthyH st.world.heap t) ⤳ fun st b =>
       if b then .ok st .next
       else
         match msg with
         | Option.none => .exn st (.assertionError Option.none)
         | some e =>
           evalExpr m fuel st e ⤳ fun st v =>
           match printOne st.world.heap v with
           | some rendered => .exn st (.assertionError (some rendered))
           | Option.none =>
             .unsupported "assert message: the tier cannot render this value EXACTLY — a set (hash order), an instance/closure/generator (identity), or a structure deeper than the repr budget — docs/memory-model.md §the assert statement")
    | .delStmt names _ =>
      -- the tail batch (docs/memory-model.md §the del statement): the
      -- FUNCTION-scope arm. `delNames` threads the locals left to right
      -- (the partial effect: earlier removals are already applied when a
      -- later target misses); a hit only rewrites `st.locals`, which is
      -- not a `World` field, so `worldInv` holds by construction. The
      -- miss case is CPython's `UnboundLocalError`: the static-local marker
      -- installed at frame entry covers a module-global target, a
      -- never-bound name, and a second deletion. (Module scope never reaches this arm from the script
      -- surface — `execScriptOne` owns it — except through a delegated
      -- `while … else`, where locals ARE the module globals and the same
      -- hit/miss split is exact/loud.)
      (match delNames st.locals names.toList with
       | (env, Option.none) => .ok { st with locals := env } .next
       | (_, some n) => .exn st (.unboundLocalError n))
    | .withStmt items body withUnsupported _ =>
      match withUnsupported, items.toList with
      | some reason, _ =>
          .unsupported s!"with statement uses unsupported features ({reason}) — outside the tier"
      | none, [item] =>
        match item.context with
        | .call (.name fname _) args kwargs callUnsupported _ =>
          if !kwargs.isEmpty || callUnsupported.isSome then
            .unsupported "with context calls with keywords or starred arguments are outside the tier"
          else
            match findContextClass m fname with
            | Option.none =>
                .unsupported "with requires an admitted class with __enter__ and __exit__"
            | some (ci, _) =>
              let exitName := fname ++ ".__exit__"
              let exitArgsFree :=
                (findFunction m exitName).map FunctionDefn.withExitExceptionArgsFree == some true
              let exitTypeTest :=
                (findFunction m exitName).map FunctionDefn.withExitExceptionTypeTest == some true
              if !exitArgsFree && !exitTypeTest then
                .unsupported "with body exceptions require __exit__ not to inspect exception arguments (full exception triples are outside the tier)"
              else
                evalExprs m fuel st args.toList ⤳ fun st vs =>
                let enterName := fname ++ ".__enter__"
                let a := st.world.heap.size
                let st' := { st with world :=
                  { st.world with heap := st.world.heap.push (.instance ci (instanceAttrs m ci)) } }
                match vs with
                | [] =>
                  Run.withLocals st'.locals
                      (callIn m fuel st'.world enterName #[.ref a]) ⤳ fun stEnter entered =>
                    match item.target with
                      | some target =>
                          Run.liftRes stEnter
                            (assignToH stEnter.world.heap stEnter.locals target entered) ⤳
                            fun stBody env' =>
                              Run.bindE
                                (execStmts m fuel { stBody with locals := env' } body.toList)
                                (fun stAfter flow =>
                                  match flow with
                                  | .next | .ret _ | .brk | .cont =>
                                      Run.withLocals stAfter.locals
                                        (callIn m fuel stAfter.world exitName
                                          #[.ref a, .none, .none, .none]) ⤳ fun stExit _ =>
                                      .ok stExit flow)
                                (fun stBody e =>
                                  Run.withLocals stBody.locals
                                    (callIn m fuel stBody.world exitName
                                      (withExitArgs exitTypeTest a)) ⤳ fun stExit exitValue =>
                                    Run.liftRes stExit
                                      (truthyH stExit.world.heap exitValue) ⤳ fun stExit suppresses =>
                                      if suppresses then .ok stExit .next else .exn stExit e)
                      | none =>
                          Run.bindE
                            (execStmts m fuel stEnter body.toList)
                            (fun stAfter flow =>
                              match flow with
                              | .next | .ret _ | .brk | .cont =>
                                  Run.withLocals stAfter.locals
                                    (callIn m fuel stAfter.world exitName
                                      #[.ref a, .none, .none, .none]) ⤳ fun stExit _ =>
                                  .ok stExit flow)
                            (fun stBody e =>
                              Run.withLocals stBody.locals
                                (callIn m fuel stBody.world exitName
                                  (withExitArgs exitTypeTest a)) ⤳ fun stExit exitValue =>
                                Run.liftRes stExit
                                  (truthyH stExit.world.heap exitValue) ⤳ fun stExit suppresses =>
                                  if suppresses then .ok stExit .next else .exn stExit e)
                | _ => .exn st' (.typeError s!"{fname}() takes no arguments")
        | _ =>
          .unsupported "with context must be a direct class constructor call"
      | _, _ => .unsupported "multiple context-manager items are outside the tier"
    | .tryStmt body excName handler tryUnsupported _ =>
      -- exceptions tier: the v0 single-handler shape on the retained-state
      -- covenant — run the body; `.ok` skips the handler; a MATCHING
      -- `.user` exn runs the handler FROM THE RETAINED STATE (no
      -- rollback — CPython's unwinding keeps every mutation up to the
      -- raise); any other exn propagates. The handler class resolves
      -- STATICALLY-FIRST (recorded as-built delta): a handler naming
      -- anything but an admitted exception class refuses before the body
      -- runs — loud, never wrong.
      (match tryUnsupported with
       | some reason =>
         .unsupported s!"try/except uses unsupported features ({reason}) — outside the tier (docs/memory-model.md §exceptions)"
       | Option.none =>
         if excName.isEmpty then
           match execStmts m fuel st body.toList with
           | .ok st' flow => .ok st' flow
           | .exn st' _ => execStmts m fuel st' handler.toList
           | .timeout => .timeout
           | .unsupported msg => .unsupported msg
         else if excHandlerTuple excName then
           let names := excHandlerNames excName
           if names.any (fun name =>
               (Env.lookup st.locals name).isSome
                 || (lookupG (moduleGlobals m).1 name).isSome
                 || (Env.lookup st.world.globals name).isSome
                 || (findFunction m name).isSome) then
             .unsupported s!"'except {excName}:': a tuple handler name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
           else if names.any (fun name => !excHandlerAdmitted m name) then
             .unsupported s!"'except {excName}:': every tuple handler name must be an admitted exception class — outside the tier (docs/memory-model.md §exceptions)"
           else
             match execStmts m fuel st body.toList with
             | .ok st' flow => .ok st' flow
             | .exn st' e =>
                 if names.any (fun name => excHandlerMatches m name e) then
                   execStmts m fuel st' handler.toList
                 else .exn st' e
             | .timeout => .timeout
             | .unsupported msg => .unsupported msg
         else if (Env.lookup st.locals excName).isSome
             || (lookupG (moduleGlobals m).1 excName).isSome
             || (Env.lookup st.world.globals excName).isSome
             || (findFunction m excName).isSome then
           .unsupported s!"'except {excName}:': the name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
         else
           match findClass m excName with
           | Option.none =>
             -- Pass 0 (docs/memory-model.md §import forms): the pinned
             -- two-name table — the recorded first extension of
             -- builtin-name matching, at minimum width. The body runs;
             -- a `.importError` is caught (both pinned names, no class
             -- identity — every import error matches), anything else
             -- propagates; the same retained-state covenant as the
             -- user-class arm below. Consulted only after `findClass`
             -- missed, so a user class named `ImportError` still wins.
             if (findNamedTuple m excName).isSome then
               Run.bindE (execStmts m fuel st body.toList)
                 (fun st' flow => .ok st' flow)
                 (fun st' _ => .exn st' (.typeError
                   "catching classes that do not inherit from BaseException is not allowed"))
             else if importErrorHandlerMatch excName then
               match execStmts m fuel st body.toList with
               | .ok st' flow => .ok st' flow
               | .exn st' e =>
                 (match e with
                  | .importError _ => execStmts m fuel st' handler.toList
                  | e => .exn st' e)
               | .timeout => .timeout
               | .unsupported msg => .unsupported msg
             else if admittedBuiltinExc.contains excName then
               match execStmts m fuel st body.toList with
               | .ok st' flow => .ok st' flow
               | .exn st' e =>
                   if builtinExcCatches excName e || userExcCatches m excName e then execStmts m fuel st' handler.toList
                 else .exn st' e
               | .timeout => .timeout
               | .unsupported msg => .unsupported msg
             else if refusedAncestorExc.contains excName then
               .unsupported s!"'except {excName}:': '{excName}' is a CPython ANCESTOR class the tier has not measured — admitting it would claim a catch set this model has never enumerated, so it is refused BY NAME rather than derived from a hierarchy (docs/memory-model.md §exceptions)"
             else
               .unsupported s!"'except {excName}:': matchable classes are an admitted user class (`class N(Exception): pass` or a measured direct builtin ancestor), the pinned import-error names, or one of `admittedBuiltinExc` — '{excName}' is none of those (docs/memory-model.md §exceptions)"
           | some (ci, c) =>
             if !c.isExc then
               .unsupported s!"'except {excName}:': class '{excName}' is not an admitted exception class — outside the tier (docs/memory-model.md §exceptions)"
             else
               match execStmts m fuel st body.toList with
               | .ok st' flow => .ok st' flow
               | .exn st' e =>
                 (match e with
                  | .user cid _ | .userMessage cid _ _ =>
                    if cid == ci then execStmts m fuel st' handler.toList
                    else .exn st' e
                  | e => .exn st' e)
               | .timeout => .timeout
               | .unsupported msg => .unsupported msg)
    | .importFrom mod _ _ _ =>
      -- Pass 0 (docs/memory-model.md §import forms): the importable
      -- universe is EMPTY — every admitted from-import RAISES,
      -- fuel-free, state unchanged, never `.ok`. The EXTRACTOR's
      -- admission is what makes the raise faithful: either the module
      -- is absent from the pinned platform inventory (the raise is
      -- CPython's own behavior, `ModuleNotFoundError` at the boundary),
      -- or the statement sits in import-guard position and the raise is
      -- caught by construction — the fallback branch then runs from the
      -- retained state under the accelerator-equivalence obligation
      -- (docs/c-intrinsics-proposal.md §2.5, differentially tested).
      -- Star changes nothing here: the raise fires before any binding.
      .exn st (.importError mod)
    | .pass _ => .ok st .next
    | .brk _ => .ok st .brk
    | .cont _ => .ok st .cont
    | .unsupported "AnnAssign:no-value" text _ =>
      match annNoValueName text with
      | some id =>
          .ok { st with locals := Env.set st.locals (unboundLocalMarker id) RVal.none } .next
      | Option.none => .unsupported "unsupported statement 'AnnAssign:no-value'"
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
    | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
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
    | some (.cell _) => .unsupported cellInternal
    | some (.closure ..) =>
        .unsupported "internal: a list cursor over a function object (report this)"
    | some (.pyset _) =>
        .unsupported "internal: a list cursor over a set (report this)"
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
        .exn w (.typeError (arityErrorMsg fname (paramArity f.params) args.size))
      else if f.isGenerator then
        -- H4 CREATION: calling a generator function runs NO code. It
        -- allocates the suspended frame — arguments bound into its
        -- locals, the whole body as the initial continuation — and
        -- returns the object. Every effect in the body (sunfish's
        -- TT writes) therefore happens only as a consumer steps it,
        -- which is exactly the laziness the search depends on.
        let g : Obj :=
          .generator fname
            (markUnboundLocals f.body.toList (mkCallEnv f.params args))
            [.block f.body.toList] .created
        .ok { w with heap := w.heap.push g } (.ref w.heap.size)
      else
        Run.toWorld <|
          execStmts m fuel
            ⟨w, markUnboundLocals f.body.toList (mkCallEnv f.params args)⟩
            f.body.toList ⤳ fun st flow =>
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
      | .failed error => .exn w error
      | .running =>
        .exn w (.valueError "generator already executing")
      | _ =>
        match Heap.update w.heap a (.generator qname locals cont .running) with
        | Option.none => .unsupported danglingMsg
        | some h₁ =>
          Run.toWorld <|
            Run.bindE (execGen m fuel ⟨{ w with heap := h₁ }, locals⟩ cont)
              (fun st r =>
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
                     .ok { st with world := { st.world with heap := h₂ } } Option.none))
              (fun st e =>
                -- exceptions tier (docs/memory-model.md §exceptions): an
                -- exception propagating out of a resume CLOSES the
                -- generator — CPython marks the frame finished, every
                -- later `next()` is exhaustion — never `suspended` (a
                -- resumable post-exception frame is unfaithful) and never
                -- stuck `running` (a permanent fake ValueError; the
                -- gen_lab status pin, flipped by this arm).
                match Heap.update st.world.heap a
                    (.generator qname st.locals [] .closed) with
                | Option.none => .unsupported danglingMsg
                | some h₂ =>
                  .exn { st with world := { st.world with heap := h₂ } } (generatorEscape e))
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
            | .bytes xs =>
                execGen m fuel st (.forSeq target (bytesIntVals xs) body :: .block ss :: k')
            | .rangeV lo hi step =>
                Run.liftRes st (rangeVals lo.toInt hi.toInt step.toInt) ⤳ fun st xs =>
                execGen m fuel st (.forSeq target xs body :: .block ss :: k')
            | .ref ad =>
              (match Heap.get? st.world.heap ad with
               | some (.list _) =>
                   execGen m fuel st (.forList target ad 0 body :: .block ss :: k')
               | some (.generator ..) =>
                   execGen m fuel st (.forGen target ad body :: .block ss :: k')
               | some (.dict _ _) =>
                   .unsupported "'for' over a dict is outside the tier (live dict iteration is deliberately NOT in the inventory; docs/memory-model.md)"
               | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
               | some (.instance _ _) =>
                   .exn st (.typeError "'object' object is not iterable")
               | some (.cell _) => .unsupported cellInternal
               | some (.closure ..) =>
                   .exn st (.typeError "'function' object is not iterable")
               | some (.pyset _) =>
                   .unsupported "'for' over a set is outside the tier (iteration is hash order — never guessed; docs/memory-model.md)"
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
       | some (.dictView ..) => .unsupported "dictionary view operation is outside the tier"
       | some (.instance _ _) => .exn st (.typeError "'object' object is not iterable")
       | some (.generator ..) =>
           .unsupported "internal: a list cursor over a generator object (report this)"
       | some (.cell _) => .unsupported cellInternal
       | some (.closure ..) =>
           .unsupported "internal: a list cursor over a function object (report this)"
       | some (.pyset _) =>
           .unsupported "internal: a list cursor over a set (report this)"
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
    | .enumDict .. :: _ =>
      -- §3c-i-c, and the ONE honest difference from the `forDict` arm below:
      -- this interpreter DOES construct this frame, because `enumFrame` is
      -- shared and decides for both presentations. So the refusal is on the
      -- STEP, not the construction, and `e = enumerate(d)` answers an object
      -- here exactly as CPython does — a capability OPENING, witnessed by
      -- `dict.enumerate-escapes` rather than suppressed. Stepping is the
      -- monadic rebuild's (docs/backlog/python-completeness.md
      -- 2026-08-23-pycomplete-13, ruling (c)).
      .unsupported "stepping an enumerate() over a dict is outside this interpreter's tier — the live cursor is the monadic rebuild's (docs/memory-model.md §dict iteration)"
    | .iterDict .. :: _ =>
      -- §iter, and it is the `forDict` arrangement rather than `enumDict`'s
      -- one above: this interpreter has NO `iter` arm at all, so `iter(d)`
      -- refuses at name resolution and the frame is unreachable here. The arm
      -- exists to compile and to refuse, and gains no consumers — which is
      -- also why the inch owes no trunk-side capability delta to witness.
      .unsupported "stepping an iter() over a dict is outside this interpreter's tier — the live cursor is the monadic rebuild's (docs/memory-model.md §dict iteration)"
    | .iterList .. :: _ =>
      -- §iterList: same arrangement as `iterDict` directly above — the trunk
      -- has no `iter` arm, so it never builds this frame either.
      .unsupported "stepping an iter() over a list is outside this interpreter's tier — the live cursor is the monadic rebuild's (docs/memory-model.md §dict iteration)"
    | .iterBytes .. :: _ =>
      .unsupported "stepping an iter() over bytes is outside this interpreter's tier — the monadic rebuild owns the bytes cursor"
    | .forDict .. :: _ =>
      -- THE LEGACY INTERPRETER'S CONTRACT under no-backwards-compat: this
      -- interpreter never CONSTRUCTS a `forDict` frame (only
      -- `LeanModels/Python/Monadic/` does), so the arm exists to compile and
      -- to refuse, and gains no consumers. The live dict cursor is inch 3a
      -- and it opens on the monadic definition only.
      .unsupported "'for' over a dict is outside this interpreter's tier — the live cursor is the monadic rebuild's (docs/memory-model.md §dict iteration)"
    | .countFrom cur step :: k' =>
      -- never exhausts: `count` is the infinite ray of sunfish's move
      -- generator, and a consumer's `break` is what ends it
      .ok st (some (.int cur, .countFrom (cur + step) step :: k'))
    | .countFromVal cur step :: k' =>
      match evalBinOp .add cur step with
      | .ok next => .ok st (some (cur, .countFromVal next step :: k'))
      | .exn error => .exn st error
      | .timeout => .timeout
      | .unsupported message => .unsupported message
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
      .exn w (.typeError (arityErrorMsg name (paramArity params) args.size))
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

/-! ## Module-init EXECUTION (pass 3, docs/memory-model.md §module-init
execution)

The live pipeline behind `initWorld`: one ordered walk over the top
level. Each statement first takes the PURE FOLD STEP on the live state
(`initFoldStep` — the `globalsStep` in-tier arms, so a statically-valued
binding is live-equal by construction); a fold-refused statement gets
the EXEC ATTEMPT through the interpreter under the per-statement PREFIX
VIEW (`topLevel := done` — name resolution must be SEQUENTIAL: the full
static table would let an executed statement read a FUTURE binding);
a failed attempt ROLLS BACK to the pre-statement state and POISONS the
statement's dirty names in the live accumulator too (`globalsDirty` —
without the live marker, the poisoned-arm consult would resurface a
STALE pre-statement value). The dict-items `for` gets the one control
shell `execStmt` cannot express, with CPython's per-step SIZE check.
Executed statements run at the fixed `initExecFuel` — like
`globalFuel`, independent of every caller's fuel. -/

/-- Fixed fuel for executed init statements. -/
def initExecFuel : Nat := 65536

/-- Names an executed init statement may NOT bind: `def`/`class`/namedtuple
names. Modeled builtins remain ordinary module globals: CPython lets a module
rebind them, and name/callee resolution consults the live module frame before
falling back to the builtin arm. -/
def initBindable (m : Module) (n : String) : Bool :=
  ((findFunction m n).isNone || m.aliases.contains n)
    && (findClass m n).isNone && (findNamedTuple m n).isNone

/-- Flush an executed statement's locals into the live accumulator
(CPython: top-level bindings are globals). `none` = a name failed
`initBindable`. -/
def flushInitLocals (m : Module) (acc : GlobalsAcc) : REnv → Option GlobalsAcc
  | [] => some acc
  | (n, v) :: rest =>
    if initBindable m n then flushInitLocals m ((n, some v) :: acc) rest
    else Option.none

/-- The live fold step: `globalsStep`'s in-tier arms with an explicit
refusal signal (`none` = the pipeline attempts execution). Kept in
lockstep with `globalsStep` — a statically-VALUED binding must be
live-equal, which is what makes static-first resolution sound. -/
def initFoldStep (h : Heap) (acc : GlobalsAcc) (s : Stmt) :
    Option (Heap × GlobalsAcc) :=
  match s with
  | .assign tgts rhs _ =>
    (match tgts.toList with
     | [.name id _] =>
       (match evalGlobalExpr h (resolvedG acc) globalFuel rhs with
        | .ok (h', v) => some (h', (id, some v) :: acc)
        | _ => Option.none)
     | [.tuple es _] =>
       (match targetNamesG es.toList with
        | some ids =>
          (match evalGlobalExpr h (resolvedG acc) globalFuel rhs with
           | .ok (h', .tuple vs) =>
             if ids.length == vs.size then
               some (h', (ids.zip (vs.toList.map some)).reverse ++ acc)
             else Option.none
           | .ok (h', .listV vs) =>
             if ids.length == vs.size then
               some (h', (ids.zip (vs.toList.map some)).reverse ++ acc)
             else Option.none
           | _ => Option.none)
        | Option.none => Option.none)
     | _ => Option.none)
  | .pass _ => some (h, acc)
  -- See `globalsStep`: class creation is a script-mode effect, while the
  -- closed function boundary keeps its module-init world unchanged.
  | .unsupported "ClassDef" _ _ => some (h, acc)
  | .exprStmt (.constant ..) _ => some (h, acc)
  | _ => Option.none

/-- Execute the body statements of the items shell ONE AT A TIME, each
in a fresh empty-locals frame over the current live globals, FLUSHING
after each — inner frames (genexp bodies, lambda calls) resolve the
loop's own bindings through the live view, which a whole-body locals
frame would hide from them. -/
def initBodyStmts (mV : Module) (fuel : Nat) (h : Heap) (acc : GlobalsAcc) :
    List Stmt → Run (Heap × GlobalsAcc) RFlow
  | [] => .ok (h, acc) .next
  | s :: rest =>
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      match execStmt mV fuel ⟨⟨h, resolvedG acc, [], []⟩, []⟩ s with
      | .ok st flow =>
        (match flushInitLocals mV acc st.locals with
         | some acc' =>
           (match flow with
            | .next => initBodyStmts mV fuel st.world.heap acc' rest
            | flow => .ok (st.world.heap, acc') flow)
         | Option.none =>
           .unsupported "an executed init statement rebinds a builtin/def/class/namedtuple name — outside the tier (docs/memory-model.md §module-init execution)")
      | .exn st e => .exn (st.world.heap, acc) e
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

/-- The init `for target in d.items():` shell — CPython's dict_items
iterator: the LIVE entries re-read per step, a SIZE change the faithful
`RuntimeError` (value updates visible mid-iteration; H1 acceptance
row 10). `n` is the size at iterator creation. -/
def initItemsLoop (mV : Module) (fuel : Nat) (h : Heap) (acc : GlobalsAcc)
    (a : Addr) (n : Nat) (i : Nat) (target : Expr) (body : List Stmt) :
    Run (Heap × GlobalsAcc) Unit :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match Heap.get? h a with
    | some (.dict entries _) =>
      if entries.size ≠ n then
        .exn (h, acc) (.runtimeError "dictionary changed size during iteration")
      else if hlt : i < entries.size then
        match assignToH h [] target (.tuple #[entries[i].1, entries[i].2]) with
        | .ok env0 =>
          (match flushInitLocals mV acc env0 with
           | some acc1 =>
             (match initBodyStmts mV fuel h acc1 body with
              | .ok (h', acc2) flow =>
                (match flow with
                 | .next | .cont => initItemsLoop mV fuel h' acc2 a n (i + 1) target body
                 | .brk => .ok (h', acc2) ()
                 | .ret _ => .unsupported "'return' at module top level (CPython: SyntaxError at compile time)")
              | .exn st e => .exn st e
              | .timeout => .timeout
              | .unsupported msg => .unsupported msg)
           | Option.none =>
             .unsupported "an executed init statement rebinds a builtin/def/class/namedtuple name — outside the tier (docs/memory-model.md §module-init execution)")
        | .exn e => .exn (h, acc) e
        | .timeout => .timeout
        | .unsupported msg => .unsupported msg
      else .ok (h, acc) ()
    | _ => .unsupported "internal: items-loop receiver is not a dict (report this)"

/-- Execute ONE fold-refused top-level statement (see the section
comment): the items shell, or `execStmt` delegation with the flush. -/
def initExecStmt (mV : Module) (fuel : Nat) (h : Heap) (acc : GlobalsAcc)
    (s : Stmt) : Run (Heap × GlobalsAcc) Unit :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match s with
    | .forStmt target (.call (.attribute d "items" _) #[] #[] Option.none _) body orelse _ =>
      (match orelse.toList with
       | [] =>
         (match evalExpr mV fuel ⟨⟨h, resolvedG acc, [], []⟩, []⟩ d with
          | .ok st dv =>
            (match dv with
             | .ref a =>
               (match Heap.get? st.world.heap a with
                | some (.dict entries _) =>
                  initItemsLoop mV fuel st.world.heap acc a entries.size 0 target body.toList
                | _ =>
                  .unsupported "'.items()' on a non-dict receiver is outside the init shell (docs/memory-model.md §module-init execution)")
             | _ =>
               .unsupported "'.items()' on a non-dict receiver is outside the init shell (docs/memory-model.md §module-init execution)")
          | .exn st e => .exn (st.world.heap, acc) e
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg)
       | _ :: _ => .unsupported "'for … else' at module init is outside the tier")
    | s =>
      match execStmt mV fuel ⟨⟨h, resolvedG acc, [], []⟩, []⟩ s with
      | .ok st flow =>
        (match flushInitLocals mV acc st.locals with
         | some acc' =>
           (match flow with
            | .next => .ok (st.world.heap, acc') ()
            | _ => .unsupported "loop flow at module top level (CPython: SyntaxError at compile time)")
         | Option.none =>
           .unsupported "an executed init statement rebinds a builtin/def/class/namedtuple name — outside the tier (docs/memory-model.md §module-init execution)")
      | .exn st e => .exn (st.world.heap, acc) e
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

/-- The live pipeline (see the section comment). `done` carries the
statements already processed — the per-statement prefix view. -/
def initFoldLive (m : Module) (fuel : Nat) :
    Heap → GlobalsAcc → Array Stmt → List Stmt → Heap × GlobalsAcc
  | h, acc, _, [] => (h, acc)
  | h, acc, done, s :: rest =>
    match initFoldStep h acc s with
    | some (h', acc') => initFoldLive m fuel h' acc' (done.push s) rest
    | Option.none =>
      -- the view INCLUDES the executing statement: its dirty names are
      -- then statically POISONED (not absent), so its own in-progress
      -- bindings resolve through the poisoned-arm live view, whose
      -- closure guard SEES the statement's nested defs (an s-less view
      -- would misfire the not-callable TypeError on the loop's lambda)
      match initExecStmt { m with topLevel := done.push s } fuel h acc s with
      | .ok (h', acc') _ => initFoldLive m fuel h' acc' (done.push s) rest
      | _ =>
        -- the attempt failed: ROLL BACK and POISON the statement's dirty
        -- names in the LIVE accumulator too — without the live marker
        -- the poisoned-arm consult would resurface a STALE value
        match globalsDirty h acc true s with
        | (h', acc', _) => initFoldLive m fuel h' acc' (done.push s) rest

/-- The fresh `World` of one public call: the LIVE-pipeline heap and
globals (pass 3 — for a module with no exec-attempted statements this is
exactly the pure fold's heap and `resolvedG` table, arm for arm). Built
afresh per public call, so module-global dicts are shared across nested
calls WITHIN one public call and fresh ACROSS two (regression case 15).
Name resolution reads the static `moduleGlobals` table FIRST; the
statically-poisoned and statically-absent arms consult `World.globals` —
the live view (docs/memory-model.md §module-init execution). -/
def initWorld (m : Module) : World :=
  match initFoldLive m initExecFuel #[] [] #[] m.topLevel.toList with
  | (h, acc) => { heap := h, globals := resolvedG acc }

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

/-- `callFunction` with the world's CLOCK TRACE seeded (pass 6,
docs/memory-model.md §the trace clock): the only difference from
`callFunction` is `World.clock := clock` — the batch harness's surface
for `"clock"`-carrying rows. `callFunction m f args fuel` IS
`callFunctionClock m f args [] fuel` definitionally (a structure-literal
`clock := []` is the field's default). -/
def callFunctionClock (m : Module) (fname : String) (args : Array Val)
    (clock : List Int) (fuel : Nat) : Res Val :=
  Run.toPublic fuel
    (callIn m fuel { initWorld m with clock := clock } fname (RVal.thawArgs args))

end LeanModels.Python
