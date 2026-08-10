# The Python heap layer: memory model (v2 — review-corrected design)

Status: NORMATIVE; the H1 core (threading, 2026-08-06), the H1-proper
dict tier (2026-08-07), the H2 list tier's IN-WORLD half (2026-08-07:
heap `Obj.list` everywhere the interpreter builds a list — literals, G1
module tables, `sorted` results — with the §list-semantics inventory
below), the H3 CLASS tier (2026-08-08: `Obj.instance`, ClassDef
representation end to end, methods as flattened functions through
`callIn`, mutable self — §class semantics below), and the NAMEDTUPLE
value tier (2026-08-08: `RVal.ntuple` immediate values, ingestion-time
recognition, loud boundary — §class semantics, the recorded VALUE-like
decision implemented) are BUILT to this document.
Still pending from it: the H2
**boundary flip** — `callFunction` still thaws `Val.list` ARGUMENTS to
the transitional value form (`RVal.listV`, reads in tier, mutation
loudly refused), while the heap-threading thaw (`RVal.thawH`, fresh
object per occurrence) and the fueled snapshot freeze (`RVal.freezeH`)
are built and the RETURN side already runs through them — flipping the
argument side is the recorded next step (docs/backlog.md) and carries
the list-example proof rebase; live dict iteration (`for k in d` is
loudly out of the inventory — the no-snapshot rule below);
value-container membership on `str`/`tuple`/`listV` (`x in "s"` — loud;
heap-list membership IS in tier); the full interpreter-wide `Heap.WF`
preservation theorem (defs + allocation/update/empty lemmas exist;
acceptance case 18 is covered by concrete regressions); and the H3+
stages. Deviation record lives in AGENTS.md. Revised per the owner review of 2026-08-06
(conditional veto of v1: heap representation approved; boundary types,
call layering, exception outcome, and fuel behavior corrected). The old
exploratory `Res (Heap × α)` threading on branch `h1-threading` is
superseded (kept for its mechanical rebase notes).

Oracle pin: **CPython 3.9.x** (the repo's extractor/tier baseline). Dict
insertion order is a language guarantee since 3.7, but iterator details,
exception messages, and method sets are checked against 3.9.

## Core shape (normative)

```lean
abbrev Addr := Nat
abbrev REnv := List (String × RVal)

/-- Runtime values — what a running Python world manipulates. -/
inductive RVal where
  | none
  | bool  (b : Bool)
  | int   (n : Int)
  | str   (s : String)
  | tuple (xs : Array RVal)    -- may contain refs (aliasing through tuples)
  | listV (xs : Array RVal)    -- transitional value-lists (see below)
  | ref   (a : Addr)

/-- Heap objects — identity-bearing, mutated in place. -/
inductive Obj where
  | dict (entries : Array (RVal × RVal)) (shapeVersion : Nat)
  | list (xs : Array RVal)     -- H2 (built)
  | instance (cls : ClassId) (attrs : Array (String × RVal))  -- H3 (built)
  -- H4: | iterator (state : IterState)

abbrev Heap := Array Obj

structure World where
  heap    : Heap
  globals : REnv
  stdout  : List String := []   -- effects are data (§effects; owner-directed)

structure FrameState where
  world  : World
  locals : REnv

/-- Interpreter outcome: state is RETAINED on `.ok` AND on `.exn`
(mutations and bindings made before a raise survive — observable once
`try` lands, and pinned by regression before that). `bind` threads state
through `.ok`, preserves it in `.exn`, short-circuits the rest. -/
inductive Run (σ : Type) (α : Type) where
  | ok          (state : σ) (value : α)
  | exn         (state : σ) (error : PyErr)
  | timeout
  | unsupported (message : String)

evalExpr  : Module → Nat → FrameState → Expr      → Run FrameState RVal
execStmt  : Module → Nat → FrameState → Stmt      → Run FrameState RFlow
execStmts : Module → Nat → FrameState → List Stmt → Run FrameState RFlow
callIn    : Module → Nat → World → String → Array RVal → Run World RVal
callFunction : Module → String → Array Val → Nat → Res Val   -- UNCHANGED
```

**`Val` (the existing type) is the frozen public boundary type and keeps
`Val.list` permanently** — it is the argument/observation snapshot form.
`ToVal Val := id` stays safe because refs are not representable in `Val`
at the type level: "addresses never leave the interpreter" is a typing
fact, not a convention. `CallsTo`, every `@[spec]` raw form, and every
existing theorem statement remain literally unchanged.

### The call layering

`callIn` is the mutual-recursion point (and the frozen recursion point of
the proof doctrine — replacing `callFunction` in that covenant): nested
Python-to-Python calls use ONLY `callIn`, sharing the caller's world
(aliasing across calls, mutation of arguments visible to the caller).

`callFunction` is the isolated public observation:
1. create a fresh `World` (empty heap, initialized globals — see module
   initialization below);
2. **thaw** boundary arguments (`Val → RVal`): every mutable-container
   occurrence in the marshalled tree is freshly materialized — distinct
   occurrences are distinct objects. The public surface therefore
   describes exactly the alias-free argument graphs; an alias-aware
   surface (explicit object graph with named roots, or a pre/post-world
   judgment) is future work and must never infer aliasing from structural
   equality nor from Lean pointer identity;
3. run `callIn`;
4. **deep-freeze** the returned `RVal` (`RVal → Res Val`): inspect the
   whole value, not just a root `.ref`. Cycle detection uses the ACTIVE
   RECURSION PATH — a repeated address on the current path is a cycle
   (loudly unsupported until a faithful outcome exists); a repeated
   address NOT on the path is sharing (a DAG), legitimately duplicated in
   the frozen snapshot because the observation deliberately forgets
   identity. A dict anywhere in the result is unsupported until public
   `Val` has a dict observation form; a (H2) list freezes to a snapshot;
5. erase the world from the public result.

Public fuel monotonicity decomposes: init-mono ∘ thaw-mono ∘ callIn-mono
∘ freeze-mono — `fuelMono` is proved for the `Run`-typed mutual block
(state is data; monotonicity is in fuel only), and the public
`callFunction_mono` is derived through the wrapper.

### The stateful call judgment (`CallsIn`) — needed by H2, designed in H1

```lean
def CallsIn (m : Module) (before : World) (fname : String)
    (args : Array RVal) (after : World) (result : RVal) : Prop :=
  ∃ fuel, callIn m fuel before fname args = .ok after result
```

A fresh-world `CallsTo` fact is NOT a valid nested-call spec once heaps
are shared: the heap-aware VC call rule consumes `CallsIn` (or a stateful
`CallTriple`), never bare `CallsTo`. Pure callee specs lift into the
stateful rule via an explicit heap/global frame theorem. This judgment is
required no later than H2: an in-place procedure returning `None` (list
mutation, aliased arguments, caller inspecting afterwards) is otherwise
unspecifiable. The VC error arm becomes state-aware
(`err : PyErr → FrameState → Prop`) in the same rebase — one foundational
proof-layer rework, not two.

### Fuel vs frontier (normative rule)

Fuel exhaustion — anywhere, including equality recursion and deep
freeze — is ALWAYS `.timeout` (the `⊑`-bottom `fuelMono` requires).
`.unsupported` marks only the fuel-INDEPENDENT semantic frontier. A
detected cyclic comparison is a faithful `RecursionError` (or, if
deferred, a fuel-independent `.unsupported "cyclic equality"` decided by
cycle DETECTION, never by running out of fuel).

## Identity, `is`, `==`

* `is` on two refs is address equality — faithful, decided dynamically
  (the extractor stops collapsing non-`None` identity comparisons to
  `Unsupported`; the interpreter refuses only the remaining out-of-tier
  operand forms, loudly). `is` between non-ref immediates other than the
  `None` link stays out of tier (CPython caching is
  implementation-defined). Tuple `is` stays out of tier (documented
  omission, never wrong).
* Runtime `==` (dicts): (1) identical addresses → `True` immediately
  (CPython's identity shortcut — `d == d` holds for self-cyclic `d`);
  (2) distinct dict refs: compare sizes; (3) traverse the LEFT dict in
  insertion order — the boolean ignores order, the evaluation order does
  not (an early mismatch returns `False` before a later cyclic value
  would raise); (4) look up each key in the right dict, compare values
  recursively; (5) track the set of ACTIVE address pairs; re-entering an
  active distinct pair raises `RecursionError` (two separate self-cyclic
  dicts do NOT compare equal — Python does not equate bisimilar cycles).

## Dict semantics (H1 inventory)

* Keys: H1 admits exactly `none`, `bool`, `int`, `str`, and tuples
  recursively containing H1-admitted keys ("hashable = immutable" is NOT
  the definition — hashability is stable-hash + compatible-equality; a
  ref's hashability depends on its referent: dict/list referents are
  unhashable, a default H3 instance is hashable by identity). Unhashable
  keys raise `TypeError` BEFORE any scan, even on an empty dict. Key
  equality is `==` with bool/int coercion (`d[True]` is `d[1]`).
* Update through an equal-but-nonidentical key REPLACES ONLY THE VALUE
  and retains the originally stored key and its insertion position
  (`{True: "old"}` then `d[1] = "new"` lists `[True]`). Duplicate equal
  keys in a literal: first key/position, last value.
* `d[k] = v` evaluation order (language reference): RHS first, then the
  target primary `d`, then the subscript `k`, then the store — a stateful
  `assignTo` must not evaluate the target early. Method calls
  (`d.get(key(), default())`): receiver/attribute lookup before
  arguments; both arguments evaluate before `.get` decides.
* Iteration `for k in d` is a LIVE ITERATOR, not a snapshot: state =
  dict address + expected size + cursor (+ `shapeVersion`). Updating an
  existing key's value during iteration is fine; inserting a new key
  raises `RuntimeError` at the NEXT iterator step (breaking first does
  not retroactively raise); the iterable expression evaluates once;
  nested iterations have independent cursors. If this is not implemented
  in H1, `for k in d` stays OUT of the inventory — no snapshot-keys
  shortcut. `shapeVersion` increments on insertion/deletion, not on
  value updates (future-proofs deletion/reinsertion).
* In tier H1: literals, read (`KeyError` faithful), write (aliasing-
  visible), `len`, `in`/`not in`, `.get(k)`/`.get(k, d)`, `==`/`!=`,
  truthiness, live iteration as above. Loud: `.keys/.values/.items/
  .update/.pop/…`, `del d[k]`, comprehensions, `**kwargs`, `|`,
  returning a dict through the boundary.

## List semantics (H2 inventory — the in-world half is BUILT)

* Every list the interpreter BUILDS is a heap object: literals allocate
  (`BUILD_LIST` — each display a fresh object), G1 module-level list
  tables allocate into `initWorld`'s heap (shared across nested calls
  within one public call, fresh across two — case 15's list analog), and
  `sorted` allocates its fresh result. Aliasing is visible: two
  references to one list see each other's writes; callee mutations reach
  the caller through `callIn`'s shared world.
* In tier: subscript read/write (bool/int indices coerce; negative
  indices from the end; out-of-range a faithful `IndexError` — CPython
  assignment never extends), `len`, truthiness, `in`/`not in` (the
  `element == probe` scan, element on the left, through the fueled
  `heapEq`), `==`/`!=` (identity shortcut, size check, elementwise,
  active-pair `RecursionError` on corresponding cycles), dynamic
  `is`/`is not`, `.append(x)`, `.pop()`/`.pop(i)` (empty/out-of-range pop
  a faithful `IndexError`), unpacking `a, b = lst` (an eager snapshot
  read, per CPython), and `for` — a LIVE INDEX CURSOR against the object
  (`execForList`, a frozen recursion point): the body's writes, `append`
  growth, and `pop` shrinkage are observed exactly as CPython's
  listiterator observes them; never a snapshot.
* Lists are unhashable keys (`TypeError: unhashable type: 'list'`, named
  through the heap); a returned list freezes to a `Val.list` SNAPSHOT
  (sharing legitimately duplicated, cycles loudly refused — §call
  layering); the wrapper's freeze takes the PURE fast path on ref-free
  results (`RVal.refFree` — the `heapEq` doctrine at the boundary) and
  only ref-carrying results enter the fueled `freezeH`.
* Loud, deliberately: list concatenation `+` and repetition (allocating
  operators would evict every `BinOp` from the heap-free fragment — they
  need an allocation-aware frame story first), `+=`/`.extend`,
  `.insert/.remove/.index/.sort/...`, slices (STR slices are BUILT —
  §string semantics; LIST slices allocate and stay loud pending the
  allocation-aware frame story), `del lst[i]`, comprehensions,
  `.get`-style method calls on lists (a faithful `AttributeError`
  awaiting a `PyErr` form).

## Class semantics (H3 inventory — BUILT, 2026-08-08)

* **Representation**: `ClassDef` is structured end to end (extractor →
  envelope → ingestion; sunfish's three ClassDef bodies are represented).
  Ingestion FLATTENS method bodies into `Module.functions` under
  qualified names `"<class>.<method>"` — a Python identifier can never
  contain `.`, so plain-name resolution never sees them — and records
  the class in `Module.classes`. **Methods are functions**: a method
  call resolves the qualified name and runs through `callIn` with `self`
  as an ordinary `.ref` first argument, so `CallsIn` specifies methods
  verbatim (no new call judgment — `Examples/python/sf_searcher`).
* **ClassId** is the INDEX into `Module.classes`, never the name.
  Duplicate class names resolve last-wins consistently on both tables
  (instantiation and qualified-name lookup), so an instance of a
  shadowed earlier class is unconstructible. A name bound by both `def`
  and `class` is loud (the split representation loses source order).
* **The dunder guard** (the tier's soundness principle): a class
  defining any dunder beyond `__init__`, with bases (inheritance —
  loudly unsupported), keywords/metaclass, decorators, or class-level
  statements (class attributes) is REPRESENTED but UNINSTANTIABLE
  (loud). Therefore every instance that exists has DEFAULT object
  protocol, which makes the following faithful by construction:
  instance `==` is identity (no shortcut subtleties — no user `__eq__`
  can exist), truthiness is `True`, `is`/`is not` by address, and the
  default-protocol refusals are real CPython errors — `len()`/
  subscript/iteration/unpacking/membership/`sorted`/`max`/`min` on an
  instance raise the faithful `TypeError`.
* **Instantiation** `C(args)`: allocate `Obj.instance ci #[]` in the
  shared world, then run `C.__init__` through `callIn` with
  `self = .ref a`; a non-`None` `__init__` result is the faithful
  `TypeError`; an `__init__`-less class called with arguments likewise
  (`C() takes no arguments`). Allocation happens after argument
  evaluation (identity-free observations cannot tell).
* **Attributes** (mutable self): reads resolve the instance attribute
  table first, then the class's methods (a bound-method VALUE is loud —
  methods are called, not passed), then the faithful `AttributeError`
  (`PyErr.attributeError`, message-free like `keyError`; no
  `__getattr__` can exist). A missing attribute in CALL position raises
  BEFORE arguments evaluate (CPython order: receiver and attribute
  lookup precede arguments). Stores (`self.x = v`) update `attrs` in
  place (`Env.set` semantics — replace-in-place or append, `__dict__`
  insertion order), CPython evaluation order RHS → target primary →
  store; attribute stores on dicts/lists/scalars are the faithful
  `AttributeError`. Also faithful now: `.get` on a list, `.append` on a
  dict (`AttributeError`, previously loud).
* **Instances as dict keys** are LOUD (CPython hashes by identity —
  in-tier keys stay value-hashable; `keyRefusal` never raises a fake
  `unhashable` `TypeError` for them). An instance cannot cross the
  public boundary (no `Val` observation form — the freeze refuses
  loudly). Referencing a class as a value is loud.
* **Meta-proof discipline** (recorded finding): dispatch that forks on
  a heap referent must fork on a PURE plan computed from free variables
  (`attrReadPlan`/`attrCallPlan`; `execAttrCall` joined the mutual
  block, conjuncts appended LAST so `fuelMono`/`worldInv` projection
  paths survive) — a match nested under the receiver's binder is
  invisible to `cases`/`rw` in the meta proofs. `Module.heapFree` now
  also requires `classes = #[]`: instantiation allocates, and syntax
  cannot tell a class call from a function call.
* **namedtuple (the VALUE-like decision — BUILT, 2026-08-08)**:
  namedtuple instances are **VALUE-like** — immutable record types are
  immediate values, per this document's hybrid principle (immutable =
  immediate), NOT heap objects: `RVal.ntuple tname fields xs` carries
  its own class and field names, so no module table is consulted at
  access time. Field access desugars to tuple indexing (declaration
  position); equality/hashing/`len`/subscript/iteration/unpacking/
  `max`/`min`/`+`-concatenation (a PLAIN tuple results, as in CPython)
  are the value-tuple semantics with the class ERASED — `Move(1,2,"")
  == (1,2,"")`, and both address ONE dict slot, which is exactly why
  sunfish's `tp_score` keys containing a `Position` stay in the pure
  `keyEq` tier. **Recognition is at INGESTION** (all-or-nothing per
  module, Json.lean): `X = namedtuple("T", <fields>)` under the exact
  benign import `from collections import namedtuple`, CPython-validated
  field specs, and a conservative binding census (every top-level
  statement analyzable; `X` bound exactly once; `namedtuple` bound and
  referenced nowhere else; no def/class subtree contains `global` — the
  extractor-recorded `has_global`, exact even under opaque
  `try`/`with`); the recognized statements become `pass` and the table
  fills `Module.namedtuples` — anything else leaves the module
  unchanged (poisoned binding, loud). Construction is exact-arity (the
  faithful `TypeError` otherwise) and allocates NOTHING — heap-free
  modules keep namedtuples. **The boundary refuses namedtuple results
  LOUDLY** (recorded decision): no `Val` observation form exists, and a
  `Val.tuple` snapshot would silently forget the class AND falsify
  freeze inversion (`eq_thaw_of_freeze*`) — `CallsIn` is the surface
  that sees the values (`Examples/python/sf_position`). Loud, never a
  fake `AttributeError`: the CPython protocol names
  (`_replace`/`_asdict`/`_make`/`_fields`/`count`/`index`), dunders,
  method calls on a namedtuple receiver, and namedtuple construction at
  G1 module level (constructor calls are out of the call-free G1 tier).
  **Value-like SUBCLASSES (H5 slice 1, 2026-08-08)**: a class whose
  SINGLE base is a plain `namedtuple(…)` call (`class
  Position(namedtuple(…))` — the shipped sunfish shape) is recognized
  structurally (extractor `namedtuple_base` → `ClassDefn.ntBase`,
  promoted/demoted by the SAME module census); instantiation constructs
  the IMMEDIATE value carrying the SUBCLASS name (no allocation, no
  `__init__` — one on the immutable self is loud), and a method name in
  READ position is the loud bound-method refusal, never a fake
  `AttributeError`. The real sunfish.py's `Move`/`Entry`/`Position` all
  recognize as-is (`Position.ok = true` with its six-field base). **Method
  dispatch (H5 slice 2, 2026-08-08)**: `pos.mirror()` runs the flattened
  qualified function through `callIn` with `self` bound to the immutable
  VALUE (no new judgment; subclass methods shadow the base's field
  properties, CPython MRO; a field in call position, the protocol names,
  and dunders are loud; a missing attribute is the faithful pre-args
  `AttributeError`). Dispatch identity: the census also refuses a plain
  candidate whose TYPENAME collides with an `ntBase` class name, so in a
  recognized module a value's `tname` names exactly its defining class.

## String semantics (H5 strings — BUILT, 2026-08-09)

Strings are immutable, so the tier is pure VALUE semantics — no heap,
no aliasing, world-preserving by construction (Semantics.lean §string
tier).

* **Slices** `s[l:u:st]` are structured end to end (extractor `Slice`
  node; absent components ingest as `Constant None` — CPython's own
  `BUILD_SLICE` compilation, so `s[:i]` and `s[None:i:None]` are the
  same program). Evaluation order is CPython's: receiver, lower,
  upper, step; the receiver dispatch (`sliceVal`) fires only after all
  components evaluate (`BINARY_SUBSCR`), and component validation is
  `PySlice_Unpack`'s order — step first (`TypeError` for a non-index,
  `ValueError` for zero), then lower, then upper
  (`str_lab.order_probe` pins the order differentially). The value is
  CPython-exact for EVERY string: negative indices, out-of-range
  clamping, both step directions (`PySlice_AdjustIndices`). Slicing a
  heap list — or a value list/tuple/namedtuple — succeeds in CPython
  and ALLOCATES, so it stays loudly out (§list semantics); slicing a
  non-subscriptable scalar is the faithful `TypeError`; a slice in
  STORE position stays loud (`assignTo`'s catch-all).
* **Methods** (`strCallPlan` — the `ntupleCallPlan` free-scrutinee
  discipline, plan decided BEFORE arguments): `.swapcase()`,
  `.isupper()`, `.islower()`, and `.upper()` on ASCII strings (the H6
  pair `islower`/`upper` serves the shipped `value()`'s capture arm;
  Lean core's `Char` case maps ARE the ASCII maps, agreeing with
  CPython exactly there; a non-ASCII string refuses loudly — the
  Unicode tables are not guessed), and
  `.index(sub)` — code-point-exact substring search, the faithful
  `ValueError` miss, a non-str argument the faithful `TypeError`
  (`start`/`end` arguments loud). EVERY other attribute on a str
  refuses loudly — never a fake `AttributeError` (CPython's str
  carries ~45 real methods plus the dunder protocol). Arity errors
  are faithful `TypeError`s, raised after the arguments evaluate
  (CPython call order).
* **Simp doctrine** (the `sortInts`/`heapEq` freeze family): the
  dispatchers (`sliceVal`, `strCallPlan`) are in
  `py_simp`/`interpUnfolds`; the value workers (`strSlice`,
  `strSwapcase`, `strIsUpper`, `strIndex` and their helpers) stay
  OUT — symbolic goals keep the compact handles, and concrete proofs
  rewrite through kernel `rfl` facts
  (`Examples/python/sunfish/proof.lean` runs the 120-char board
  through each worker in ONE rewrite).
* **heapFree**: the `Slice` node is in the fragment (every receiver
  is pure or loud). Str METHOD calls conservatively LEAVE the
  fragment — the attribute-call whitelist is still `.get`-only, like
  every `sorted` call; extending it to the pure trio is sound and
  recorded (docs/backlog.md).
* Still loud, deliberately: str unpacking, `%`-formatting, `sorted()`
  on a str, and non-ASCII case mapping.
* Acceptance: `Examples/python/str_lab` (every function differential);
  leanpy corpus `harness/scripts/str_script.py`; the shipped-file
  theorems in `Examples/python/sunfish` (`Position.rotate`).

## Iteration semantics (H5 iteration — BUILT, 2026-08-09)

The membership/iteration surface `gen_moves` needs, decided for EVERY
in-tier container rather than one container at a time.

* **`in` / `not in`** are one dispatcher, `valContains`: a heap
  referent delegates to `heapContains` (dict keys, the H2 list scan);
  a str is CPython's SUBSTRING test (`strContains`; `"" in s` is true,
  and a non-str LEFT operand is the faithful
  `'in <string>' requires string as left operand, not …` `TypeError` —
  str is the one container whose `in` is not element membership);
  value tuples, boundary value-lists and namedtuples scan their
  elements with the same `element == probe` convention as lists
  (`heapContainsScan`, so elements may be refs and each step is the
  fueled `heapEq`), namedtuples class-erased like every other tuple
  observation. Anything else is the faithful "not iterable"
  `TypeError`.
* **`for` over a str** walks its CODE POINTS through `execFor` on
  `strCharVals s`. The snapshot IS the live semantics here: a str is
  immutable, so unlike `execForList`'s heap cursor there is nothing
  for an iterator to observe mid-loop.
* **`ord`/`chr`** are code-point exact. `ord` names the found length
  in its `TypeError`, as CPython does; `chr` outside
  `range(0x110000)` is the faithful `ValueError`, and a SURROGATE code
  point is refused LOUDLY — CPython builds a lone-surrogate str, which
  Lean's `Char` cannot represent, and substituting anything else would
  be silently wrong.
* **Simp doctrine**: the dispatchers (`valContains`, `ordVal`,
  `chrVal`) are in `py_simp`/`interpUnfolds`; the value workers
  (`strContains`, `strCharVals`) stay OUT, like `strSlice` — a
  concrete proof rewrites through one kernel `rfl` fact per
  application.
* **heapFree**: all three are pure reads, so every node stays in the
  fragment.
* Acceptance: `Examples/python/iter_lab` (every function
  differential); leanpy corpus `harness/scripts/iter_script.py`.

## Generator semantics (H4 — BUILT, 2026-08-09)

A generator is the one construct in sunfish whose LAZINESS is
semantically load-bearing: `bound` consumes `moves()` under a beta
cutoff, and every yield the consumer never reaches must leave its
TT-writing search unrun. A generator-free rewrite is therefore not an
alternative, and neither is pre-expansion; nor is plain desugaring,
because `gen_moves` has ~six yield sites at different control-flow
depths and desugaring collapses into the same state machine anyway. So
the tier takes the principled construction.

**Representation — a heap object, not a value.** `Obj.generator qname
locals cont status` is the suspended frame AS DATA. It is heap-allocated
because a generator is IDENTITY: `h = g; next(g); next(h)` advances one
shared frame, and a `for` loop that abandons a generator by `break` must
leave the very object the next consumer resumes. Both are pinned
differentially (`gen_lab.aliased`, `gen_lab.two_phase`); an
immediate-value representation answers them wrong, silently. `status`
(`created`/`suspended`/`running`/`closed`) exists so a generator that
re-enters itself is CPython's faithful `ValueError`, never a silent
nested resumption.

**Continuation — defunctionalized, structural.** `cont : GenCont` is a
STACK of `GenFrame`s, innermost first: `block rest` ("finish these
statements"), and one frame per suspendable loop carrying exactly the
residual state CPython's frame carries (`forSeq` remaining elements,
`forList` a live heap cursor, `forGen` a sub-generator address,
`whileLoop` test/body/orelse). Every statement list in a frame is a
structural SUFFIX of the function body, so a frame is a structural PATH
into it — never an arbitrary expression context, which is why `yield` is
admitted in STATEMENT position only. Loop frames carry no "rest of the
enclosing block": the frames BELOW already are it, which makes the three
exits uniform — normal exhaustion and `break` both POP the loop frame,
`continue` re-enters it (advancing the cursor), and a `while`'s `orelse`
is pushed on normal exit and skipped on `break` (`genBreak`/
`genContinue`, two pure unwinders).

**Stepping.** `stepIter m fuel w a : Run World (Option RVal)` — `some v`
is the next yield, `none` exhaustion — and `execGen m fuel st k :
Run FrameState (Option (RVal × GenCont))` runs the body from a
continuation to the next yield. Both are FROZEN recursion points, like
`callIn`/`execWhile`/`execFor`. `execGen` delegates every yield-FREE
statement to the ordinary `execStmt`, so those statements keep exactly
one definition; only the constructs that can suspend are opened. Which
ones those are is decided by a PURE plan, `genPlan : Stmt → GenPlan`,
following the H3 free-scrutinee discipline — and here it is not a
convenience but a requirement: with the statement match written inline,
Lean's equation compiler splits `execGen`'s block arm per `Stmt`
constructor and its equations never fire at a symbolic statement, so
`fuelMono`/`worldInv` cannot step the walker at all.

**Creation and consumption.** `callIn` on a function with
`isGenerator = true` runs NO code: it allocates the frame with the
arguments bound and the whole body as the initial continuation, and
returns the ref. `for x in <generator>` is `execForGen`, a frozen
recursion point that calls `stepIter` once per iteration — so generator
effects interleave with the body's — and `break` simply stops stepping,
leaving the object SUSPENDED. `next(g)` raises the faithful
`StopIteration` at exhaustion; `next(g, d)` consumes exhaustion
(sunfish's `king_capture` shape). `return` inside a generator is
exhaustion; `return <value>` sets `StopIteration.value` in CPython, a
channel the tier does not model, and refuses LOUDLY rather than dropping
the value.

**heapFree.** Generator creation ALLOCATES and syntax cannot tell a
generator call from an ordinary one, so `Module.heapFree` gains a third
conjunct: no generator defs (`moduleGenFree`) — the H3 `classes = #[]`
carve-out, again. `next(...)` calls leave the fragment syntactically
(like every `sorted` call), and the `for`-over-`.ref` dispatch GUARDS on
`moduleGenFree`: in a module with no generator defs no generator object
can exist, so that arm is unreachable and says so loudly. That guard is
what keeps `worldInv` free of a heap-side invariant.

**Generator EXPRESSIONS** are LOWERED at ingestion (`lowerGenExps`,
Json.lean), exactly as CPython compiles them: each genexp becomes a call
`<genexpr@n>(<iter>, <captures…>)` to a synthesized generator function
`for <target> in .0: if <ifs…>: yield <elt>` — first parameter `.0`,
CPython's own name, and the outer iterable evaluated at CREATION. The
one real design point is CAPTURE: CPython closes over the frame BY
REFERENCE, the lowering passes free names BY VALUE, and the two disagree
exactly when a captured name is REBOUND between creation and
consumption. v0 admits a free name only where they provably agree — a
PARAMETER the enclosing body never assigns, or a name resolved outside
the frame anyway (a module-level binding, a builtin). Anything else
leaves the `Expr.genExp` node, and evaluating it refuses loudly. On the
shipped file four genexps lower (`king_capture`'s among them); the ones
inside `bound`'s nested `moves()` are invisible, that whole def being
`Stmt.unsupported "FunctionDef"`.

**Builtin iterators.** `enumerate` and `itertools.count` are generator
FRAMES (`enumSeq`/`enumList`/`countFrom`), not a second object kind, so
`for`/`next`/`stepIter` consume them through one mechanism:
`enumerate(s)` is as lazy as a `def` with a `yield` (value sequences
snapshot — all immutable in tier; a heap list gets the live cursor), and
`count` never exhausts, which is exactly sunfish's ray
(`for j in count(i + d, d)`, ended by the consumer's `break`).

**Loud, deliberately** — never a fake answer: `send`/`throw`/`close` and
every other generator method; a `yield` in EXPRESSION position (the
`send` receiver); finalization/`close`-on-GC semantics; `x in gen`,
`sorted(gen)`, `max`/`min(gen)` and generator UNPACKING (all of them
CONSUME the generator — a stateful read these pure helpers cannot
express); `enumerate` over a generator (it would need a stepper inside
the stepper); a generator as a dict key (identity hash); and a generator
crossing the call boundary (a snapshot of its yields would run the body
eagerly, which is exactly what laziness forbids).

**Acceptance**: `Examples/python/gen_lab` (every function differential,
including two INFINITE generators that terminate only under real
laziness); leanpy corpus `harness/scripts/gen_script.py`.

## Call-site keyword arguments (H6 — BUILT 2026-08-10)

The surface is `f(x, k=v)` — sunfish's `pos.rotate(nullmove=True)` and
`sorted(…, reverse=True)`. The extractor STRUCTURES plain named keywords
(`"keywords": [{"arg": name, "value": expr}]`) instead of flagging the
whole call; `**` unpacking stays `call_unsupported`. The AST call node
gains `kwargs : Array (String × Expr)`.

**Evaluation order** is CPython's: positional argument expressions, then
keyword VALUE expressions, left to right — which is source order,
because Python syntax forbids a positional after a keyword (starred
arguments, the exception, are refused at extraction).

**Binding never touches `callIn`.** Its signature is covenant
(§proof-layer covenants); keywords are resolved to a COMPLETE positional
array at the CALL SITE by a pure merge against the callee's `params`:
name → slot; faithful `TypeError`s for an unexpected keyword, multiple
values for one parameter, and a missing required parameter; holes and
trailing gaps fill from literal `Param.default` via `Const.toRVal` — the
same def-time-literal argument `mkCallEnv` already records. The merge
requires `argsOk`: on a function whose parameter list we do not fully
understand, the refusal is the LOUD unsupported, never a binding
`TypeError` computed from an untrusted table.

**Callee coverage** (everything else with keywords is loud):

* module-level `def`s called by name;
* namedtuple-subclass method calls (the ntuple receiver prepends `self`,
  then the same merge on the flattened defn's params);
* instance-method calls (bound() arc pass 1 — BUILT 2026-08-10):
  `self.bound(…, root=True)`, the shipped shape — an attribute call on
  a `.ref` receiver whose `attrCallPlan` is `.instMethod` evaluates
  positional arguments then keyword values (source order, CPython's),
  prepends the receiver, and binds through the SAME merge against the
  flattened defn's params, gated on `argsOk` like every merge;
  `fuelMono` carries the mirrored walk;
* the builtin `sorted`: `reverse=<expr>` is accepted (truthiness
  decides the direction, as CPython's does); `key=` is REFUSED loudly —
  it gates on first-class callable values (a bound method as a value is
  loud under H3), not on draining, and is recorded in the backlog; any
  other keyword name on `sorted` is CPython's faithful `TypeError`.

Loud by choice: BUILTIN heap-receiver methods with keywords
(`.get`/`.append`/`.pop` — positional-only in CPython, and we decline
to fake the exact `TypeError`), calling an instance ATTRIBUTE value,
class instantiation and namedtuple CONSTRUCTION with keywords (CPython
allows the latter; a wrong guess about field order would be silent
corruption), str methods, and every other builtin.

**Fragments**: a call carrying keywords leaves `heapFree` (conservative;
sunfish's keyword sites live inside method bodies that are already out
of the fragment). The G1 scans see keyword values as ordinary subtree
expressions; a keyword name binds nothing in the caller.

## Draining consumers (H6 — BUILT 2026-08-10)

sunfish's ordering line is
`sorted(((pos.value(m), m) for m in pos.gen_moves()), reverse=True)`
(NO `key=` anywhere in the shipped file), guarded by `any(…genexp…)` /
`all(…genexp…)`. Three consumer families over the H4 stepper:

* **Full drain** — `sorted`/`max`/`min` of a generator ref: a frozen
  mutual member `drainIter` loops `stepIter` to exhaustion (the object
  ends `closed`; body effects interleave into the shared world exactly
  as stepping does; fuel bounds the drain, so an infinite generator is a
  loud timeout). The drained values then take the SAME pure path as a
  value-list argument.
* **Short-circuit drain** — `any`/`all` (NEW builtins): step until the
  first truthy (`any`) / falsy (`all`) element and STOP — the generator
  stays SUSPENDED and resumable, CPython's partial drain, pinned
  differentially by an effect-observing generator plus a post-call
  `next`. Non-generator receivers scan without draining: strs by code
  point, value tuples/lists and heap lists by snapshot (no user code can
  run mid-scan in tier, so the snapshot IS the live semantics); dicts
  stay loud (live iteration).
* **Ordering comparison, one relation** — `sorted` beyond all-int lists
  needs `<` on tuples, and the OPERATOR and the sort must share it:
  `rvalLt` (worker, `valEq`/`valEqList` recursion geometry) — int/bool
  numeric, str code-point lexicographic, tuple/namedtuple lexicographic
  and CLASS-ERASED (first `valEq`-differing element decides via
  `rvalLt`; exhaustion → shorter is smaller). `evalCompareOp`'s ordering
  arm gains the tuple case derived from the same worker (`a <= b` as
  `¬(b < a)` is exact within this tier). Refs and mixed value kinds
  refuse loudly, as the operator does today — never a guessed
  `TypeError`.

**Sort algorithm**: stable insertion by `rvalLt` only (CPython sorts
call only `__lt__`); within the tier every total order agrees with
timsort, and comparison refusals surface as the drained list's loud
refusal, position-independent. `reverse=True` is descending STABLE
insertion (insert before the first strictly-smaller element) — NOT
sort-then-reverse: `sorted([1, True], reverse=True)` keeps `[1, True]`,
a reversal would forge `[True, 1]`. `sorted` still allocates its result
(H2); `max`/`min` of an empty drain is the faithful `ValueError`.

Simp doctrine unchanged: dispatchers in the sets, the new workers
(`rvalLt`, the merge, the drain) OUT (the `sortInts` freeze family).

**As built (2026-08-10):** `drainIter` (full drain) and `anyAllIter`
(short-circuit) are frozen mutual members, conjuncts appended LAST;
all-int ascending `sorted` and all-int `max`/`min` keep their ORIGINAL
`sortInts`/`foldExtremum` computation paths byte-for-byte (the
proof-layer bridges and captured runs depend on those terms); `sorted`
gained str/tuple/namedtuple receivers (CPython sorts them); `max`/`min`
gained the general `rvalLt` fold plus str receivers. Fragment
bookkeeping: `any`/`all` are excluded from `heapFree` syntactically
(their generator arm drains unguarded); `max`/`min` STAY in the fragment
— their drain arm is guarded on `moduleGenFree`, which a heap-free
module discharges (`Module.heapFree_genFree`), so a generator-free
module keeps today's loud refusal and `worldInv` never meets the drain.
The `value()` prerequisites `.islower()`/`.upper()` landed in the str
tier (§string semantics). Acceptance: `Examples/python/drain_lab`
(observable partial drains, the bool-identity stability pins, the
infinite-`any` laziness pin) and `Examples/python/sf_order` — the
shipped ordering line VERBATIM over the verbatim `gen_moves`/`value`
(padded `pst` = CPython's own output of the shipped padding loop),
differential on whole ordered move lists, opening board included.

## Nested defs and closures (H7 — BUILT 2026-08-10)

The target is `bound()`'s inner `def moves():` — a nested def that is
ALSO a generator, closing over `self`/`pos`/`gamma`/`depth`/`root`/
`val_lower`, consumed lazily by the fold below it. Python closes over
VARIABLES (cells), not values; the tier implements a SNAPSHOT taken when
the `def` statement executes, and admits exactly the fragment where the
two are observationally equal:

**The never-rebound restriction (extraction-time, loud).** A nested def
is STRUCTURED (envelope kind `NestedDef`, one level deep) only when
every captured name — a free name of the nested body that is a local or
parameter of the enclosing function, CPython's symtable rule — is:

* a parameter of the enclosing function, or bound by at least one
  statement textually BEFORE the def (else the snapshot could miss —
  CPython would raise the free-variable `NameError`; we refuse);
* bound NOWHERE textually after the def (assignment, augmented
  assignment, `for`-target, unpacking, `del`, import — any binding
  occurrence); and the def itself sits in NO loop body of the enclosing
  function (a loop makes "textually after" and "executes after"
  diverge, and re-creating the closure per iteration is exactly where
  cell-vs-snapshot becomes observable).

`nonlocal` in the nested body, a def nested deeper than one level, and
any violation above keep today's loud `Stmt.unsupported` — the
extractor records the precise reason, and a differential row pins the
refusal (never a snapshot translation that CPython's cells would
falsify). Under the restriction, snapshot and cell agree even for a
GENERATOR nested def, whose body reads captures at RESUME time: the
cell's content can no longer change after creation, so read-at-resume
equals read-at-def. The shipped `moves()` satisfies the restriction as
written (`depth = max(depth, 0)` and `val_lower = …` both precede the
def; nothing rebinds after).

**Representation.** `Stmt.defStmt` carries the nested function INLINE
(name, params, the argsOk/localsOk/hasGlobal censuses scoped to the
nested body, `isGenerator`, body, captures). Executing it snapshots the
captured names from the CURRENT frame and ALLOCATES `Obj.closure`
(functions are heap objects with identity in CPython): parameters +
snapshot become the callee env at call time (parameters shadow
captures), so no `Module.functions` flattening and no qname scheme —
`callIn`'s covenant signature is untouched, and a new frozen mutual
member `callClosure` mirrors its call shape. Calling a GENERATOR
closure allocates the H4 `Obj.generator` with the snapshot already in
its stored locals — resume-time capture reads fall out of the existing
stepper for free.

**Closure objects elsewhere, faithful or loud:** truthy; `==` by
identity (two distinct function objects are unequal in CPython — the
distinct-address answer `False` is EXACT); not iterable / no `len` /
not subscriptable (faithful `TypeError`s); a dict key (identity hash)
loud; crossing the public boundary loud (a snapshot would forget
identity); attributes loud; keyword arguments on a closure call loud
(recorded — the merge needs only wiring, nothing in the shipped file
calls a closure with keywords).

**Fragments.** `Stmt.defStmt` ALLOCATES → out of `Stmt.heapFree`. The
closure-CALL arm (a local name resolving to a `.ref`) is guarded on
`funsHeapFree` — the fragment's own function-body walk, which is false
the moment any body contains a nested def — so heap-free modules keep
the existing faithful `TypeError` for called refs, and `worldInv` never
meets a closure call (the `moduleGenFree` guard discipline).

**As built (2026-08-10):** `callClosure` is a frozen mutual member
(conjunct appended LAST); the extractor emits `NestedDef` for DIRECT
children of a function body with the capture set and the refusal
reasons; two admission edges hardened beyond the design: a call of a
nested-def NAME before its def is CPython's `UnboundLocalError` under
the static-locals rule, so it rides the loud `locals_unsupported`
channel (a module fallthrough would silently call the wrong function),
and direct nested-def names count as enclosing LOCALS for the capture
analysis, so a closure may capture an EARLIER closure (`chain`) under
the same never-rebound rule. The shipped `moves()` is ADMITTED as
analyzed: captures `depth`/`gamma`/`pos`/`root`/`self`/`val_lower`,
no refusal, generator. Acceptance: `Examples/python/closure_lab`
(the `rebound_after` row is CPython's cell semantics OBSERVABLE — 6
where a snapshot would forge 5 — refused at extraction, never
translated) and `sf_order.bound_probe`, the `moves()`-shaped nested
generator with the verbatim ordering line inside and the beta cutoff
abandoning it mid-drain: `(46, 1)` cutting vs `(46, 20)` not.

**Lambdas (bound() arc pass 1 — BUILT 2026-08-10).** A single-target
`name = lambda params: expr` assignment DIRECTLY in a function body is
the nested-def shape with a one-statement body — sunfish's
`put = lambda board, i, p: board[:i] + p + board[i + 1:]` in
`Position.move`. The extractor rewrites exactly that assign into
`NestedDef` with body `[Return expr]` (CPython compiles a lambda body
as its own function scope; the rewrite is the same compilation). The
capture census is the same `_closure_analysis` with one scope fact
made explicit: a lambda's locals are its PARAMETERS ONLY (a lambda
body cannot contain assignments), so `_assigned_names` applies to
`FunctionDef` nodes only. The same never-rebound admission decides —
`closure_lab.lam_rebound` is the refused exposing row, lambda flavor
(CPython's cell would see the rebinding; a snapshot would not) — and
everything fancier keeps the loud channels it already had: non-literal
defaults, `*args`/keyword-only/`**kwargs` via `args_unsupported`, and a
lambda anywhere OTHER than a single-target direct assign (call
argument, conditional expression, in a loop, multiple targets) stays
the un-rewritten `Lambda` expression node, refused loudly at
evaluation. NO new runtime: the lambda IS `Obj.closure` with a
`Return` body. Consequence on the shipped file: `Position.move` runs
as shipped — the census has no refusals left — and
`sf_order.move_probe` pins the verbatim `move` + `rotate` chain
differentially.

**Recursion through a captured receiver (bound() arc pass 2 —
designed and BUILT 2026-08-10; as-built notes at the end).** The last
structural construct of `bound()`'s move loop:
`yield move, -self.bound(pos.move(move), 1 - gamma, depth - 1)`,
evaluated INSIDE the suspended-then-resumed `moves()` frame, where
`self` is a snapshot-captured `.ref` to the Searcher instance. The
claim this design records: the construct needs NO new representation
and NO new mutual-block member — it is the COMPOSITION of pieces
already built, and what it needs is the demonstration that they
compose, pinned differentially:

* **Dispatch is frame-agnostic.** A resumed generator body evaluates
  its yield expression through the same `evalExpr` as any frame, with
  the snapshot in the stored locals — so `self` resolves to the `.ref`,
  `execAttrCall`/`attrCallPlan .instMethod` dispatches the flattened
  `"Searcher.bound"` through `callIn`, and the callee runs NESTED
  inside `execGen`/`stepIter`. The mutual block already nests
  arbitrarily under fuel; `running` status on the OUTER generator is
  untouched (the callee resumes only generators IT creates — resuming
  the outer one from inside itself would be the faithful `ValueError`,
  and nothing in the shape does).
* **Effects thread through the running frame.** The recursive callee
  mutates the shared world (`self.nodes`, the TT dicts) mid-step; the
  H4 stepper is `Run`-typed over the world exactly so that a yield's
  evaluation can carry effects. Nothing is snapshotted but NAMES: the
  captured `self` is a `.ref`, so state is one heap object at every
  depth.
* **Identity is per invocation.** Each recursive `bound` executes its
  own `def moves():` — a FRESH `Obj.closure` per call frame — and each
  `moves()` call allocates a FRESH `Obj.generator`; locals never
  shadow across depths because every frame carries its own env. The
  H7 admission is TEXTUAL (never-rebound within the enclosing body),
  so it is depth-oblivious: the same analysis admits every recursive
  instance or none.
* **Fuel is the resume's fuel.** H4 stores NO fuel in the object;
  each resume spends the caller's remaining fuel, so recursive drains
  are bounded by the ordinary structural decrement and the
  `fuelMono`/`worldInv` conjuncts quantify over the whole nest with
  no new argument. Deep probes simply need generous fuel (a depth
  bound, so generosity is free on concrete runs).

What the admission EXCLUDES, stated so the refusal rows can pin it: a
nested def calling ITSELF by its own name (`f` inside `f` — the name
is an enclosing local bound BY the def, not textually before it, so
the census refuses; CPython's cell would resolve it) — sunfish never
does this, `bound` recurses through the METHOD name on `self`, which
is `Module.functions` dispatch, not a captured cell; first-class
method values (`g = self.bound`) stay loud under H3; and every
existing H7 refusal (rebound captures, loops, depth > 1) is unchanged
by recursion.

Acceptance (design): battery rows for direct method self-recursion
(`self.down(n - 1)`), MUTUAL method recursion (`self.odd`/
`self.even`), and recursion FROM a generator frame with the consumer
breaking mid-drain — the per-depth node counter observable proves the
abandoned yields never searched. Refusal row: the self-calling nested
def. Capstone: `sf_order.rec_probe` — a MiniSearcher whose `bound`
folds `moves()` yielding `-self.bound(child, 1 - gamma, depth - 1)`
with the beta cutoff, on small fixed Positions, `(best, nodes)`
against CPython — the cutting/non-cutting gamma pair showing the
recursion tree itself pruned.

*As built (2026-08-10):* the composition claim held EXACTLY — zero
interpreter changes; the pass is battery + capstone only.
`cls_lab.method_rec`/`method_mutual` (direct and mutual dispatch,
one shared `nodes` across the nest), `closure_lab.gen_rec` (the
tree shape: `(2, 4)` under cut=2 vs `(9, 13)` under cut=100 at the
same depth — pruned subtrees never ran), and
`closure_lab.rec_nested_name` refused by the census with the
predicted reason (`'f' has no binding before the def`).
`sf_order.rec_probe`'s moves() captures are the shipped set minus
`root` (`depth`/`gamma`/`pos`/`self`/`val_lower`); the depth-2
cutting/non-cutting pair `(113, 7)` vs `(113, 15)` and the opening
board's `(46, 2)` are kernel-checked and differential. One
mechanical note: the sf_order envelope outgrew the default
elaborator budget — `set_option maxRecDepth 100000 in load_program`,
the `sunfish` example's own pattern.

## Set semantics (bound() arc pass 1 — BUILT 2026-08-10, the honest subset)

The target is `self.history = set(history)` + `pos in self.history` —
`bound()`'s repetition-draw gate, a set that is FROZEN after
construction. A CPython set's iteration order is hash order, and the
tier never guesses it; what is admitted is exactly the ORDER-BLIND
surface, and everything order-revealing is loud.

**Representation.** `Obj.pyset (xs : Array RVal)` — a heap object
(sets have identity), holding the deduplicated elements in first-seen
order. That retained order is UNOBSERVABLE through the admitted
readers, which is the design invariant that makes the subset honest.

**Construction** — `set()` and `set(iterable)`, the only builders.
Iterable coverage: a str (its code points), a value tuple, a
namedtuple (class-erased elements), a boundary list, a heap list,
another set (a fresh already-deduplicated copy), and a GENERATOR —
which DRAINS, like `sorted` (so `set` leaves `heapFree`
syntactically). A dict argument is refused loudly (`set(d)` walks the
keys — live dict iteration is out of tier); non-iterables are the
faithful `TypeError`. Dedup is `setDedup`: the fueled
`heapContainsScan` decides duplicates by VALUE equality through
`heapEq` (the `==` doctrine — bool/int identified, so
`set([1, True])` has ONE element, first occurrence kept), and
elements ride the dict-KEY doctrine: `hashableKey` gates, an
unhashable element gets `keyRefusal`'s answer (the faithful
`unhashable type: '…'` `TypeError` for lists/dicts, LOUD for
identity-hashed instances/closures).

**Admitted readers** — membership (`in`/`not in`, the same
value-equality scan; CPython HASHES the probe before any comparison,
so an unhashable probe raises the same faithful `TypeError`, empty
set included — `set_lab.unhashable_probe` pins it), `len`, and
truthiness. All three are order-blind by construction.

**Loud, never guessed** — iteration (`for v in s`), `sorted(set)` /
`max`/`min` over a set (refused although a sorted RESULT would be
order-independent — deliberately deferred, recorded), every mutator
(`add`/`remove`/`discard`/`pop` — `pop` removes an ARBITRARY element,
the message says so), set operators and `==` between sets, a set
crossing the public boundary (a list snapshot would invent an order),
and `.get`/`.append`-style foreign methods (faithful
`AttributeError`s). A set used as a dict key or set element is
CPython's faithful `unhashable type: 'set'` `TypeError`
(`keyHasInstanceRef` answers false — never the loud identity-hash
channel, because CPython really does refuse).

**Fragments.** `set(…)` calls leave `Expr.heapFree` (allocation, and
a generator argument drains); the membership/len/truthiness readers
were already heap-side. `worldInv`'s builtin walk rewrites the `set`
branch away via the fragment's `fname != "set"` conjunct, mirroring
`sorted`.

Acceptance: `Examples/python/set_lab` (checks-only): construction
from every admitted iterable including an infinite-free generator
drain, bool/int dedup, tuple elements (the Position shape),
membership both ways, `len`/truthiness on empty and nonempty,
unhashable element AND probe `TypeError`s, and the loud frontier
(`iter_is_loud`, `sorted_is_loud`) pinned as refusals.

## Exceptions (bound() arc pass 2 — DESIGN ONLY, nothing built)

The deferred non-mechanical blocker, designed before any line of
implementation, per the standing discipline. NOTHING in this section is
implemented; no tier claim changes until a build commit says so.

**Scope facts from the shipped file, established first.** (1) The whole
in-file exception surface is three constructs: `class Stop(Exception):
pass` (line 310), `raise Stop` inside `bound()` (line 332), and
`main()`'s `try: import sys, tools.uci … except ImportError: pass`.
(2) The `raise Stop` is GUARDED: `if self.deadline is not None and
self.nodes % 2048 == 0 and time.time() > self.deadline` — and the
in-file driver NEVER sets `deadline` (`__init__` sets `None`; only the
external `tools/uci.py` assigns it). Under `deadline = None` the
`and`-chain short-circuits at its first conjunct, so the raise AND the
`time.time()` call are dynamically dead: a deadline-less `bound()`
needs neither exceptions nor time to run faithfully. (3) The one
in-file `try`/`except` wraps an IN-FUNCTION import, which is loud for
independent reasons (imports execute only under the G1 whitelist at
module top level), and `main()` is interactive-I/O driver code, not a
proof target. (4) The catcher for `Stop` lives OUTSIDE the file
(`tools/uci.py stop_softly`: `try: yield from gen; except Stop: pass`).
CONSEQUENCE, recorded honestly: exceptions gate the DEADLINE story and
corpus completeness, not the deadline-less `bound()` theorem — the
module-init padding loop (`pst` poisoned, so `pos.value` refuses on the
shipped file) blocks that theorem harder than exceptions do.

**What already exists and was built for this.** The `Run`/`Res` channel
carries `.exn (e : PyErr)` with the frame state RETAINED — the H1 core
decision "state retained on `.ok` AND `.exn`" is exactly CPython's
unwinding semantics (mutations up to the raise persist; callee locals
are discarded with the callee frame; the caller's threaded state at a
propagated `.exn` is the state at the raise). Builtin raises are
faithful throughout the tier, `==>!`/`Raises` is a stated judgment, and
the leanpy boundary already renders a class line per `PyErr` kind. What
does NOT exist: user exception classes, `raise`, `try`/`except`, and
exception INSTANCES as values.

**Representation: class-identity exceptions, no payload.**
`PyErr.user (cid : ClassId)` — a raised user exception IS its class
identity. The admitted class shape is recognized at ingestion, like
namedtuples: `class N(Exception): pass` EXACTLY (single base literally
named `Exception`, body `pass`/docstring only, no methods) — the
`Stop` shape. Such a class is an exception NAME, not an instantiable
object: `N()` as a value, attributes, `raise N(args…)` with arguments,
`raise <expr>` of anything but an admitted class name, `raise … from`,
and the bare re-raise `raise` all refuse loudly. `raise N` maps to
`.exn (.user cid)` — CPython's implicit no-arg instantiation of an
empty subclass is observationally the class identity as long as the
instance can never be INSPECTED, which the refusals above guarantee.
The H3 dunder guard is untouched: an exception class is a THIRD
recognized class kind (plain / ntBase / exc), demoted to today's loud
representation by any deviation from the exact shape.

**`try`/`except`: structure and semantics.** `Stmt.tryStmt body
handlers orelse finalbody` structured by the extractor; the v0 tier
admits EXACTLY one handler, naming one admitted exception class, with
NO `as` binding, empty `orelse`, empty `finalbody` — everything else
(multiple/bare handlers, tuple patterns, `as e`, `else`, `finally`)
stays structured-but-loud. Evaluation composes on the existing `Run`:
run the body; `.ok` skips the handler; `.exn (.user cid)` with cid
matching the handler's class runs the handler FROM THE RETAINED STATE
(no rollback — CPython); any other `.exn` propagates. Matching is
IDENTITY on `ClassId`: with bases beyond `Exception` refused there is
no hierarchy to walk. `except Exception:` is REFUSED in v0 (it would
catch builtin `PyErr`s and change every faithfulness story); matching
a BUILTIN exception name (`except ImportError:` — the `PyErr` kind ↔
name table the leanpy boundary already owns) is the recorded first
extension, not v0. Handler flow is ordinary flow (`break`/`return`
inside a handler route as anywhere); nested `try` needs no design —
structural recursion composes, and an exception raised INSIDE a
handler propagates (CPython, chaining refused with `from` above). No
new mutual-block member: `tryStmt` is an `execStmt` arm.

**The generator decision (the one real semantic point).** An exception
propagating out of a resume must CLOSE the generator: CPython marks the
frame finished, and every later `next()` raises `StopIteration`.
`stepIter` therefore routes a body `.exn` outward AND sets
`status := closed` — never `suspended` (a resumable post-exception
frame is unfaithful) and never stuck `running` (a permanent fake
`ValueError`). OBLIGATION RECORDED: today builtin `PyErr`s can already
fire inside a step — pin the CURRENT status-after-exn behavior with a
differential row BEFORE building, and fix it WITH the tier if it
diverges. `execForGen` needs nothing: `Run.bind` already propagates the
step's `.exn` out of the loop. A `yield` INSIDE a `try` body would make
`tryStmt` a suspendable construct needing its own `GenFrame` — REFUSED
in v0 (`genPlan` has no try frame; the extractor flags a generator
whose `yield` sits under `try`), and nothing in the shipped file does
it (`moves()`/`gen_moves`/`search` all yield outside `try`).

**Fragments and proof layer.** `raise` of an admitted class and
`tryStmt` over heap-free subtrees allocate nothing — both can stay IN
`heapFree` (the exception value is an immediate). `==>!` already
states raising runs; no new judgment. `fuelMono`/`worldInv` gain
ordinary `execStmt`-arm cases, no appended conjuncts.

**Acceptance staging (design).** A lab example (`exc_lab`):
raise-catch roundtrip; mutations-before-raise visible in the handler
(the state-retention covenant observable); non-matching class
propagates; an exception crossing a generator resume closes the
generator (the `next()`-after-exn row); the refusal battery (`as`,
`finally`, `else`, args on raise, `raise` bare, `except Exception`,
value raise, yield-under-try). Corpus script with a top-level
try/except once the shell learns the statement. THEN the sunfish
shapes: `Stop` recognized on the shipped file's census, and a
lab-scale deadline capstone — a MiniSearcher raising on a NODE-COUNT
budget (`if self.nodes > limit: raise Stop`) consumed through a
driver `try`/`except Stop`, which exercises the full raise-through-
resume-into-handler path while leaving `time.time()` exactly where it
is: deferred, awaiting its own recorded abstraction decision.

**Explicitly NOT decided here:** the `time.time()` abstraction,
`except Exception`, builtin-name matching, `finally`, exception
payloads/`as` bindings. Each needs its own recorded decision.

## Heap well-formedness (explicit invariant)

Every semantic dereference establishes `a < heap.size` — never `getD`,
never an `Inhabited Obj` fallback, never a silent arbitrary object.
Define `Heap.WF`, `RVal.WF : Heap → RVal → Prop`, `Obj.WF`, and prove:
empty world WF; allocation fresh + preserves old lookups; update
preserves size and other addresses; every interpreter operation preserves
WF on decided outcomes; freeze/equality dereference only valid addresses.
Keeping refs out of public `Val` is what makes malformed roots
unconstructible.

Garbage: unreachability is unobservable **through `CallsTo`** (no
`__del__`/`id()`/weakref — loud). The claim is scoped: a future raw
`CallsIn` surface exposes worlds for semantics/VC purposes and is NOT
observationally abstract; if an abstract stateful public surface is ever
wanted, it must expose only named reachable roots and frozen
observations, or quotient heaps modulo renaming and garbage.

## Effects are data (owner-directed addition, 2026-08-06)

The `leanpy` script-runner direction (run ARBITRARY Python files under
the Lean semantics; differential-test whole programs — stdout + exit
status — against the pinned CPython 3.9; make the completeness goal an
empirical corpus metric with loudness as telemetry; capstone: sunfish.py
playing identical chess under `leanpy`) fixes the effect representation
NOW, so it is a field, not a refactor:

* **stdout is `World` data**: `World.stdout : List String` — chunks in
  emission order, appended at the tail. `print` becomes a tier builtin
  appending to it when module execution lands (H1-1 writes nothing; the
  arms stay loud). Observation: the runner prints the accumulated chunks
  after the run; proofs may speak about it through the future stateful
  surface (`CallsIn`-style), never through `CallsTo` (which erases the
  world).
* **exit status is the RUNNER boundary**, not a world field: the module
  run's outcome maps to the process exit code (`ok` → 0, `exn` → the
  CPython-conventional nonzero + traceback-class line, `unsupported` /
  `timeout` → distinguished codes that the differential driver treats as
  LOUD, never as agreement).
* **argv is a marshalled global** (`sys.argv` shape) supplied at world
  initialization when the `sys` tier lands — a stub note, not a field.

`leanpy` v0 (post-H1-core): module-level execution of current-tier
scripts, first-unsupported-construct reporting, stdout diff vs python3.9,
wired into the harness as a script-corpus mode. `Module`'s
functions/topLevel split loses `def`/assignment interleaving — v0 must
detect and refuse interleaving-sensitive scripts loudly (the ordered
`ModuleItem` representation stays the fix, §module initialization).

## Module initialization (decision)

H1 keeps **closed-function semantics**: `callFunction` does not pretend
to import a module. The fresh world's `globals` are initialized from the
G1 constant pass (top-level constant bindings in source order; everything
else loudly absent/incomplete as today) — extended at H1 to admit dict
literals so `piece = {…}` and `MATE_LOWER/UPPER = piece["K"] ∓ 10 *
piece["Q"]` initialize faithfully (the G1 evaluator gains the same dict
tier as the interpreter). Faithful fresh-module EXECUTION (imports,
class definitions, arbitrary effects, `def`/assignment interleaving) is
a separate future stage and needs an ordered `ModuleItem` representation
— `Module`'s current functions/topLevel split loses interleaving and is
sufficient only for the closed-function tier. Module-global dicts are
shared across nested calls within one public call and recreated across
two public calls (regression case 15).

### The dirty-name pass (2026-08-09, BUILT — replaces the `complete` flag)

The G1 fold used to carry one boolean, `complete`, and clear it at the
first top-level statement it could not analyse; every LATER binding was
then poisoned. On the shipped `sunfish.py` that first statement is
`import time`, line 12, so *every* module global was poisoned and
`Position.gen_moves` refused at `directions[p]`. The flag conflated two
independent questions, and the fold now answers them separately.

**Poisoned is per NAME.** An out-of-tier top-level statement poisons only
what it may have changed: the names it BINDS anywhere in its subtree
(`Stmt.g1Binds`) and the primaries it STORES into (`Stmt.g1Stores` —
`pst[k] = …` poisons `pst`). Poisoning is an ordinary rebinding to `none`
in the accumulator, so it needs no new state: `lookupG` refuses the read,
a later right-hand side that mentions the name fails with it, and
`resolvedG` shadows the stale value the poisoning replaces. That last
point is load-bearing and was a latent bug: a poisoning entry sits in
FRONT of the value it invalidates, so `resolvedG` must keep only the
latest binding per name (`resolvedGAux`), not merely drop the markers.

**Analysable is per MODULE.** A statement whose binding set cannot be
determined (`g1Binds = none` — an unwhitelisted `import`, a starred or
chained target, an opaque construct) poisons the whole accumulator AND
clears `analysable`. Resolution then reads: bound and clean → the value;
poisoned → loud refusal; absent and the module analysable → the faithful
`NameError`; absent otherwise → loud refusal. The `NameError` is never
invented for a file we did not fully understand. `isModuleDunder` is the
standing exception — `__name__`/`__doc__`/… are bound by the import
machinery, not by any statement, so a miss on one is loud even in an
analysable module.

**Imports are decided by an EXACT-TEXT whitelist**, `benignImportBinds`
(Ast.lean) — the table the namedtuple census already established for its
single member, now shared and extended to the three stdlib imports the
shipped file uses. A blanket "imports are benign" would be a genuinely
wider claim (an import runs code, and a circular one can mutate the
importer). A whitelisted row records whether the model already gives the
bound name a meaning: `count` IS `itertools.count` in `isBuiltinName`, so
G1 binds nothing and resolution falls through to it; `time` is
unmodelled, so it is bound POISONED — loud, never a fake `NameError` for
a name CPython did bind.

On the shipped file this resolves exactly the intended set, kernel-
checked: `time` poisoned; `piece`/`pst` valued, then the
`for k, table in pst.items()` loop poisons `pst`/`k`/`table`/`padrow`, so
`K_MID = pst["K"]` stays correctly poisoned; and `A1/H1/A8/H8`,
`initial`, `N/E/S/W`, `directions`, `MATE_LOWER`/`MATE_UPPER`, the search
constants all resolve. The module is `analysable`. `Position.gen_moves`
then runs on the shipped file and yields CPython's 20 opening moves in
CPython's order.

**RECORDED GAP, owner-visible.** The scan is syntactic, so it does not
see a mutation performed by code the statement CALLS: a top-level
`foo()` whose body runs `tbl["k"] = 1`, or an alias taken inside a
callee, mutates a table that stays clean here. The hazard is NOT
introduced by this pass — the old `complete` flag never guarded mutation
either, only later bindings — but more names now resolve, so more rides
on it. Two named pieces close it and neither is built: G1 is IMPORT
semantics, so an `if __name__ == "__main__":` guard is statically dead
and need not be analysed; and with a purity whitelist for the calls that
remain (`dict`/`sum`/`tuple`/`range`, namedtuple construction) any other
call could soundly poison every ref-carrying name.

**The `leanpy` script runner folds the PREFIX VIEW only (2026-08-10
fix).** Poisoning is RETROACTIVE (the marker shadows the earlier value),
which is exactly right for the closed-function surface — every top-level
statement "already happened" before the call — and exactly wrong for the
statements `runScript` is about to EXECUTE: folding the live suffix too
poisoned prefix-bound names the suffix rebinds or stores into
(`n = n + 2` in a top-level loop, `tt[1] = 11`), breaking the v0
shared-heap exemplars (fib_loop/tt_script/list_script, bisected to the
dirty-name commit 6a79764). `runScript` therefore builds its world from
`mPre` (`topLevel := g1Prefix …`) and threads `mPre` through the
executor; the widened `suffixConsistent` guard (any suffix assignment to
a function-read name is loud) keeps the prefix view sound — see
Script.lean's header for the argument.

### Module-init EXECUTION (2026-08-10, pass 3 — the padding loop)

The named target: the shipped file's

```python
for k, table in pst.items():
    padrow = lambda row: (0,) + tuple(x + piece[k] for x in row) + (0,)
    pst[k] = sum((padrow(table[i * 8 : i * 8 + 8]) for i in range(8)), ())
    pst[k] = (0,) * 20 + pst[k] + (0,) * 20
```

plus `K_MID = pst["K"]` and the `K_END` comprehension — module-level
statements that MUTATE prefix globals, which the fold can only poison.
Two standing facts shape the design:

1. **Function-frame name resolution stays on the static table.** The
   covenant that keeps world-symbolic theorems provable (`rotate_callsIn`
   holds for EVERY `w` because a static read reduces at a symbolic
   world). And the static table CANNOT contain execution results: 
   `moduleGlobals → execStmt → evalExpr → moduleGlobals` is not even
   definable (the interpreter reads the table, so the table cannot be
   defined through the interpreter).
2. **`World.globals` is the recorded seam** ("the future
   `global`-statement tier must switch reads to it"). Init execution is
   exactly the fragment that needs the switch: CPython executes a
   module's top level in a frame whose locals ARE its globals, live.

**The resolution chain gains ONE arm.** `locals → static table → …` is
unchanged except at the STATICALLY-POISONED marker (`some none`), which
now consults `st.world.globals` — the LIVE view — before refusing:
hit → the value (a `.ref` in call position dispatches as a closure call,
mirroring the locals arm, `funsHeapFree`-guarded); miss → the same loud
refusal as today. Soundness of static-first: the dirty-name pass poisons
every name an out-of-tier statement BINDS or STORES-into, and the exec
tier attempts exactly (a subset of) the fold-refused statements — so a
name the static table VALUES was provably never touched by an executed
statement, and a name execution DID touch is provably poisoned, i.e. the
static table is never stale and the live view is consulted exactly where
it is the only truth. Backward compatibility is exact: a pre-pass
world's `globals` (`resolvedG` — markers dropped) cannot contain a
poisoned name, so the new lookup MISSES and the arm decides the refusal
it always decided.

**The pipeline** (`initWorld`, one ordered walk; the pure fold
`moduleInit`/`moduleGlobals` is UNCHANGED and stays the static table):

* each statement first takes the PURE FOLD STEP on the LIVE state — the
  same `globalsStep` code, so a statically-valued binding is live-equal
  by construction (one evaluator, not two that must agree);
* a fold-REFUSED statement gets the EXEC ATTEMPT: `execStmt` at the
  fixed `initExecFuel` in a frame `⟨liveWorld, []⟩`, new locals FLUSHED
  into `world.globals` after each statement (CPython: top-level
  bindings are globals). The one construct `execStmt` cannot express —
  `for k, v in d.items():` — gets a control SHELL (the Script.lean
  discipline): index iteration over the dict's LIVE entries with the
  per-step SIZE check — value updates visible mid-iteration, insertion/
  deletion the faithful `RuntimeError` (H1 acceptance row 10, finally
  live). The shell handles `.items()` ONLY here; everywhere else the
  attribute call keeps its loud refusal (recorded gap);
* an attempt that refuses, raises, or times out ROLLS BACK to the
  pre-statement state and the walk continues — the static poisoning
  already recorded the loss, so every later read of what it would have
  bound is loud. (An `.exn` here is imprecise the same way the fold's
  existing `.exn` arm is: CPython would abort the import; the model
  poisons and continues, loudly downstream. Pre-existing wart, now
  recorded.)

**The DIVERGED discipline (static fold).** From the first exec-attempted
statement on, the two heaps may differ (execution commits allocations
the pure fold never sees), so a later STATIC binding would carry
addresses into the wrong heap — and a static scalar computed by READING
the (stale) fold heap could contradict the live world. The fold
therefore marks divergence at the first statement the executor would
attempt, and after it values a binding only when the RHS is HEAP-PURE
(constants, statically-clean names whose values are ref-free, operators
over those — no subscript, attribute, call, display) and the result is
ref-free; everything else takes the poison marker and resolves through
the live view. On the shipped file that keeps `A1/H1/A8/H8`, `initial`,
`N/E/S/W` and the search constants STATIC (symbolic-world-friendly)
while `pst` (mutated), `K_MID`, `K_END`, `directions`, `MATE_LOWER/
UPPER` move to the live view — same values, one heap.

**Module-level lambdas: the H7 fork DISSOLVES.** The pass brief flagged
`padrow = lambda …` rebound per iteration as a collision with the H7
never-rebound admission. The honest answer is that no capture exists to
admit: CPython's symtable gives a module-level lambda ZERO freevars —
every free name in its body is a GLOBAL, read dynamically at call time
(`piece`, `k` compile to `LOAD_GLOBAL`). So the extractor structures a
module-scope single-target `name = lambda …` assign (top level, or
directly in a top-level `for` body) as the H7 `NestedDef` with
`captures = []`; execution allocates the ordinary `Obj.closure` (fresh
identity per iteration, exactly CPython); and the body's global reads go
through the poisoned-arm live view AT CALL TIME — by-reference through
the world, no snapshot anywhere, so there is nothing for a rebinding to
diverge from. The H7 admission census is untouched (it governs
function-scope captures, which are cells).

**Genexp lowering: unchanged, justification strengthened.** A
module-level genexp's free names stay GLOBAL READS in the synthesized
body (never by-value captures), and under the live view those reads are
by-reference through the world at RESUME time — CPython's cell-free
module-scope semantics exactly. The padding genexp reads `padrow`/
`table` (poisoned → live view) per drain step; the lambda-internal
genexp reads `piece`/`k` the same way.

**New value tiers riding the pass** (general — function bodies too;
each construct differential, refusals loud):

* **tuple/namedtuple SLICES** (`table[i*8 : i*8+8]`): CPython's
  `tuple.__getitem__` — a namedtuple slice is a PLAIN tuple. In-model
  tuples are immediate values, so the slice allocates nothing; LIST
  slices stay loud (they allocate a heap object).
* **sequence repetition** `tuple * int` / `int * tuple` (bool coerces;
  `n ≤ 0` → empty). List/str repetition stays loud, recorded.
* **`sum(iterable[, start])`**: the element fold IS `evalBinOp .add`
  (so int and tuple sums are exactly Python's `+`, mixed types its
  faithful `TypeError`); a str `start` is CPython's special
  `sum() can't sum strings` `TypeError`; a generator argument DRAINS
  (guarded on `moduleGenFree` like `max`/`min`, keeping `sum` in the
  heap-free fragment).
* **`tuple(iterable)`**: str/tuple/namedtuple(class-erased)/boundary
  list/heap list(snapshot — CPython copies)/range/generator(+guard);
  dict and set receivers stay loud (order).
* **`range` as the IMMEDIATE `RVal.rangeV lo hi step`** (construction:
  1–3 int args, `step = 0` the faithful `ValueError`). A range is
  IMMUTABLE and re-iterable, so materialization-per-use is exact and
  the value form avoids heap/boundary churn: `for`-iteration and the
  draining consumers materialize FUEL-BOUNDED (a huge range times out,
  never hangs); `len`/truthiness exact. Everything else is loud or
  faithful: `==` loud (CPython compares ranges as sequences — not
  guessed), dict-key/set-element loud via `keyRefusal` (ranges ARE
  hashable in CPython — never a fake unhashable `TypeError`), the
  boundary loud, `next()` the faithful `not an iterator` `TypeError`.

**What stays out, loudly:** `.items()` outside the init shell;
`dict.keys/.values`; the call-mutation gap where an attempt was REFUSED
(rollback restores the un-mutated heap — the old syntactic gap,
unchanged); executed calls CLOSE the gap for their own effects (the
mutation is real in the live heap). Top-level `if`/`while` ARE
attempted (a `while` executes — `g1_lab.read_m` flipped from refusal to
CPython's value); the `__main__` guard still never runs its body:
`__name__` is loud, so the attempt refuses and rolls back, which is
exactly right until the recorded import-semantics decision.

**As built (2026-08-10/11), the deltas the implementation forced:**

* **Per-statement PREFIX VIEWS.** The executor cannot thread `m` itself:
  `evalExpr` resolves globals against the FULL static table, so an
  executed statement could read a binding made by a LATER statement — a
  FUTURE value, silently wrong (`X = Y + 1` before `Y = 5` must be
  CPython's import-time `NameError`). `initFoldLive` therefore threads
  `{ m with topLevel := done }` — the statements already processed — so
  static resolution is sequential-correct, and the ABSENT arm (not just
  the poisoned one) consults the live view before the `NameError`
  decision: the running suffix's own bindings are statically absent
  under a prefix view. Post-init both arms are equally correct (the
  live view carries every binding, valued identically).
* **Failed attempts poison the LIVE accumulator too** (`globalsDirty`
  on the live side): rollback alone would let the poisoned-arm consult
  resurface the PRE-statement value of a name the failed statement
  rebinds — the marker keeps stale reads impossible on both views.
* **The dirty-name pass gained the DIVERGED flag** (4th component of
  `moduleInit`): set at the first exec-attempted statement
  (`g1ExecCandidate` — def/for/if/while/augAssign/bare-call statements
  and fold-REFUSED assigns; `.unsupported` statements are NOT
  candidates, `execStmt` refuses them, so imports never diverge).
* **`Module.heapFree` gained a FOURTH conjunct, `topLevelDefFree`**,
  and every closure-call arm's guard is now
  `funsHeapFree … && topLevelDefFree m`: module init can bind closures
  into the live view, so a call of a statically-poisoned/absent name
  can dispatch `callClosure` — the fragment must exclude modules whose
  TOP LEVEL creates closures, or `worldInv` would meet arbitrary code.
  (Also the guard fix that makes `init_lab.call_pad` — a module lambda
  called from a function body, post-init — dispatch rather than
  misfire into the not-callable `TypeError`.)
* **Executed statements may not rebind builtins or def/class/namedtuple
  names** (`initBindable`, checked at flush): those resolution arms
  fire BEFORE the live view, so a live shadow would be silently
  ignored. Loud, attempt rolls back.
* **A keyword call of a live binding is loud** (the kwargs tail
  consults the live view only to REFUSE): closure keywords were already
  out of tier, and the alternative was a fake `NameError`.
* **The fold's `.exn` arm stays imprecise as before** (poison and
  continue, where CPython aborts the import) — now recorded; the items
  shell's `RuntimeError` on insertion IS faithful and pinned
  (`init_lab`'s hand-built `insLoop`), with rollback leaving the table
  poisoned, never half-mutated.

## Staging (amended)

* **H0 (landed): representation.** Structured `Dict`/`Attribute`.
  STILL NEEDED for H1 representation: membership `in`/`not in`
  comparisons, dynamically-decided generic `is`/`is not`, subscript
  STORES in tier, `KeyError`/`RuntimeError`/`RecursionError` in `PyErr`.
* **H1: the corrected-core threading + dicts.** One commit for the
  `RVal`/`World`/`FrameState`/`Run`/`callIn` re-shape with all heap
  features still loud (observable behavior unchanged; `fuelMono` re-
  proved over `Run`; the VC layer re-based with the state-aware err arm
  and the `CallsIn`-consuming call rule designed in), then a second
  commit enabling the dict inventory + differential rows + the `sf_pst`
  acceptance example (pst/piece reads, real MATE constants).
* **H2: lists to the heap.** `RVal.listV` → `Obj.list`; public
  `Val.list` STAYS (snapshot form). In-place list ops enter the tier;
  the stateful judgment is exposed (see above). STATUS 2026-08-07: the
  in-world half is BUILT (§list semantics; `CallsIn` list proofs in
  `Examples/python/sf_hist`); the BOUNDARY FLIP — arguments through the
  heap-threading `RVal.thawH` instead of the transitional `listV` value
  form — is built-but-not-wired, pending the list-example proof rebase
  (docs/backlog.md). Until the flip, mutating a boundary-passed list is
  loudly refused (never wrong), and `RVal.listV` survives as the
  boundary-argument form and the pure proof-layer vocabulary
  (`RVal.thaw`'s image of `Val.list`, bridged by `thawH_of_listFree`).
* **H3: classes — BUILT (2026-08-08, §class semantics).**
  `Obj.instance (cls : ClassId)` with ClassId = the class-table index,
  NOT the name; methods flattened to qualified-name functions through
  `callIn`/`CallsIn`; the dunder guard makes default-object semantics
  faithful; `Searcher`'s tables and the cross-call-state surface are
  proved (`Examples/python/sf_searcher`: write/read/chained/pinned).
  Class objects with heap identity and mutable class attributes remain
  future work (class-as-value is loud); `namedtuple` is BUILT
  value-like (2026-08-08, see §class semantics — immediate
  `RVal.ntuple` values, ingestion recognition, loud boundary).
* **H4: generators — BUILT (2026-08-09, §generator semantics).**
  `Obj.generator` frames carry a DEFUNCTIONALIZED CONTINUATION (a stack
  of `GenFrame`s — structural suffixes of the body plus each loop's
  residual state) and a status (created/suspended/running/closed).
  Generator functions, `for`-consumption, `break`-suspension, `next`
  with and without a default are live (`Examples/python/gen_lab`);
  generator EXPRESSIONS are structured but not yet lowered, and
  `sorted(key=)` remains orthogonal. sunfish's `moves()` consumed
  lazily by `bound` stays the capstone.
* **H5: sets — BUILT (bound() arc pass 1, §set semantics).** The
  order-blind honest subset (construction/dedup, membership, len,
  truthiness); iteration order stayed OUT (refused loudly), so the
  language-vs-CPython hash-order question never needed deciding.

## H1 acceptance: minimum differential + proof regression set

1. `e = d; e["x"] = 1; return d["x"]` (local alias mutation).
2. Callee mutation visible to caller (via `callIn`).
3. Two separate dict literals have different identity.
4. `True`/`1` address one entry; original key retained.
5. Duplicate equal literal keys: first position/key, last value.
6. Dict equality ignores insertion order.
7. Self-cyclic dict equals itself (identity shortcut).
8. Two corresponding self-cyclic dicts: `RecursionError` (or the
   documented cycle-specific unsupported).
9. Unhashable lookup/membership raises on an empty dict.
10. Value-update during iteration OK; insertion → `RuntimeError` at the
    next step.
11. Subscript assignment evaluates RHS before target primary before key.
12. Returned tuple containing a ref: recursively frozen or rejected per
    referent.
13. Shared acyclic output ≠ cycle.
14. Low fuel → `.timeout`; more fuel → the decided equality/freeze
    result (never `.unsupported` from exhaustion).
15. Module-global dicts shared across nested calls, fresh across public
    calls.
16. Mutations and bindings before an internal exception survive in the
    exception state.
17. A stateful spec observes an in-place mutation of an argument even
    when the function returns `None`.
18. WF preserved by allocation, lookup, update, call, iteration.

## Proof-layer covenants (restated)

1. `fuelMono` over the `Run`-typed mutual block; public mono derived
   through the wrapper decomposition.
2. Frozen recursion points: **`callIn`**, `execWhile`, `execFor` (+ the
   H4 stepper); `.eq_n` one-step unfolds remain the manual route.
3. Kernel-reducible structural recursion everywhere (`#py_check`).
4. `#print axioms` stays `[propext, Classical.choice, Quot.sound]`.
5. Loudness: `.unsupported` is fuel-independent; `.timeout` is the only
   exhaustion outcome; nothing is ever silently wrong.
