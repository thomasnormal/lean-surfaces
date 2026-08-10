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
  discipline, plan decided BEFORE arguments): `.swapcase()` and
  `.isupper()` on ASCII strings (Lean core's `Char` case maps ARE the
  ASCII maps, agreeing with CPython exactly there; a non-ASCII string
  refuses loudly — the Unicode tables are not guessed), and
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
* **H5: sets** (explicitly staged; iteration order raises the
  language-vs-CPython question — decide against the 3.9 oracle then).

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
