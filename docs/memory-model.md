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
* **Class CREATION is an effect** (2026-08-12, found by `tools/leanpy`,
  BUILT — normative). The tier answers "can an instance exist?"
  (`ClassDefn.ok`, the dunder guard above) and, since leanpy runs whole
  programs, it must separately answer **"does executing the `class`
  statement do anything observable?"** CPython evaluates the bases and
  runs the class body THERE; the model builds `ClassDefn` at ingestion
  and executes no class body ever. For most classes that is invisible,
  but `class C: print("x")` printed under CPython and not under the
  model — a WRONG ANSWER, not a refusal, and the only silent divergence
  the first completeness survey turned up (`class C(base())`, where the
  base expression prints, is the same hole through the other door).
  **`ClassDefn.creationPure`** is therefore a SECOND, independent flag:
  the extractor emits the structured verdict `creation_effects`
  (unrecognized base / metaclass keyword / decorator / any class-level
  statement beyond a method, `pass`, a docstring, or an attribute bound
  to a LITERAL), ingestion re-checks the body it already parses
  (`classBodyStmtPure` — never trust a field you can verify), and a
  demoted namedtuple/`Exception` base clears the flag too, because the
  base expression the census rejected is no longer one the model
  reproduces. `runScript` refuses a module containing any non-pure
  class (`classesCreationPure`, the FIRST admission check): a script
  never silently skips a class-creation effect. The two flags are
  deliberately independent — `class Tag: kind = "tag"` is creation-pure
  (a literal binding prints nothing) yet stays UNINSTANTIABLE, so a
  program that defines it runs and `Tag()` still refuses
  (`harness/scripts/cls_data_script.py` pins both halves;
  `cls_effect_script.py` pins the refusal). The closed FUNCTION surface
  is untouched: it makes no claim about module stdout, and the one
  class-body effect that could reach a call's result — a class-level
  `global` — is already tracked by `ClassDefn.hasGlobal`.
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

## Exceptions (designed in bound() arc pass 2 — BUILT 2026-08-11, pass 4)

The deferred non-mechanical blocker, designed before any line of
implementation, per the standing discipline. BUILT in pass 4 exactly as
recorded below, with the as-built deltas at the end of this section
(each one a narrowing or a mechanical necessity, never a widening).

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
diverges. OBLIGATION DISCHARGED (2026-08-11, pass 4, pre-build):
`gen_lab.bad_first`/`bad_second` pin the faithful RAISE (the whole call
propagates CPython's `ZeroDivisionError` — differential rows), and the
raw `#guard` in `gen_lab/spec.lean` pins the STATUS divergence exactly
as this section predicted: the stepper sets `running` on entry and the
`.exn` path never clears it, so a third step is the fake "generator
already executing" `ValueError` where CPython closes the frame
(`next()` → `StopIteration`). No differential row can observe the
divergence yet — nothing in tier survives the second step — so the pin
is Lean-side, and the fix lands WITH the tier (the build flips the pin
to `closed` and adds the `try`-driven differential row in `exc_lab`). `execForGen` needs nothing: `Run.bind` already propagates the
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

**As built (2026-08-11, pass 4) — the deltas the implementation
forced, each recorded with its reason:**

* **`PyErr.user cid name`** — the constructor also CARRIES the class
  name. Identity (handler matching, `BEq`) is decided by the `cid`
  alone within any one module (the name is determined by it); the name
  exists so the boundary (`errName`, Main.lean; the leanpy class line)
  can render CPython's `type(e).__name__` without threading the module
  through `PyErr`.
* **Recognition rides `exception_base`** (extractor marker, the
  `namedtuple_base` pattern): the exact shape `class N(Exception):
  pass` (single base literally named `Exception`, no keywords/
  decorators, body only `pass`/docstring, no methods) suppresses the
  "bases (inheritance)" refusal and marks the class; ingestion then
  runs a module CENSUS — every top-level statement bind-analyzable
  (`stmtBinds`, the namedtuple census's walker) and `Exception` bound
  NOWHERE (no top-level bind, no def/class/namedtuple of that name, no
  `has_global` anywhere that could rebind it) — and on ANY failure
  demotes the class to the ordinary loud state (`isExc := false`,
  `ok := false`, exactly the `ntBase` demotion discipline): a shadowed
  `Exception` must not recognize as the builtin one.
* **`Stmt.raiseStmt (exc cause : Option Expr)`** is structured in FULL
  generality (bare `raise`, `raise <expr>`, `raise … from …` all parse);
  EVALUATION admits exactly `raise N` where `N` names an admitted
  exception class, everything else the loud refusals of the design.
* **`Stmt.tryStmt body excName handler tryUnsupported`** carries the
  v0 single-handler shape plus the `callUnsupported`-style reason
  field: the extractor fills `try_unsupported` for every out-of-v0
  feature (multiple/bare handlers, tuple pattern, `as`, `else`,
  `finally`, a non-name handler class expression) and execution refuses
  with that reason — structured-but-loud, one channel.
* **The handler class resolves STATICALLY-FIRST**: `except N:` refuses
  loudly (never runs the body) unless `N` is an admitted exception
  class of the module. CPython evaluates the handler expression only
  when an exception arrives, so a module whose body never raises could
  run under a bogus handler name — the tier refuses it up front. Loud,
  never wrong; the faithful late-`NameError` story is deferred with
  builtin-name matching.
* **`tryStmt` is OUT of `Stmt.heapFree`** (the design said both new
  statements could stay in; the PROOF disagrees for `try`): `worldInv`
  is an `.ok`-only invariant, and the handler resumes from the BODY'S
  RETAINED `.exn` STATE, about which `Run.OkW` says nothing — so the
  handler's decided world cannot be tied to the input world through the
  existing induction. Conservative `false`, zero loss today (every
  try-bearing target module has classes and is already outside the
  fragment). `raiseStmt` stays IN: it never decides `.ok`, so its
  invariance is vacuous, as designed.
* **`stepIter` closes on exn through `Run.bindE`** — a new bind
  combinator with an explicit exn continuation (`ok`/`exn` both carry
  state; `timeout`/`unsupported` pass through), so the close-on-
  exn-through-resume update composes without restructuring the stepper,
  and `fuelMono` glues it with one new congruence lemma
  (`Run.le_bindE`). The `gen_lab` status pin flipped exactly as the
  discharge note predicted: third step after the exn is now exhaustion
  (`closed`), and `exc_lab.gen_closes` is the try-driven differential
  row.
* **`genPlan` gained the explicit `tryStmt` fork**: a try WITHOUT yield
  delegates to `execStmt` whole (its internal raise/catch is invisible
  to the frame stack); a try WITH a yield anywhere inside is the
  refused suspendable-`try` case, with the precise reason. The census
  walkers (`hasYield`/`hasGenDef`/`defFree`/`g1Binds`/`g1Stores`/
  `allNames`/`assignedNames`, and Json's `stmtBinds`/`bodyAssigns`/
  `stmtRefs`) all see through `tryStmt` body AND handler — wildcard
  arms would have silently mis-censused hand-built modules.
* **Top-level `raise`/`try` are exec candidates** (`g1ExecCandidate`):
  the init pipeline attempts them; a top-level raise `.exn` rolls back
  and poisons (the fold's recorded `.exn` imprecision, unchanged).

## Wall-clock time (`time.time()`) — the recorded abstraction decision (pass 4, 2026-08-11)

The deferred second non-mechanical blocker, decided and recorded BEFORE
its battery rows landed. The decision: **the wall clock has NO value in
the model — `time.time()` is an impure builtin whose EVALUATION refuses
loudly, so it may APPEAR in code and is sound exactly when dynamically
dead.** No stub, no frozen clock, no "returns 0": any numeric answer
would be silently wrong somewhere, and the model never guesses.

The MECHANISM is the one already in place, now claimed as the
abstraction rather than an accident: `import time` sits on the exact
benign-import whitelist (`benignImportBinds`, Ast.lean) with
`modelled = false`, so G1 binds `time` POISONED — CPython did bind the
name, so a read must never be a fake `NameError` — and any evaluation
that reaches the name (in particular the receiver of `time.time()`)
refuses loudly with the poisoned-name message naming `time`
("module-level value of 'time' is outside the G1 tier"): the wall
clock outside the tier, refused at the exact moment code would consult
it. (A bespoke `time.time`-shaped call arm with a prettier message was
considered and rejected: it would special-case the largest match in
`evalExpr` for zero semantic content — the refusal is already
evaluation-time, already loud, already names the clock.)

Soundness on the shipped file is the SHORT-CIRCUIT: the only reach is
`bound()`'s guard `self.deadline is not None and self.nodes % 2048 == 0
and time.time() > self.deadline`, and the in-file driver never sets
`deadline` (`__init__` binds `None`), so the `and`-chain dies at its
first conjunct and the wall clock is never evaluated. The battery pins
BOTH directions in `exc_lab` (the deadline story's home):
`time_dead` — the guard shape with `deadline = None` runs to completion
(differential MATCH: the short-circuit keeps the clock dead);
`time_live` — `deadline` set, evaluation reaches `time.time()` and
refuses loudly (whitelisted row + the message pinned by `#guard`).

The same doctrine covers every impure stdlib call the file can reach:
there are no others in tier range today (`main()`'s `input()`/
`sys`/`tools.uci` are driver-side and out of scope; NOTE the recorded
gap that `input` is absent from `isBuiltinName`, so a hand-driven
`main()` run would answer a fake `NameError` before reaching any of
this — pre-existing, backlog).

AS-BUILT DELTA (pass 5, the post-#158 re-pin): the shipped guard is
now `if self.nodes % 2048 == 0 and time.time() > self.deadline: raise
Stop` with `deadline = 1 << 63` — the None test is GONE, so
`time.time()` is dynamically LIVE at every 2048th node and the
soundness story changes from "short-circuit dead" to "refuses at the
frontier": every pinned bound() probe stays under 2048 nodes (max 587
— re-derived from CPython on the new engine), and the frontier itself
is pinned CHEAPLY in the sunfish spec by a searcher whose `nodes` is
pre-set to 2047 through `Heap.update`, so the very next entry is the
2048th — CPython consults the real clock there and continues; the
model refuses loudly at that exact evaluation, one node in (never a
2048-node fresh-searcher run per build). The `exc_lab`
`time_dead`/`time_live` rows are unchanged and still pin both
directions at lab scale.

AMENDED (pass 6, owner-approved): the refusal wall for the exact call
`time.time()` is replaced by the TRACE CLOCK — time as an input, a
clock trace threaded through `World`, popped per call, empty trace a
loud underrun refusal (docs/memory-model.md §the trace clock below).
Everything else in this section stands: the poisoned binding remains
the abstraction for every OTHER impure surface (`time` as a value,
`time.sleep`, any other module attribute), and no reading is ever
invented — readings come from the trace or the evaluation refuses.

## bound() end-to-end (pass 4 capstone — the last mechanical constructs)

Everything `Searcher().bound(pos, gamma, depth)` needs beyond the
exceptions/time landings, designed here before code. Census of the
remaining gaps against the shipped file: THREE constructs.

1. **Attribute augmented assignment** (`self.nodes += 1`). CPython
   order: receiver, attribute LOAD (an `AttributeError` fires before
   the value evaluates), value, binop, attribute STORE. In tier for
   IMMEDIATE old values only — a heap-valued attribute's `+=` is
   in-place mutation through an alias and a boundary-list value would
   silently rebind: both refuse loudly (the name-target discipline,
   verbatim). The read rides `attrReadResult`, the store
   `heapAttrStore`. `Stmt.heapFree` goes `false` for attribute targets
   (the store mutates); subscript/other targets keep their loud arms.

2. **Tuple targets with ATTRIBUTE elements**
   (`self.tp_score, self.tp_move, self.history = {}, {}, set()`).
   CPython: RHS evaluates, unpacks, then the element stores run LEFT TO
   RIGHT, each mutating the heap. All-NAME tuples keep the pure
   `assignToH` path bit-for-bit; a tuple containing anything else takes
   the new heap-threading pair `unpackSeq` (the `assignTo` arity/type
   discipline factored out; heap lists unpack as an eager snapshot) +
   `unpackStoreH` (names bind; attribute elements store through a
   LOCAL-name receiver holding a `.ref` — sunfish's `self.x`; any other
   element or receiver shape refuses loudly). Both are WORKERS and join
   `py_simp`/`interpUnfolds` (the recorded simp-set trap).
   `Stmt.heapFree`: a tuple target stays in the fragment iff it is
   all-names (`targetNames.isSome`).

3. **Genexp admission: body-assigned free names under an immediate
   drain.** The correction's
   `all(depth > 1 and pos.value(m) >= val_lower or … for m in
   pos.gen_moves())` captures `depth` (a parameter the body REBINDS:
   `depth = max(depth, 0)`) and `val_lower` (a plain local) — both
   outside the H4 by-value admission. The drain-gate argument
   (pass 3's `genTargets` precedent) extends: a genexp passed DIRECTLY
   to a draining builtin is created and consumed within ONE expression
   evaluation, and no statement of the enclosing frame can run in
   between, so by-value-at-creation equals CPython's by-reference — for
   ANY frame name, provided it is BOUND at creation. Boundness is the
   real condition (an unbound capture would fake a NameError CPython
   never raises when the iterable is empty), decided conservatively:
   the name is a PARAMETER (always bound), or it has a single-target
   assign / nested-def bind as a DIRECT CHILD of the enclosing body at
   a strictly smaller line (`LowerCtx.boundBefore` — direct children
   execute in order, so a smaller-line direct bind provably ran before
   any statement containing the genexp). Names failing the test leave
   the node un-lowered and loud, as always. (Rebinding between
   iterations of an enclosing loop is harmless under the gate: each
   drain re-captures at its own creation.)

The CAPSTONE this unblocks: `Searcher()` instantiates on the shipped
file (`__init__`'s two tuple-attribute unpacks), and `bound()` runs
END TO END — the table probe (`tp_score.get` under the dict-key
doctrine with `(pos, depth)` keys), the history-set membership, the
nested `moves()` generator with recursion through the captured `self`,
the killer/null/IID prologue, the verbatim ordering line, the fold with
the beta cutoff and the virtual-cutoff validation, the mate/stalemate
correction, and the table store — differentially against CPython at
depths 1-3 from the opening board and midgame/tactical/endgame boards,
comparing the RETURNED BOUND and `self.nodes` (node-count equality is
the lockstep signal: one extra or missing node anywhere in the tree
breaks it). Pinned as `#guard`s in `Examples/python/sunfish/spec.lean`
(the boundary cannot carry a Searcher, so `CallsIn`-style kernel runs
are the surface, as for every shipped-file claim).

## Left shift and bitwise or (pass 5 — the post-#158 file's census gaps)

The engine repo's #158 review rewrote the shipped file (142 clean
lines), and the re-pin census found two integer-op gaps: `1 << 63`
(the deadline sentinel in `Searcher.__init__` — there is no `None`
test anywhere anymore) and `live |= move is not None and score >
-MATE_UPPER` (bound()'s fold). Both are `BinOp` extensions (extractor
`ALLOWED_BINOPS`, `parseBinOpName`, `BinOp.symbol`, `evalBinOp`);
`|=` rides the existing augAssign name path unchanged.

- `<<` is EXACT on all ints as multiplication: `x << n = x * 2^n` for
  `n >= 0` (CPython ints are unbounded; the sign carries through), and
  a negative count is the faithful `ValueError: negative shift count`
  — raised BEFORE any magnitude concern, as CPython does. Bools coerce
  through `asInt` (`True << 2 == 4`, an int) — CPython's bool-is-int.
  Non-int operands keep the faithful TypeError arm.
- `|` must decide BOOLNESS before the int path: `bool.__or__(bool)`
  returns a BOOL (`True | False is True`), while any int operand makes
  it an int (`True | 2 == 3`). So: two bools → boolean or; otherwise
  int/bool operands BOTH `>= 0` → `Nat.lor` (nonneg territory, where
  CPython's unbounded bitwise-or IS the binary or of magnitudes); a
  NEGATIVE operand refuses loudly (infinite two's complement is not
  guessed); non-int operands the faithful TypeError. `live |= <bool>`
  therefore stays a bool through the whole fold, and the battery pins
  the TYPE, not just the value (the harness's typed JSON distinguishes
  bool from int).

AS-BUILT note: `Nat.lor`/`Nat.shiftLeft` kernel reducibility was
verified on the toolchain before the tier landed (a `#guard` probe) —
`<<` is nevertheless computed as `x * 2^n`, keeping the mathematical
reading primary.

## `yield from` (pass 5 — the promotion arm returns to gen_moves)

#158 rewrote gen_moves's promotion loop as
`yield from (Move(i, j, prom) for prom in "NBRQ")`. The tier admits
exactly the statement-position `yield from <genexp>` shape, by
INLINING at ingestion — no delegation machinery:

    yield from (E for x in IT if C₁ if C₂)     -- statement position
      ⇢  for x in IT: if C₁: if C₂: yield E

The rewrite is CPython-exact in tier because (1) a genexp's free names
are read from the enclosing frame at each resume, and during a
delegation the enclosing frame provably cannot run — the inlined loop
reads the same frame at the same points, so even REBOUND enclosing
locals (gen_moves's `i`, `j`) are read identically, with NO capture
analysis at all (strictly better than the by-value admissions: this is
by-reference, verbatim); (2) `IT` evaluates once, at the same program
point (genexp creation = loop start, both at the statement); (3)
exceptions and exhaustion surface at the same points; (4) everything
delegation COULD distinguish — `send`/`throw` through the outer
generator, the inner generator's identity, `.close()` finalization —
is already loudly out of tier.

What inlining DOES change is the frame: the genexp's target binds in
the ENCLOSING frame, where CPython gives it its own scope. Admission
therefore requires the target names to occur NOWHERE else in the
enclosing function body — not read, not bound, not a nested def's name
or capture (`yfNames`, a whole-body census that skips yield-from-
genexp statements' own subtrees). gen_moves's `prom` passes (its only
occurrences are the genexp's own). Two yield-froms may share a target
name: each admission ignores ALL yield-from subtrees, and the second
loop's rebinding is as unobservable as the first's binding. Everything
else stays structured-but-loud: `Stmt.yieldFromStmt` survives
ingestion un-lowered for a non-genexp iterable (`yield from [1, 2]`),
a used-elsewhere target, or an unanalyzable target, and BOTH executors
refuse it with the reason (`execStmt` and `genPlan` — never a silent
skip). A yield-from in EXPRESSION position (its value is the
delegation's return value) keeps falling to `Expr.unsupported`, like
expression-position yield. `Stmt.heapFree` excludes `yieldFromStmt`
(it only occurs in generator bodies, which already evict the module
from the fragment; conservative and simple).

## The walrus filter (pass 7 — the QS ordering line; BUILT)

The re-pin to current engine master hits ONE out-of-tier construct: the
quiescent-search ordering line became

```python
for val, move in sorted(((v, m) for m in pos.gen_moves() if (v:=pos.value(m)) >= val_lower), reverse=True):
```

— a genexp whose FILTER binds `(v := …)` and whose ELEMENT reads `v`
(filter-before-sort: the sub-threshold tail is never sorted, and the
shape is literally the formal model's movesAbove form). Ingestion left
the genexp un-lowered and `bound()` refused loudly at evaluation — the
correct loudness behavior for a missing tier, now closed BY INGESTION
ALONE (zero interpreter changes, zero new AST constructors, zero
meta-theorem arms):

* **Extractor** (`extract.py`): inside a structured genexp's `ifs`, a
  filter of the exact shape `Compare(NamedExpr(Name v, value), [op],
  [rhs])` is emitted as the rewritten filter `Compare(Name v, [op],
  [rhs])` plus a `walrus` binding record `{name: v, value}` on the
  genexp node. A `NamedExpr` ANYWHERE else stays the generic
  unsupported expression — loud, never half-structured.
* **Lowering** (`lowerGenExps`): a walrus-bearing genexp synthesizes

  ```
  def <genexpr@n>(.0, captures…):
      for target in .0:
          v = <value>
          if v <op> <rhs>: yield <elt>
  ```

  — CPython's own compilation of the filter, with `v` an ordinary
  local of the synthesized frame (it joins the target-bound set for
  the capture analysis; the walrus VALUE's free names go through the
  standing capture admission unchanged).
* **The admission — why a frame-local is honest.** PEP 572 scopes a
  comprehension walrus to the CONTAINING function: CPython's `v` leaks
  into the enclosing frame as the drain runs. The frame-LOCAL lowering
  is observationally equal exactly when the enclosing body never looks:
  admitted only if `v` occurs NOWHERE in the enclosing function outside
  walrus-bearing-genexp subtrees (not a parameter, not assigned, not
  read — `walrusForbidden`, collected like `yfNames`), and module-scope
  genexps check the top level the same way. Anything else leaves the
  genexp un-lowered — the loud refusal at evaluation, never a
  wrong-scope guess. On the shipped line `v` lives only inside the
  genexp, so the admission passes; the census-refusal lab row pins the
  exposing direction.

**AS-BUILT (same day):** exactly as designed. `Expr.genExp` gained the
`walrus : Array (String × Expr)` field (parsed with a `#[]` default, so
pre-existing envelopes ingest unchanged; every meta-theorem arm matches
the node with `..` or one extra binder — no new induction cases);
`LowerCtx.walrusForbidden` is collected by `stmtNamesXW`/`exprNamesXW`
(the `yfNames` discipline: skip walrus-bearing-genexp subtrees; a
NESTED def's names all count, conservatively); a walrus-bearing
delegation is NOT `yield from`-inlined (its binding would land in the
enclosing frame — refused loudly instead). Labs:
`gen_lab.walrus_filter` (the shipped shape, three differential rows)
+ `walrus_leak` (the PEP 572 leak read back — refused) +
`walrus_stmt` (a walrus outside a genexp filter — the generic loud
unsupported). On the shipped file the QS ordering line lowers
(`<genexpr@2>` returns to the census) and the full bound() battery
matches CPython.

## search()'s first blockers (pass 5 — dict.clear(), chained assignment, the live-view store)

`Searcher.search()`'s prologue is four statements; the census against
the tier found two constructs missing and one recorded gap already
closed:

1. **`self.tp_score.clear()`** — the dict MUTATOR, `AttrPlan.dictClear`
   (the `attrCallPlan` dict arm grows `"clear"` beside `"get"`; every
   other dict method stays the loud refusal): entries := `#[]`, shape
   version BUMPED (a live `pst.items()`-style iteration must see the
   change as CPython's "dict changed size during iteration" would),
   returns `None`; wrong arity is the faithful
   `TypeError: clear() takes no arguments (n given)`; keyword arguments
   ride the positional-only-loud pattern of `.get`. Aliasing-visible
   through the heap, exactly like the subscript store. `.clear` is NOT
   added to `Expr.heapFree`'s attribute whitelist (`.get`-only), so the
   fragment is undisturbed.

2. **Chained assignment** (`pos = self.root = history[-1]`; main()'s
   `best, cand, d0 = …` is a single tuple target, not this) — CPython:
   the RHS evaluates ONCE (DUP_TOP), then the targets are stored LEFT
   TO RIGHT, each target's subexpressions evaluated at ITS store time.
   Built as an INGESTION SPLIT (`splitChains`, Json.lean — the
   yield-from/genexp lowering family, running FIRST so every later
   census sees plain assigns), admitted when the FIRST target is a
   plain NAME:

       t1 = t2 = … = v   ⇢   t1 = v; t2 = t1; …

   This is exact: the duplicated top is read back from `t1` — a
   frame-local name store followed by a name read returns exactly the
   stored value (pure, unobservable — `x = x.y = v` reads the NEW `x`
   for the receiver, as CPython does), each later target's
   subexpressions still evaluate after the earlier stores, and every
   target rides the EXISTING single-target discipline (including its
   per-statement `Stmt.heapFree` classification — no fragment edits at
   all, no interpreter edits at all, no new mutual member). A chain
   whose first target is NOT a name cannot be split without
   re-evaluating or naming the RHS; it stays un-split and hits the
   standing loud multi-target refusal (`chain_attr_first` the exposing
   row).

3. **`pst["K"] = K_MID if … else K_END` from a function body** — the
   pass-4 gap note ("the subscript-store arm must accept a live-view
   `.ref` primary") turned out ALREADY CLOSED by pass 3's live-view
   consult in name resolution: the primary `pst` resolves through
   `World.globals` to the live ref and `heapStore` proceeds. Claimed by
   differential rows (init_lab `swap_a`), not new code.

## The trace clock (pass 6 — time as an INPUT, the owner-approved design)

The pass-4 §wall-clock time decision said the wall clock has NO value in
the model. That stands — refined, not reversed: the wall clock still has
no value the model INVENTS. What changes is where readings come from:
**time is an input, not an effect.** `World` gains a CLOCK TRACE — a
finite list of readings, consumed in order — and evaluating the exact
call `time.time()` POPS the next reading. The old poisoned-binding
refusal remains the abstraction for every OTHER impure surface: `time`
as a bare value, `time.sleep(…)`, any other attribute of the module, and
every other unmodelled import keep refusing loudly at evaluation. This
replaces the "impure builtin refuses on evaluation" wall for exactly one
call shape, and unblocks deep `search()` stepping past the 2048-node
frontier.

**Representation: the trace is `List Int`, readings are OPAQUE integers.**
The decision and its soundness argument, recorded honestly:

* CPython's `time.time()` returns an IEEE-754 double. The model has no
  float tier anywhere, and a float reading would immediately meet
  arithmetic whose rounding the model refuses to guess. The shipped
  file's only in-tier clock consumer is `bound()`'s
  `time.time() > self.deadline` (line 328) — a single comparison against
  an int-valued attribute (`1 << 63`, or whatever the driver stored).
* The trace domain is therefore ℤ, and the RECORD-REPLAY boundary keeps
  the differential claim exact: the harness's recording clock
  (CPython side) returns `time.time_ns() // 1000` — an **int** in
  integer microseconds — and records exactly what it returned. The
  oracle run itself consumes those integer readings, and the model
  replays the same list. Both sides see literally the same values, so
  exact equality is preserved end to end; nothing is quantized AFTER
  the fact.
* The claim is scoped, loudly: the model says NOTHING about runs under
  float readings. `model(tr) = CPython(tr)` for integer traces `tr` —
  and the shipped comparison site factors through an exact int/int
  comparison under any integer trace, while CPython's own float-int
  comparison at that site is also mathematically exact, so the integer
  restriction loses no behavior OF THAT SITE (both branch outcomes are
  reachable by integer traces). Extending readings to exact dyadic
  rationals (every double is one) is sound but pointless until floats
  exist elsewhere in the tier; that extension is a future recorded
  decision, not a widening of this one.
* Microsecond scaling is a HARNESS CONVENTION of record mode (real-clock
  magnitude, still an int, still under `1 << 63` — the dead-clock regime
  survives recording); the model semantics is unit-agnostic. Synthetic
  traces choose their own units, consistently with the deadlines they
  are compared against.

**Pop semantics.** `World.clock : List Int := []`. Evaluating the
admitted call shape pops the head: result `.int t`, world's clock := the
tail. An EMPTY trace is the LOUD refusal "clock trace underrun" —
fuel-independent, per the loudness doctrine: a trace underrun is a spec
error in the run's INPUT, never a silent 0, never a timeout. `initWorld`
seeds `[]` (the pinned file's regime: any reachable `time.time()` under
an empty trace refuses at the exact consultation point, the pass-5
frontier pin's behavior with a sharper message). The public boundary
gains `callFunctionClock m f args clock fuel` — `callFunction` with the
world's trace seeded; `CallsIn` carries traces through its explicit
world, as for every world-dependent claim.

**Admission — exactly `time.time()`, decided by the pure `isClockCall`.**
The arm fires in the call-with-attribute-receiver dispatch BEFORE the
receiver evaluates (the receiver's own evaluation is the poisoned
refusal), if and only if ALL of:

1. the call is literally `<name>.time()` with `<name> = "time"`, the
   attribute `"time"`, NO arguments and NO keywords (the attr test is
   the FIRST conjunct, outside the receiver match, so the heap-free
   fragment's `.get` arm reduces `isClockCall` to `false` by `rfl` and
   world-symbolic proofs never consult the world here);
2. the name is UNSHADOWED at the consultation point: not in frame
   locals, statically POISONED in the G1 table (the benign-import
   binding's state), and absent from the live view (a rebound-during-
   init `time` falls through to the ordinary arms);
3. the module CENSUS `moduleClockOk` passes: some top-level statement is
   the exact benign import `import time`, NO other analysable top-level
   statement binds or stores `time` (an unanalysable statement fails the
   census — it might), and no function or class subtree carries `global`
   (the extractor-recorded `has_global`, the namedtuple census's
   discipline) — so the poisoned binding provably IS the import's, not
   some out-of-tier rebinding's.

Everything failing the admission takes today's path (poisoned refusal /
faithful errors), verbatim. `time.time(x)` refuses loudly (CPython would
evaluate args then raise `TypeError`; the model never fakes it).
`time.time()` under kwargs syntax rides the H6 loud arm unchanged.

**Fragments and meta-theorems.** The clock call is an attribute call
with attr ≠ `"get"`, so it is ALREADY outside `Expr.heapFree` — the
fragment is undisturbed and `worldInv` stays true as stated (its
attribute arm picks up the `isClockCall = false`-by-`rfl` reduction).
`fuelMono`: the new arm is fuel-free on both sides of the pop. No new
mutual member, no appended conjuncts.

**Record-replay in the harness.** A `cases.json` case may carry
`"clock"`: either a literal trace (list of ints — BOTH sides replay it:
CPython through a per-module stub object bound to the module's `time`
name, the model through the job's `"clock"` field) or `"record"` (the
CPython side's stub reads the real clock as integer microseconds,
records, and returns; the recorded list becomes the model's trace). A
CPython-side underrun raises a distinctively-named exception that can
never match anything. Rows without `"clock"` run exactly as before
(empty trace). Batch jobs gain the optional `"clock"` field
(`callFunctionClock`); script mode has NO trace flag yet — a top-level
`time.time()` underruns loudly — recorded as deferred, not designed.

**Axiom classes over traces (groundwork).** Trace classes are named
predicates on `List Int` (Logic.lean): `ClockTrace.WallClock` — the
unconstrained class, `True`, so a `∀ tr` theorem IS a WallClock theorem
(no axioms consumed); `ClockTrace.Monotone` — nondecreasing readings
(`List.Pairwise (· ≤ ·)`), the class future deadline-abstraction
theorems will consume ("once expired, always expired" needs it; nothing
consumes it yet — stated, not spent). The FIRST trace-quantified theorem
shape: **safety is trace-independent when the run never consults the
clock** — concretely, the pass-5 stepped-search results hold FOR ALL
traces (`∀ tr`, the four pinned `(depth, gamma, score, move)` tuples and
node counts are unchanged with `clock := tr`), provable by `rfl` because
the sub-2048-node runs never scrutinize the trace, so kernel reduction
never blocks on the free variable. The recorded CPython trace for those
steps is EMPTY — CPython never called `time.time()` below the node wall
— and the `∀ tr` statement is strictly stronger than replaying it.

**As-built deltas** are recorded at the end of this section when the
implementation lands, per the standing discipline. Predicted flips the
build will make, named up front so they are review points, not
surprises: exc_lab's `time_live` message pin (poisoned-binding message →
underrun message — still loud, one message sharper) and the sunfish
2047-searcher frontier pin's REASON (same `.unsupported` shape,
underrun instead of poisoned binding), which also gains the armed pair —
a trace that lets the 2048th node continue to CPython's exact
`(bound, nodes)`, and one that raises `Stop` at that node.

AS-BUILT (2026-08-11, pass 6). Implemented as designed; the deltas,
each a narrowing, a mechanical necessity, or a MEASURED correction:

* `isClockCall m st recv attr = (attr == "time") && clockRecvOk m st
  recv` — the receiver fork is the separate worker `clockRecvOk`, the
  attr conjunct outside it as designed; the worldInv patch is exactly
  the predicted `rfl` (`isClockCall m st recv "get" = false`), the
  fuelMono patch one `split`. The census walks `m.topLevel` with
  `stmtIsClockImport` and requires `hasGlobal = false` on BOTH
  `m.functions` and `m.classes` (methods are flattened, but a class
  BODY carries its own flag).
* Both predicted pin flips happened verbatim (exc_lab `time_live` →
  the underrun message; the sunfish frontier pin now PINS that message
  and gained the armed pair — `clock := [999]` continues to CPython's
  exact `(0, 2049)`, `clock := [1001]` raises `Stop` at node 2048 with
  the world retained and the reading consumed, both CPython-derived).
* **The `rfl` prediction for trace-quantified theorems is FALSIFIED by
  measurement** — recorded so nobody retries it: the elaborator's
  free-variable `whnf` does not share work the way closed kernel
  evaluation does. On clock_lab's TEN-ITERATION `pure_sum(10)`, `rfl`
  died beyond 4,000,000 heartbeats (and `py_simp` at fuel 512 blew
  1,000,000 on `isDefEq`). What WORKS is SYMBOLIC EXECUTION at small
  concrete fuel: `py_simp [clock_lab, callIn, execWhile]` proves
  `pure_sum_all_traces` (fuel 64) in ~20 s — the world is
  concrete-except-clock and nothing scrutinizes the free trace.
  CONSEQUENCE for the capstone shape this section promised: the
  sunfish stepped-search `∀ tr` statement does NOT land by per-run
  normalization (a search-sized py_simp storms — the standing pass-4/5
  finding); it waits for the **CLOCK-ERASURE meta-theorem** — "a run
  decided `.ok`/`.exn` from the EMPTY trace never consulted the clock,
  hence runs identically under EVERY trace, preserving it" — the
  fuelMono-shaped mutual induction, recorded in the backlog as the
  next milestone. The shipped-file trace claims that DO land now are
  the concrete armed pair + underrun pins above; the lab-scale
  `pure_sum_all_traces` is the first trace-quantified theorem.

## The cast tier: `int(str)` and `str(…)` (pass 8 — parse/render; BUILT)

The whole-file goal leaves two one-line module functions un-runnable:
`parse(c)` needs `int(c[1])` (a str) and `render(i)` needs `str(1 - …)`
(an int). Two gaps, one of them a LOUDNESS BUG:

* `int(<str>)` refuses loudly today (the v0 arm) — honest, just narrow.
* `str` (and `input`, the recorded pass-4 gap) are absent from the
  builtin surface entirely: `str(x)` resolves through locals → G1 →
  functions → the ladder → the live view → **a fake `NameError`** for
  a name CPython binds. The doctrine violation, not the tier gap, is
  what forces the change.

**Design:**

* `int(<str>)` — the honest subset, three-way: (1) every char of the
  argument is in the SAFE ALPHABET `" \t\n\r+-0123456789"` and the
  string parses as `[ws] [one sign] digit+ [ws]` → the exact integer;
  (2) safe alphabet but malformed (`""`, `"+"`, `"1 2"`, `"--3"`,
  trailing junk from the alphabet) → the faithful
  `ValueError: invalid literal for int() with base 10: '…'` — within
  the safe alphabet CPython accepts NOTHING we reject (underscore
  grouping and Unicode digits are outside it by construction); (3) any
  char outside the alphabet → LOUD refusal (it could be one of
  CPython's exotic acceptances — `"1_2"`, `"٣"` — never guessed).
* `str(…)` — a new ladder builtin, value-only: `str()` = `""`,
  `str(<int>)` the exact decimal (Lean's `toString : Int → String` is
  CPython's format, `-` sign included), `str(<bool>)` = `"True"/"False"`,
  `str(<str>)` identity, `str(None)` = `"None"`; every container/ref
  argument and every 2+-argument form (`str(bytes, enc)`) is LOUD
  (repr recursion and decoding are not guessed).
* `input(…)` — a ladder arm that refuses LOUDLY unconditionally (stdin
  is a runner-boundary effect, docs/memory-model.md §effects), placed
  like `print`'s; plus `isBuiltinName` membership for both names so a
  bare `str`/`input` value reference is the loud builtin-as-value
  refusal, never a fake `NameError`.
* Meta-theorems: two new ladder `ite`s thread through `fuelMono`/
  `worldInv`/`clockErase`'s name-call arms; `str`/`int` calls stay
  inside `Expr.heapFree` (pure workers, refs refused loudly).

**AS-BUILT (same day):** exactly as designed — `intWs`/`digitsToNat`/
`intOfStr` (workers, OUT of the simp sets per the freeze doctrine),
`strOfVal` (dispatcher, IN `py_simp`/`interpUnfolds`), the two ladder
arms before `print`'s, the `isBuiltinName` additions. Labs:
`str_lab.cast_int` (8 match + 2 loud rows — `"1_2"` and a Unicode
digit refuse, empty/`"+"`/`"12x3"`/`"- 3"` raise the faithful
`ValueError`) and `cast_str` (6 rows). ON THE SHIPPED FILE:
`parse`/`render` run, CPython-exact and mutually inverse
(pins_init §the module surface); `hist` is confirmed a live-view heap
list; `main()`'s loud refusal at `import sys, sunfish_ui.uci` is
PINNED as the file's designed boundary — the real UCI interface is an
EXTERNAL module (shipped in the wheel), so whole-file coverage of
sunfish.py ends there BY THE FILE'S OWN STRUCTURE, not by a tier gap.

**THE KERNEL-AFFORDABILITY VERDICT (pass 8, definitive — closes the
pass-7 open item unless the interpreter's compilation is redesigned):**
bisected with `decide +kernel`: `initWorld` alone ≈ 10–20 s; the
`Searcher()` construction ≈ +10 s; ONE 2-node `bound()` run EXCEEDS
22 minutes at fuel 4096 and 16+ minutes at fuel 1000000 (fuel-literal
size ruled out by the comparison) versus milliseconds natively — the
kernel is ~3 orders of magnitude slower per interpreter step at search
shapes (suspected: `brecOn` spine re-reduction over the mutual block's
match trees). Search-scale concrete runs are NOT kernel-checkable in
practical time; the `∀ tr` search statements remain the transport
theorem + native `#guard` pairing. Reopening requires an
interpreter-representation change designed for kernel reduction (a
fuel-indexed step function) — a major direction, recorded, not
scheduled.

## Clock erasure (pass 7 — the trace-independence meta-theorem; DESIGN)

Opened by pass 6's measured finding: free-variable normalization does
not scale, so search-sized `∀ tr` claims need a TRANSPORT theorem, not
per-run reduction. The claim:

**A run decided `.ok` or `.exn` from a world with `clock = []` never
consulted the clock; it therefore runs identically under EVERY seeded
trace, and returns it untouched.**

Why the empty trace is the right base: the pop arm on `[]` is the
underrun `.unsupported`, and `.unsupported` propagates unconditionally
(the loudness invariant — nothing converts it to `.ok`, and the
exceptions tier catches only `.exn`), so a decided `.ok`/`.exn` from
`[]` provably never reached the pop. `.timeout` from `[]` also
transports (a run that popped would have refused, not timed out).
`.unsupported` does NOT transport — the underrun itself is the
counterexample — and the relation simply claims nothing there.

Shape (Obs.lean, the fuelMono discipline — one conjunct per mutual
member, the appended-LAST ordering preserved):

* `World.withClock w tr := { w with clock := tr }`;
  `FrameState.withClock st tr :=
  { st with world := st.world.withClock tr }`.
* `ClockErasedW (x : Run World α) (y : List Int → Run World α)` — the
  three clauses: ok (`x = .ok w v → w.clock = [] ∧ ∀ tr, y tr =
  .ok (w.withClock tr) v`), exn (same shape), timeout
  (`x = .timeout → ∀ tr, y tr = .timeout`). `ClockErasedF` the
  `FrameState` twin. No unsupported clause, by design.
* Theorem `clockErase (fuel)`: for every mutual-block member `F` and
  every input whose world has `clock = []`,
  `ClockErased (F … st …) (fun tr => F … (st.withClock tr) …)`.
  Induction on fuel, mirroring `fuelMono` arm for arm.
* Congruence spine: `ClockErased.bind` (the continuation instantiated
  at the DECIDED intermediate state, whose emptiness the ok-clause of
  the head supplies — that emptiness is exactly why the clause carries
  it), `.bindE` (the exceptions-tier bind), `.liftRes`, `.withLocals`,
  `.ite`; plus the projection lemmas (`(w.withClock tr).heap = w.heap`
  and friends — `rfl`) and the update-commutations (`withClock`
  commutes with `with heap :=`/`with globals :=`/`with stdout :=` —
  `rfl` by structure eta).
* The clock arm's own case: the base side is the underrun
  `.unsupported` — vacuous under the relation; the pure admission
  (`isClockCall`/`clockRecvOk`) is withClock-invariant (it never reads
  `clock`) — `rfl` lemmas.
* `initWorld m` has `clock = []` definitionally, so the public
  corollary is: whenever `callFunction m f args fuel` is `.ok`/`.exn`,
  `callFunctionClock m f args tr fuel` equals it for EVERY `tr` — and
  `CallsIn`-level corollaries transport every existing concrete
  empty-trace pin (the whole pass-5 stepped-search battery included)
  to `∀ tr` statements at zero marginal kernel cost.

Payoff target, in order: the sunfish stepped-search `∀ tr` theorem
(the shape pass 6 promised) as a corollary of the existing concrete
pins plus this lemma; later, `Monotone`-conditioned deadline theorems
on the same transport.

**BUILT (pass 7, `LeanModels/Python/ClockErase.lean`) — as designed,
with the as-built record:**

* The induction is assembled from PER-MEMBER ARM LEMMAS (`ce<F>_succ`,
  each taking the whole 18-conjunct `CE fuel` as its induction
  hypothesis) rather than one monolithic `induction … with` block —
  every arm is independently compilable during development and the
  final `clockErase` is a two-line induction. Conjunct order is
  `fuelMono`'s exactly.
* **The workhorse replacing `fuelMono`'s `Run.le_refl`:**
  `ClockErasedF.of_seed` (and the `W` twin) — any fuel-free tail whose
  seeded family is literally `Run.seedF` of its base run is erased;
  the equation is provable by the withClock simp NORMAL FORM
  (projection lemmas; `withClock_mk` constructor-unfoldings — seeded
  updates and base leaves meet at `World.mk … tr`; `liftRes`/
  `withLocals`/`toWorld` seed-naturality), and the `h0` side pins the
  base's decided clock through `FrameState.withClock_self` at the
  site's emptiness hypothesis. Congruences for the combinator spine:
  `bind`, `bindE`, `liftRes`, `ite`, `ClockErasedW.withLocals`,
  `ClockErasedF.toWorld`. The clock admission is withClock-invariant
  (`isClockCall_withClock`/`clockRecvOk_withClock`, in the `ce_norm`
  normal-form simp set); the pop arm itself closes by the vacuous
  `unsupported` leaf, exactly as designed.
* **Mechanical traps, measured on this file:** (1) `exact … (by …)`
  COMMITS inside `try`/`first` even when the nested block fails (the
  recorded py_prove trap, live again here) — a `cases X <;> try
  (…of_seed…)` script that PARTIALLY applies poisons the remaining
  goals; every such site is written as explicit per-constructor arms.
  (2) The relation's seeded clauses carry a BETA-REDEX (`y tr` with `y`
  a lambda): consume them with `simp only [hy]`, never `rw [hy tr]`.
  (3) `cases h : <scrutinee>` finds no occurrence under an UNREDUCED
  nested matcher — force it with `dsimp only` first (`stepIter`'s
  status arms, the kw plan arms, `next`/`enumerate`'s list matchers).
  (4) Continuation goals regenerate `(s.withClock tr)` projections —
  `ce_norm` before any relational step whose head mentions the state's
  fields.
* **The boundary corollaries:** `initWorld_clock` (`(initWorld m).clock
  = []` — the base regime is definitional); `callFunctionClock_ok`/
  `_exn`/`_timeout` (a decided/timed-out `callFunction` equals
  `callFunctionClock` at EVERY trace); `CallsIn.clock_erased` (stateful
  transport, after-world seeded `w'.withClock tr`);
  `CallsTo.clock_erased` (every `==>` fact holds under every trace).
* **The exemplar** (`clock_lab.pure_sum_all_traces_transported`): the
  `∀ tr` statement as `callFunctionClock_ok` applied to the SINGLE
  empty-trace instance of the pass-6 theorem (through the
  `[]`-boundary bridge `callFunctionClock_nil`, ClockErase.lean). The
  `∀ tr` costs nothing beyond the one empty-trace proof. Per-member
  projections (`evalExpr_clockErased` … `callClosure_clockErased`, the
  fuelMono `_mono` discipline) expose every conjunct for the
  search-scale corollaries.
* **MEASURED: the THREE-TIER evaluation hierarchy on concrete runs**
  (amended after building `pins_clock.lean` — the earlier
  DecidableEq/`decide +kernel` plan was tried and its premise
  FALSIFIED). Core `#guard` evaluates by the UNTRUSTED COMPILED
  evaluator — its own docstring says passing "is *not* a proof" — so
  the repo's concrete pin batteries (`#py_check` included) are
  native-evaluated REGRESSION checks, not kernel facts. Measured on
  the re-pinned file: native — the whole 23-pair bound battery ≈ 937 s
  (the split's pole); KERNEL (`decide +kernel`, core `DecidableEq` on
  the `Option (Int × Int)` probe — no new instances needed) — ONE
  2-node bound probe exceeded 16 minutes, dominated by `initWorld`
  re-evaluated per fact; elaborator (`by rfl`) — ~2 minutes even for a
  ten-iteration loop at fuel 64, fuel-independent. Consequence: an
  UNCONDITIONAL search-scale `∀ tr` theorem is not affordable today —
  `Examples/python/sunfish/pins_clock.lean` lands the transport
  theorem `boundProbeT_all_traces` (seconds to check: `evalExpr`/
  `callIn` erasure composed through the probe's projections — it
  upgrades ANY proved empty-trace probe to every trace) plus native
  `#guard` pins of the seeded surface (empty AND sample traces, the
  batteries' standing trust level). A kernel-affordable concrete-run
  route (e.g. a kernel-reducibility pass over `initWorld`'s hot path)
  is the recorded open item; transport hypotheses AT SYMBOLIC SCALE
  keep the exemplar's route (`pure_sum_all_traces_transported`).

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
* **`__name__` is the FIRST marshalled global, and it is BUILT**
  (2026-08-12). CPython's import machinery binds it before the first
  statement; for a file executed as a program it is `"__main__"`, and
  running a file as a program is exactly what leanpy does. Reading it used
  to refuse loudly ("bound by the import machinery, not by a statement"),
  which walled off every `if __name__ == "__main__":` block in real Python
  — a boundary of the model's own making, not of the language. `runScript`
  now supplies it by PREPENDING the binding (`scriptNameBinding`, span
  line 0) to the prefix view the G1 fold sees, so static resolution finds
  it before the dunder arm and a file that rebinds `__name__` itself still
  wins on source order. The scope is exactly the script surface: the
  closed FUNCTION surface (`initWorld`, `callFunction`) never sees the
  binding, because an imported module's `__name__` is its module name and
  the runner has no such claim to make. The other dunders (`__file__`,
  `__doc__`, `__spec__`, …) keep the loud refusal — only `__name__` has a
  value the runner boundary fixes. Pinned by
  `harness/scripts/main_guard_script.py` (both arms of the guard).

`leanpy` v0 (post-H1-core): module-level execution of current-tier
scripts, first-unsupported-construct reporting, stdout diff vs python3.9,
wired into the harness as a script-corpus mode. `Module`'s
functions/topLevel split loses `def`/assignment interleaving — v0 must
detect and refuse interleaving-sensitive scripts loudly.

**RESOLVED 2026-08-12 without changing the representation** (`Script.lean`
`defsBoundBefore`): the split loses ORDER, but order is only observable
through a REFERENCE, so the admission is per statement and per name — a
top-level statement may mention a name the module binds by
`def`/`class`/namedtuple only if that definition ends before the statement
begins. Under that condition the position-independent tables and CPython's
sequential binding agree on every reference made, and a genuine forward
reference (CPython: `NameError`) refuses loudly. The check covers the G1
prefix too, where the old blanket rule never looked: `x = f()` above
`def f` was executed by module init and answered `1` where CPython exits 1.
The ordered `ModuleItem` representation remains the fix for what this does
NOT buy — running a `def` as a statement, rebinding a name between two
definitions — but it is no longer what stands between leanpy and real
files (docs/backlog.md, the measured ladder).

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
fix; SUPERSEDED 2026-08-13 by §the one pipeline — script mode no longer
folds anything, and `g1Prefix`/`suffixConsistent` are deleted. The
paragraph is kept because it is the argument the closed-function fold's
retroactivity still rests on.)** Poisoning is RETROACTIVE (the marker shadows the earlier value),
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

**THE ROLLBACK IS SOUND FOR CALLS AND UNSOUND FOR PROGRAMS (2026-08-12,
found by `tools/leanpy`, guarded — normative).** `initFoldLive`'s last arm
rolls a failed top-level statement back and poisons the names it may have
bound. On the closed FUNCTION surface that is exactly right: nothing was
observed, and every later read of a poisoned name refuses loudly. On the
whole-PROGRAM surface it is wrong, because the statement's OWN effect is
observable. Two reproductions, both silently wrong before the guard:

* `x = talk()` where `talk` prints — the in-function `print` refusal
  aborted the attempt, the output vanished, and leanpy answered `done`
  where CPython printed `side effect` first;
* `x = 1 // 0` — the attempt raised, the rollback swallowed it, and leanpy
  answered `done` with exit 0 where CPython exits 1 having printed
  nothing.

`runScript` refused such a program (`initNothingSkipped`, Script.lean)
until §the one pipeline (2026-08-13) removed the fold from script mode
altogether: with every top-level statement EXECUTED there is no rollback
to detect, and the residue recorded at the end of this paragraph is
closed by construction. The rest of this paragraph documents the guard as
it stood, and the reproductions it was found by, both still pinned in the
corpus. The signal needed no fold change: a rolled-back statement's dirty names are poisoned in the static
table AND absent from the live view (`resolvedG` drops poisoned entries),
while a statement the live pipeline EXECUTED leaves its value there.
Benign imports are exempt — the whitelist poisons `time` by decision, not
by failure, and running one observes nothing. RESIDUE, recorded rather
than silently accepted: a failed statement whose name a later top-level
statement successfully rebinds hides behind that later value; closing it
exactly needs a status signal from `initFoldLive` itself, which is the
recorded next step. `harness/scripts/init_effect_script.py` and
`init_raise_script.py` pin both reproductions.

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
* **The genexp lowering gained the DRAIN-GATED nested-target
  admission** (K_END nests a genexp inside a genexp's elt): a free name
  that is the TARGET of an ENCLOSING genexp is admissible as a by-value
  capture ONLY when the inner genexp is passed DIRECTLY to a draining
  builtin (`tuple`/`sum`/`sorted`/`max`/`min`/`any`/`all`/`list`/`set`
  — `LowerCtx.genTargets` + the call-arm `drainOk` gate): the drain
  completes within one elt evaluation, before the enclosing target can
  advance, so by-value equals CPython's by-reference. And a synthesized
  `<genexpr@m>` call inside the elt is EXCLUDED from the capture census
  (the leading `<` is unnameable in Python — the `defsBeforeLive`
  precedent); without the exclusion the outer genexp refused its own
  lowered inner.

## The one pipeline (2026-08-13 — leanpy's script surface unified)

**Normative for SCRIPT mode only.** The closed-function surface
(`callFunction`/`CallsIn`, `initWorld`, `moduleGlobals`, every theorem) is
untouched by this section: `initWorld` still folds-and-executes a module's
top level exactly as §module-init execution describes, and every
world-symbolic proof keeps its geometry. What changed is how `runScript`
runs a whole PROGRAM.

### The bug class this closes

leanpy ran a program through TWO pipelines: the G1 fold built `initWorld`
from the G1-faithful PREFIX of the top level, and `execScriptStmts` ran
the live SUFFIX. Every hole the completeness survey found was the same
shape — the fold's approximation (skip, poison, never print) meeting the
program surface's demand that every effect be observable, in order:

| found | what the model answered | the guard bolted on |
|---|---|---|
| `class C: print("x")` | the print vanished | `ClassDefn.creationPure` |
| `x = talk()`, `talk` prints | the print vanished | `initNothingSkipped` |
| `x = 1 // 0` | `done`, exit 0 | `initNothingSkipped` |
| a suffix rebinding a function-read global | (refused) | `suffixConsistent` |

Three were WRONG ANSWERS. Each guard was correct and each made the
boundary a little more baroque; `initNothingSkipped` carried a recorded
RESIDUE it could not close (a failed binding masked by a later successful
rebinding of the same name), and `suffixConsistent` was the single biggest
wall in the wild — 27 stdlib files and sunfish.py itself.

### The design

**Execute every top-level statement through the script executor, write its
bindings to the live globals, and read them back through the poisoned/
absent arms.** `initWorld` is not called in script mode at all. Nothing is
folded, so nothing can be skipped, rolled back, or go stale;
`initNothingSkipped`, `suffixConsistent`, `g1Shape`/`g1Prefix`/
`liveSuffix` are DELETED rather than tightened, and the residue above is
closed by construction.

The hard question was the covenant: function frames resolve module names
STATICALLY FIRST (`moduleGlobals`), and the static table cannot contain
execution results (`moduleGlobals → execStmt → evalExpr → moduleGlobals`
is not definable). The answer is not to change resolution — it is to
remove the static table from the picture. `runScript` threads a module
VIEW (`scriptView m`, Script.lean) whose top level carries no program
statement:

* `scriptNameBinding` (`__name__ = "__main__"`), because `isModuleDunder`
  fires BEFORE the live-view consult;
* `scriptDefMarker`, an unnameable top-level `def`, which makes
  `topLevelDefFree` FALSE so every closure-call arm takes its DYNAMIC
  path — a module-level `lambda` bound by executed code is a live
  `Obj.closure`, and the heap-free shortcut would answer a fake
  `'dict' object is not callable`;
* the module's IMPORT statements verbatim, so the benign whitelist still
  binds `time` POISONED (the loud refusal for a bare `time`, and the
  precondition of `moduleClockOk`).

Every other module global is then statically ABSENT, and the absent arm
already consults `World.globals` before deciding — hit gives the live
value, miss the faithful `NameError` (the view is trivially
`analysable`). **Sequential visibility is therefore exact for free**: a
name resolves exactly once the statement binding it has run, which is what
the module-init pipeline's per-statement prefix views had to imitate by
hand. The view is built ONCE, so a name lookup costs the fold over three
statements, not over the program.

### The publish

CPython runs a module's top level in a frame whose locals ARE its globals.
The model keeps two fields, so `execScriptStmts` re-establishes the
identification after EVERY statement (`publishScriptGlobals`:
`World.globals := st.locals`, one shared list, no copy). Keeping the
frame's locals rather than draining them is load-bearing: `x += 1` at
module level must read the module global, while inside a FUNCTION the same
statement is a local by CPython's compile-time rule (`+=` is a binding, so
an unbound one is `UnboundLocalError`, never a global read) — which is
exactly why `execStmt`'s augmented-assignment arm reads locals only. The
identification makes module scope come out right through that very arm;
draining the locals produced a `NameError` on `tot += 1` at top level, and
that is how the delta was found.

`initBindable` rides the publish: a top-level rebinding of a builtin or of
a `def`/`class`/namedtuple name refuses loudly (those resolution arms fire
before the live globals, so the shadow would be silently ignored).

### What is still refused, and why it is narrow

The publish is per STATEMENT, so a compound statement the executor
DELEGATES wholesale to `execStmt` (a `for`, a `try`, a `while … else`)
holds its inner bindings in the frame until it finishes — invisible to a
function called from inside it. `scriptFlushCoherent` refuses exactly that
overlap: no name assigned inside a delegated compound may be a name some
function body reads. That is the narrow residue of `suffixConsistent`,
which refused it for the WHOLE live top level.

**THE SEAM IS CLOSED for everything but `while … else` (2026-08-13.)**
The recorded fix was a control shell per statement kind — the executor
already had `if`, `while`, and the `for … in d.items():` shell that
module-init execution used to own (live entries re-read per step, a size
change the faithful `RuntimeError`) — and the general `for` and `try` now
have theirs:

* `execScriptFor`/`execScriptForList`/`execScriptForGen` mirror
  `execStmt`'s `for` dispatch ARM FOR ARM — value sequences (tuple,
  namedtuple, boundary list, str code points, materialized range), the
  LIVE heap-list index cursor whose per-step re-read makes mutation,
  growth and `pop`-shrinkage observable exactly as CPython's listiterator
  makes them, and the lazy generator cursor stepping one `stepIter` at a
  time — including every refusal message verbatim. The TIER is unchanged;
  only the publish granularity differs, and the loop target publishes
  BEFORE the body runs.
* the `try` shell keeps `execStmt`'s admission verbatim (the same
  `tryUnsupported` reason, the same shadowing refusal, the same
  statically-first handler-class resolution) and the same RETAINED-STATE
  covenant — a matching `.user` exn runs the handler from the state the
  raise left, no rollback — moving only the body and handler statements
  onto `execScriptStmts`.

`for … else` is refused by the shell itself (out of tier, as in the
interpreter), so `while … else` is the ONLY compound still delegated
wholesale and the only shape `scriptFlushCoherent` can still fire on. The
guard stays: it costs nothing and it is what would catch the next shell
that goes missing. Measured: the refusal disappeared from both sweeps (it
was 4 stdlib files), and `harness/scripts/loop_publish_script.py` — a
function called from inside a top-level `for`, reading a name that loop
assigns — flipped from refusal to CPython-identical output.

Whitelisted `import` statements are SKIPPED by the executor (they bind
through the static view and running one observes nothing); every other
import refuses loudly through `execStmt`, as before.

### Measured (2026-08-13, oracle CPython 3.9.19)

* in-repo corpus 86 files: **69 MATCH (80.2%)**, up from 59 (68.6%), with
  **47 files executing live top-level statements**, up from 18.
* `harness/script_corpus.py`: 27 scripts, **21 matched / 6 loud**, up from
  18/9 — `live_rebind_read.py`, `live_fresh_global.py` (the old
  `suffix_*` refusal rows, renamed because they are payoff rows now) and
  `init_raise_script.py` all flipped from refusal to CPython-identical
  answers.
* `Examples/python/sf_order/sf_order.py` — the sunfish ordering-arc
  example — went from REFUSE to MATCH with 11 live top-level statements.

## Two bugs the unification exposed (2026-08-13)

Both were reachable BEFORE it, on the closed-function surface; the one
pipeline is what pointed a real program at them.

**1. An unmodelled CPython builtin answered `NameError` — a WRONG
ANSWER.** The shipped sunfish.py's `opt_ranges = dict(QS=(0, 300), …)`
resolved `dict` through locals → static table → live globals → all
missing → and the arm decided the faithful-looking `NameError`. CPython
binds `dict`. The same hole was reachable from an ordinary function body
(`def f(): return len(dict())` answers `NameError`), so it was never a
script-mode artifact. FIXED: `isPyBuiltinName` (Semantics.lean) is the
full `dir(builtins)` of the PINNED CPython 3.9, and every arm that may
DECIDE a `NameError` consults it first — an unmodelled builtin is a loud
refusal naming the construct. `isBuiltinName` (what the model implements)
stays the resolution arm that fires earlier; the difference between the
two lists is precisely the set of names for which a `NameError` is a lie.

**2. `moduleGenFree` claimed more than it can — FIXED the same day.** Its
docstring said no `Obj.generator` can exist in a module with no generator
defs, because "`callIn` is the only allocator". `enumerate(…)` and
`itertools.count(…)` allocate generator FRAMES with no generator def in
sight, so `for i, c in enumerate("PNB"):` in such a module hit the guard
and refused with `internal: … heap well-formedness violation — report
this` — ordinary Python reported as an interpreter bug, and reachable
from a plain function body, not just script mode. It was a LOUDNESS
defect, not a soundness one: `Expr.heapFree` already excludes
`enumerate`/`count`/`next` calls, so `worldInv` never met the arm.

`moduleGenFree` now has three conjuncts: no generator `def`
(`funsAnyGen`, as before) and no generator-FRAME ALLOCATOR in the
function bodies or the top level (`funsGenAllocFree` /
`Stmt.genAllocFreeList`, over the new `Expr.genAllocFree` — a call of
`enumerate` or `count`, or a surviving generator expression; `next(…)`
STEPS a generator and never builds one, and an `unsupported` node refuses
before allocating). The walkers are LIST-recursive on purpose:
`Module.heapFree` is discharged by `rfl` at concrete modules and
`Array.all` does not reduce in the kernel (`VCTests`' `factM` caught
that immediately). `Module.heapFree` inherits the strengthening, which
can only make it FALSE for more modules — the safe direction, and
measured: no example lost it, since a function body containing such a
call already left `Expr.heapFree`.

The SCRIPT VIEW needed one more thing for it: carrying no program
statement, it also hides the program's own `enumerate`/`count` calls, so
`moduleGenFree (scriptView m)` would read true again. `scriptViewMarker`
— already the unnameable top-level `def` that turns `topLevelDefFree`
off — got an `enumerate()` call in its body, so BOTH shortcuts are off in
script mode, which is exactly right there: each is a claim that some arm
is unreachable, kept only to make `worldInv` provable, and turning them
off takes the faithful dynamic path.

Acceptance: `Examples/python/iter_lab` gains `enum_sum`/`enum_first`
(differential rows plus `#guard !moduleGenFree iter_lab` — a module with
no generator definition of its own, which is what makes it the right
witness) and `harness/scripts/enum_script.py` pins the top-level shape.
`gen_lab` never caught it because that module defines generators.

## `print` is an ordinary builtin (2026-08-13)

Stdout has been `World` data since the H1 core (§effects); what was
missing was the arm that writes it from inside the interpreter. Until
this pass `print` in a function body refused loudly ("the effect must
thread the mutual block"), and leanpy intercepted `print` STATEMENTS in
its own top-level executor instead. That wall ran through essentially
every real program — functions are where Python prints — and it also made
the executor's shells load-bearing for a second reason (a `print` inside
a delegated top-level `for` was loud).

`evalExpr`'s call arm now implements it: after locals, the module
globals, `findFunction`/`findClass`/namedtuples — so every shadow still
wins — `print(args…)` evaluates its arguments left to right, appends ONE
chunk to `World.stdout` (the runner boundary prints chunks as lines) and
returns `None`. `strOfRVal`/`strOfArgs` moved from Script.lean into
Semantics.lean with it; the printable tier is unchanged (int, bool,
`None`, str; a container or heap value refuses loudly rather than guess a
`repr`), and `print(x, end="")` stays loud through the keyword-call arm.
leanpy's executor no longer intercepts `print` at all — its shells exist
only for the per-statement publish, and prints work anywhere.

TWO CONSEQUENCES, both recorded rather than discovered later:

* **`print` leaves `Expr.heapFree`.** It is the first expression that
  mutates the world without allocating, and `worldInv` says a decided
  run of a heap-free statement returns its input world. The exclusion is
  the same syntactic carve-out `sorted`/`set`/`enumerate` already take,
  and the three proof obligations moved with it: `worldInv`'s call arm
  gains `hprx` and loses one walked `ite`, `fuelMono`'s print branch
  becomes a `bind`, and `clockErase` gains a `bprint` case closed by
  `of_seed` (printing reads no clock, so the seeded family IS the seeded
  base run).
* **The VALUE boundary does not observe stdout.** `callFunction` returns
  `Res Val` and drops the world, so `CallsTo m "f" args v` is silent
  about what `f` printed — true, but not the whole story. `CallsIn` is
  the surface that sees it (`World.stdout` is a field of the world it
  relates), and leanpy's script surface is where the differential harness
  compares output. `Examples/python/g1_lab`'s `try_print` row says so in
  its own docstring, since it is the row that compares a return value
  through a printing call.

Measured: in-repo corpus **72/87 MATCH (82.8%)**, 0 DIVERGE, 23 files
printing; `harness/script_corpus.py` 24 matched / 4 loud, with
`fnprint.py` and `init_effect_script.py` flipping from refusal to
CPython-identical output.

## List comprehensions (2026-08-13)

`ListComp` was the top in-repo construct on the static ladder and shipped
as a loud `Unsupported` leaf. It is now live, and almost none of it is
new machinery.

**The extractor emits the SAME node as a generator expression, under a
different `kind`.** CPython compiles both into an implicit function over
the already-evaluated outer iterator, differing only in what that
function does with each element (yield vs append), so the envelope
carries the identical fields (`elt`/`target`/`iter`/`ifs`/`walrus`) and
the identical v0 restriction (ONE `for` clause, not `async`).

**INGESTION desugars `[e for x in it if c]` into `list(e for x in it if
c)`** (Json.lean, the `yield from` inlining precedent — the envelope
stays a faithful dump of the real AST and the rewrite is a semantics
decision recorded here). That is CPython-exact: building the list eagerly
from the lazy one observes the same effects in the same order, because
the drain completes before the enclosing frame can run again. It also
inherits the genexp lowering WHOLE — the capture census, the walrus
filter, and the `drainOk` gate, which already counted `list` among the
draining builtins.

**The one new interpreter piece is `list(iterable)`**: `tuple`'s exact
inventory of iterables (str code points, tuple, namedtuple class-erased,
boundary list, heap list snapshot, range, generator drain; dict and set
receivers stay loud on the order doctrine) but it ALLOCATES — CPython's
`list(x)` is always a NEW object, never an alias. So the call leaves
`Expr.heapFree` (the `sorted` carve-out again, with the three proof
obligations moving with it: `worldInv` gains `hlstx`, `fuelMono` gains a
`bind` arm, `clockErase` gains `case blist` over a new `allocList` leaf
lemma), and the generator arm can drain WITHOUT the `moduleGenFree` guard
`tuple` needs, precisely because the call is outside the fragment.

Acceptance: `iter_lab.lc_squares`/`lc_filter`/`lc_capture`/`list_of`/
`list_empty` (13 differential rows, plus `#guard`s including
`!(findFunction iter_lab "lc_squares").any FunctionDefn.heapFree`) and
`harness/scripts/listcomp_script.py`. The old `blocked_comprehension.py`
telemetry row became that payoff row; what it used to blame the
comprehension for is now the honest blocker it always had underneath —
`print` of a LIST, whose `repr` the tier does not guess (CPython quotes
strings inside containers and not outside them), pinned separately by
`harness/scripts/print_container.py`.

Measured: in-repo corpus **73/88 MATCH (83.0%)**, 0 DIVERGE; script
corpus 25 matched / 4 loud; 998 differential cases, 0 failed.

## Rendering: `print` of containers (2026-08-13)

CPython's `print` applies `str()` to its ARGUMENTS and `repr()` to
everything INSIDE a container — the two differ on exactly one shape
(`str("a")` is `a`, `repr("a")` is `'a'`), which is why `print("a")` has
no quotes and `print(["a"])` does. The model implements both levels
(`printOne`/`reprVal`, Semantics.lean), replacing the scalar-only
`strOfRVal` that shipped with leanpy v0.

In tier, each pinned differentially in `harness/scripts/repr_script.py`:
int/bool/`None`, str (the quote CPython picks — `'` unless the string
holds one and no `"` — with `\\`/quote/`\n`/`\r`/`\t` escapes and
`\xNN` for the other C0 controls and DEL), tuple (including the
one-element trailing comma), namedtuple (`Move(i=1, j=2, prom='')`),
list (boundary and heap), dict (`{k: v}` in insertion order, which the
model preserves and CPython guarantees), and range
(`range(0, 10, 2)`, the step omitted when it is 1). A container that
contains ITSELF prints `[...]` / `{...}`, CPython's own answer, decided
by an ACTIVE-PATH list rather than by fuel; depth beyond the fixed
`reprFuel` refuses (a budget refusal must not depend on the caller's
fuel).

LOUD, never a plausible-looking line: a SET (its `repr` is hash order,
which the order doctrine forbids guessing), an instance/closure/generator
(identity lives in the address), and a NON-ASCII string, whose escaping
depends on Unicode PRINTABILITY — the same table `.swapcase()` refuses to
guess. `print("héllo")` is fine (that is `str()`); `print(["héllo"])` is
not (that is `repr()`). Pinned by `print_set.py` and
`print_nonascii.py`.

Nothing in the proof layer moved: `print` already left `Expr.heapFree`
when it became a builtin, and `reprVal` is a pure function of the heap,
so `worldInv`/`fuelMono` are untouched and `clockErase`'s `bprint` case
only re-scrutinizes the renderer's result.

Measured: script corpus 26 matched / 5 loud; in-repo survey **74/90
MATCH (82.2%)**, 0 DIVERGE.

## The `dict(…)` constructor, and the shipped file's whole top level
(2026-08-13)

`dict()` is the empty mapping; `dict(k=v, …)` builds one in the CALL's own
order (duplicate keywords are a SyntaxError, so no insert can collide);
`dict(d)` is CPython's shallow COPY — a fresh object, never an alias,
which is the whole point of writing it. A pairs ITERABLE stays LOUD:
rebuilding one needs the per-insert hashability and duplicate-key rules,
and guessing them would be silent corruption. Like every allocating call,
`dict` leaves `Expr.heapFree` (`worldInv` gains `hdctx`, `fuelMono` two
arms — the positional and the keyword form — and `clockErase` a `bdict`
and a `bdictkw` case over a new `allocDict` leaf lemma).

**THE PAYOFF: the shipped sunfish.py's WHOLE top level now executes under
leanpy.** `opt_ranges = dict(QS=(0, 300), …)` was the file's last named
blocker; with it in tier, `runScript` runs the imports, the piece/pst
tables, the padding loop through the items shell, `K_MID`/`K_END`, the
`Move`/`Entry` namedtuples, the three class creations, `hist`, and the
`if __name__ == "__main__":` guard — which is TRUE under leanpy — and
stops at exactly one construct: `main()`'s own
`import sys, sunfish_ui.uci`. A module system is out of scope BY KIND,
and CPython does not get past that line either (`ModuleNotFoundError`,
`sunfish_ui` being a separate package), so the refusal is the honest end
of the program rather than a tier gap in the middle of it. Pinned as the
MESSAGE, not just the shape, in `Examples/python/sunfish/pins_init.lean`
— an `unsupported` for any other reason would be a regression in the
module initialization this whole arc built. (That pin is why `pins_init`
now imports `LeanModels.Python.Script` directly: `runScript` is not in
the `LeanModels` umbrella.)

Measured: in-repo survey **75/91 MATCH (82.4%)**, 0 DIVERGE; script
corpus 27 matched / 5 loud; stdlib sweep unchanged at 5 MATCH / 0
DIVERGE.

## The `assert` statement (the tail batch, construct 1 — BUILT 2026-08-13)

The first member of the ordinary-Python tail (docs/backlog.md §the tail,
ranked the same way). Its justification is NOT the stdlib count — `assert`
is `sole` blocker for 3 library modules and no more — it is that `assert`
is ordinary Python that real programs use, and the goal is to verify
arbitrary Python.

### What CPython does

`assert test, msg` compiles to `if not test: raise AssertionError(msg)`,
guarded by `__debug__`. The model runs the way CPython runs by default
(no `-O`), so the statement is never compiled away and the test is always
evaluated. `__debug__` itself is NOT modelled: it stays a loud module
dunder, so no program can observe the model disagreeing about it.

Two behaviours are observable and neither is guessable, so both are
pinned by paired rows rather than reasoned about:

* **The message is LAZY.** It is evaluated only when the test is falsy.
  `assert_lab.lazy_pass`/`lazy_fail` are the same source on the two
  paths, and the message is a call that PRINTS — so a strict model shows
  up immediately as an extra line of stdout on the passing path.
* **The message is `str()` of the value**, not a fixed string:
  `assert 0, 5` is `AssertionError: 5`.

### Representation

`Stmt.assertStmt (test : Expr) (msg : Option Expr) (span : Span)` and
`PyErr.assertionError (msg : Option String)`. The `Option String` mirrors
the payload-carrying `PyErr.valueError`/`runtimeError` constructors, and
`none` is the bare `assert test` — CPython prints the class name alone,
so a payload-free constructor is EXACT here rather than a recorded gap
(contrast `IndexError`, which is three different CPython texts).

### The message rendering is REUSED, not re-decided

The rendered message is `printOne h v` — the function `print` already
uses for one argument (§rendering: CPython's two-level rule, `str()` on
the argument and `repr()` inside a container). That is not a convenience:
`str(x)` for an `AssertionError` argument and `str(x)` for a `print`
argument are the SAME CPython operation, so sharing the function is what
makes them agree by construction rather than by two parallel tables that
can drift. The refusals come along unchanged and are the right ones — a
set (hash order), an instance or closure or generator (identity), or a
structure deeper than the repr budget make the statement LOUD instead of
guessing a rendering.

MEASURED CORRECTION (2026-08-13, found by the acceptance battery before
landing): a non-ASCII STRING message does NOT refuse, and the design
sketch that predicted it would was wrong. `printOne` is
`| .str t => some t` — a `str` argument renders as ITSELF, with no
`repr` applied and therefore no printability decision to guess. So
`str("héllo")` is `héllo`, and the model emits `AssertionError: héllo`
byte-identically to CPython 3.9.19 (verified both ways, exit 1). The
non-ASCII refusal is real only INSIDE a container, where `reprVal` must
decide escaping. `assert_lab.msg_nonascii` is therefore a `match` row,
not an `unsupported` one. The two-level rule was reused correctly; the
sketch had simply mis-stated WHICH level a bare message argument hits.

### Proof-layer position: inside the fragment

`assert` evaluates two expressions and either does nothing or raises. It
allocates nothing and mutates nothing, so `Stmt.heapFree` holds for
`assertStmt test msg` exactly when both subexpressions are heap-free, and
`worldInv` is undisturbed — no new hypothesis, no weakening. This is the
cheapest possible shape for a tail construct and is why it goes first:
`fuelMono` gains a `bind`-shaped arm and `clockErase` a case that is
closed by the existing `of_seed`, and nothing else in the proof layer
moves.

### What stays loud, and one asymmetry recorded

An `AssertionError` can be RAISED but not CAUGHT. The v0 `try`/`except`
tier matches the class identity of an admitted `class N(Exception): pass`
only, so `except AssertionError:` refuses exactly as `except
ZeroDivisionError:` already does — the existing except-tier boundary, not
a new one. It is asymmetric on purpose: a loud refusal beats a handler
that silently matches nothing. `assert_lab.catch_assert` pins it.

`assert (a, b)` — the classic always-true parenthesised assert CPython
warns about at compile time — is NOT special-cased: a non-empty tuple is
truthy in the ordinary tier, so the model agrees with CPython by
computing the same truthiness. `assert_lab.tuple_test` is the row that
would catch a well-meaning special case.

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
