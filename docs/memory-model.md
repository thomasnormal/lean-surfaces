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
  truthiness, live iteration as above, the three VIEWS in consuming
  position, `enumerate(d)`, `del d[k]`, `iter(d)` + `next` (the bare
  KEY cursor as a first-class object), and `next(<genexp over the keys with
  a filter>)`. Loud: the views as
  FIRST-CLASS values (`k = d.keys()` held across statements, set algebra,
  `reversed`), `.update/.pop/…`, comprehensions, `**kwargs`, `|`,
  returning a dict through the boundary, same-size key-set churn
  during iteration, and `iter` over any NON-dict receiver (CPython has a
  distinct iterator type per receiver — each is its own inch).

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
  a faithful `IndexError`), `.insert(i, x)` (CPython's CLAMPING index —
  never an `IndexError`; §`list.insert`), unpacking `a, b = lst` (an
  eager snapshot
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
  `.remove/.index/.sort/...`, slices (STR slices are BUILT —
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
  statement beyond an UNDECORATED method, `pass`, a docstring, or an
  attribute bound to a LITERAL), ingestion re-checks the body it already
  parses (`classBodyStmtPure` — never trust a field you can verify), and a
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
* **THE THIRD DOOR — a DECORATED METHOD (2026-08-14, found by
  `harness/class_census.py`, BUILT — normative).** The flag above shut two
  doors, a class-body statement and a base expression. It left a third
  open for two years of tier work: the extractor's body loop
  (`if isinstance(s, ast.FunctionDef): continue`) and ingestion's
  (`if k == "FunctionDef" then pure true`) each skipped a method
  UNCONDITIONALLY, decorator list and all. `@log def m(self)` CALLS `log`
  at the `class` statement — CPython prints, the model executed no class
  body and printed nothing. A wrong answer, not a refusal, through exactly
  the door this flag exists to guard. Measured over the pinned 3.9 Lib
  before the fix: **15 such classes in 14 files, 2 of them (`shlex`,
  `sre_parse`) in files the admission was passing**; every one decorates
  with `property`/`setter`/`classmethod`/`staticmethod`, which happen to
  have no creation-time effect — the model was LUCKY, not sound. A
  decorated method is now a creation effect on both sides. The check is
  the structured extractor flag `has_decorators` (`methodCreationPure`,
  Json.lean), in the `has_global`/`is_generator` family, and deliberately
  NOT the method's `args_unsupported`: that is a comma-joined message
  mixing "decorators" with `*args`/`**kwargs`/defaults, and an unusual
  SIGNATURE is refused at CALL time while doing nothing whatever at the
  `class` statement (`cls_deco_args_script.py` is the precision pin,
  `cls_deco_script.py` the refusal with CPython's own output in its
  docstring). This narrowing is the ONLY one the class-tier census found:
  `unexplained demands ≠ ∅ ⟺ creation_effects` holds with 0 violations
  over 679 top-level stdlib classes once the decorated method and the two
  recognized bases are excused, so a decorated method is the single shape
  that was pure-but-not-reproducible.
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
  is pure or loud), and since 2026-08-15 **so are the pure str
  METHOD calls**. The attribute-call whitelist is now a named
  predicate, `heapFreeAttr` = `get` plus
  `swapcase`/`isupper`/`islower`/`upper`/`index`, decided from the
  attribute NAME (all syntax knows) with soundness carried per
  receiver kind: on a heap receiver the five str names miss
  `get`/`clear` on a dict and `append`/`pop`/`insert` on a list and
  refuse on a generator/closure/set, while an INSTANCE receiver
  cannot dispatch at all in a heap-free module (no classes), so
  `attrCallPlan_heapFree` yields a heap READ or a decided refusal;
  on a namedtuple receiver `ntupleCallPlan_heapFree` says the same;
  on a str receiver each arm is argument evaluation plus
  `Run.liftRes` of a total pure worker. `time` is deliberately
  OUTSIDE the whitelist — a trace-clock read consumes a reading, so
  it changes the world (`isClockCall_of_heapFreeAttr` is the fork
  `worldInv`'s attribute case clears first). `.clear` stays out
  because it MUTATES, and every `sorted` call still leaves the
  fragment.
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
differentially (`gen_lab.aliased`, `gen_lab.two_phase`), and the second is
also a THEOREM — `two_phase_calls`, symbolic in `n`, whose second loop
reads the same address in the configuration the first abandoned
(Examples/python/gen_lab/proof.lean); an immediate-value representation
answers them wrong, silently. `status`
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
ALSO a generator, consumed lazily by the fold below it. **The capture
set below is the PRE-#236 engine's** (`self`/`pos`/`gamma`/`depth`/
`root`/`val_lower`, none of them rebound after the `def`); engine master
captures `depth`/`gamma`/`guard`/`killer`/`pos` and `guard` IS rebound,
which is what §Closure CELLS below exists for. This section states the
snapshot fragment, which is still the tier's base case. Python closes over
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
equals read-at-def. The pre-#236 `moves()` satisfied the restriction as
written (`depth = max(depth, 0)` and `val_lower = …` both precede the
def; nothing rebinds after). Engine master's does NOT — `guard` is
assigned below the `def` — and is admitted by §Closure CELLS instead.

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
the same never-rebound rule. The pre-#236 `moves()` was ADMITTED as
analyzed: captures `depth`/`gamma`/`pos`/`root`/`self`/`val_lower`,
no refusal, generator. (Engine master's is
`depth`/`gamma`/`<cell>guard`/`killer`/`pos`, pinned in
`Examples/python/sunfish/spec.lean`.) Acceptance: `Examples/python/closure_lab`
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

## Closure CELLS for rebound captures (H7 cells — BUILT 2026-08-19)

The snapshot tier above admits exactly the captures a frame never
rebinds after the `def`. The shipped engine walked out of that fragment:
post-#236 `bound()` defines `def moves():` and assigns
`guard = not root and calm` BELOW it, so `Searcher.bound` answered
`unsupported statement 'NestedDef'` and NO statement about the current
engine could be typed (docs/backlog.md §L13). Closures with late-bound
captures are ubiquitous in real Python, so this is core capability, not
a sunfish special case.

**A cell is a heap slot.** CPython closes over VARIABLES; a local that a
nested def captures and the enclosing frame REBINDS lives in a cell that
both frames share. The tier models that as what it is:

* `Obj.cell (value : Option RVal)` — a heap object, `none` for CPython's
  empty cell. It is never a Python VALUE: every value-position consumer
  refuses it with `cellInternal` rather than inventing a type for it.
* The frame files the slot under a DIRECTORY key `"<cell>x"`. `<` and
  `>` cannot occur in a Python identifier, so the directory can never
  collide with a name the extractor emits, and the frame's ordinary
  binding of `x` — every read, every write, every existing lemma about
  frames — is untouched.
* `allocCells` creates (or REUSES) the frame's slots when the `def`
  executes, seeded with the name's current binding when it has one and
  EMPTY when it does not (`guard`'s shape). Reuse is what makes a `def`
  in a loop correct: one frame, one cell, every closure it creates
  sharing it.
* `capturesSnapshot` then copies the DIRECTORY entry instead of a value,
  so what the `def` stored in the closure is a location, not a reading.
* `cellsFor` reads the cells at the CALL, from the live locals of the
  frame that is calling, and hands the body plain bindings. That is the
  late binding, and the whole difference from snapshot-at-def.

The extractor decides which captures are cells (`"<cell>x"` in the
`captures` list) and admits exactly the fragment those three rules model
exactly. Three LOUD refusals draw the boundary:

* the nested name must never ESCAPE the defining frame — the cell is
  read from that frame at the call, so an escaped closure would read it
  stale (`closure_lab.cell_escapes`); `cellsFor` re-checks at runtime,
  for hand-built modules;
* for a GENERATOR nested def, every binding of a celled name must
  precede the FIRST call of the nested name. A generator reads its cells
  at RESUME and the tier reads them at the CALL, so a rebinding between
  two resumes would be read late (`closure_lab.gen_cell_after_call`);
* `nonlocal` (a cell WRITE from the closure) and a scope nested deeper
  than one level keep the refusals they already had.

**What the slot's CONTENT is for, stated honestly.** Under the escape
admission the defining frame is the authority, so writing the live value
back into the slot at each call would be an observationally invisible
copy, and the tier does not do it. What the slot buys is the cell's
IDENTITY — one per frame, shared by every closure the frame creates,
reused by a `def` in a loop — which a snapshot cannot express. Relaxing
the escape admission is where the content starts to matter, and where
the write (plus its `Res.mapOk` blindness lemma next to
`heapAttrStore_swapAt`) has to be paid for. Relaxing the generator
admission is a refresh at the four frame-level resume sites.

**The capture census was over-approximating, and CPython said so.**
`_assigned_names` did not count the WALRUS as a binding, so `moves()`'s
`val` — a walrus target, `moves`' OWN local — was reported as a capture
of `bound()` and the census refused the whole nested def for a name
CPython never cells. With the clause added (and comprehension targets
subtracted back out, since `_walk_scope` descends into comprehensions on
purpose), the extractor's capture set agrees with CPython's own compiler
(`co_freevars`) on all 30 nested defs in `Examples/python` plus the
engine's `sunfish.py`: `moves()` captures `depth`/`gamma`/`guard`/
`killer`/`pos`, and only `guard` is a cell.

**Acceptance.** `closure_lab`'s cell battery — `rebound_after` (6, where
a snapshot would forge 5), `cell_read_twice` (two calls straddling a
rebinding), `two_closures_one_cell` (one cell per frame),
`cell_unbound_at_def` (empty at the def), `gen_cell_before_call`
(`moves()`' shape), `lam_rebound` (the lambda flavour) — plus the two
loud rows above, differential and `#py_check`ed.

## The walrus operator (H7+ — BUILT 2026-08-19)

`Expr.namedExpr`: `(x := e)` evaluates `e`, BINDS `x` in the frame that
is running, and answers the same value. Only a plain NAME target is
Python-legal, so the target is a `String`. Nothing else moves — a celled
name keeps its plain binding here, because the cell is read at the
closure call, which is the only place it can be observed.

The general node is emitted ONLY outside a comprehension. A
comprehension is its own scope and PEP 572 leaks the binding to the
ENCLOSING one, which `Expr.namedExpr` would re-scope; inside one the
admitted walrus stays the pass-7 FILTER lowering (§the walrus filter),
whose `walrusForbidden` census is what makes the re-scoping
unobservable. That lowering now hoists the filter's LEFTMOST walrus
rather than requiring the filter to BE a compare: CPython evaluates the
leftmost operand of a compare, a boolop, a binop or a unary first and
without a guard, so hoisting exactly that one is CPython's own
compilation, and the shipped ordering line
(`… if (v := pos.value(m)) >= QS or depth`, a BoolOp) lowers. Anything
deeper is conditional (`a or (v := b)`) and stays loud.

`Expr.heapFree` answers `false` for a walrus. Evaluating one preserves
the WORLD — it binds a frame local — but `worldInv` has no case for it
yet, so the honest answer to "PROVABLY preserves" is `false`; it only
shrinks the fragment. `genAllocFree` is the recursive answer, since a
walrus allocates nothing of its own.

**Acceptance.** `walrus_lab`: the binding outliving its expression, the
evaluation ORDER (`w_order`, `w_call_arg`), the loop-condition idiom, a
short-circuited walrus that never binds (`w_short_circuit(0)` is
CPython's `UnboundLocalError`, which the harness maps to this tier's
`NameError`), and the genexp filter's hoist.

## `yield from` a non-genexp delegate (pass 5+ — BUILT 2026-08-19)

`yield from <expr>` where the delegate is not an admitted genexp now
inlines too, through a FRESH loop target `<yieldfrom@n>` that no Python
identifier can spell — so it collides with nothing in the enclosing body
and needs no `yfForbidden` check at all. `yield from e` differs from
`for t in e: yield t` only in `send`/`throw`/`close` propagation and in
the delegation's RETURN value, and all four are already outside the tier
(a yield in EXPRESSION position is `Expr.unsupported`, and the generator
methods refuse), so the lowering is exact on this tier's surface. The
shipped `moves()` ends in `yield from sorted(…)`, a CALL — which the
statement-level census reported as SUPPORTED while the run refused, so
this one was found by the smoke, not by counting nodes.

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
   drain.** The pre-#236 correction's
   `all(depth > 1 and pos.value(m) >= val_lower or … for m in
   pos.gen_moves())` captured `depth` (a parameter the body REBINDS:
   `depth = max(depth, 0)`) and `val_lower` (a plain local) — both
   outside the H4 by-value admission. (Engine master's correction is
   `all(pos.move(m).king_capture() for m in pos.gen_moves())`, which
   captures only `pos`; the admission below is what still carries
   `calm`'s `any(c in pos.board for c in "RBNQ")` and the ordering
   line.) The drain-gate argument
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
  `0 <= n <= shiftBudget` (CPython ints are unbounded; the sign carries
  through), and a negative count is the faithful
  `ValueError: negative shift count` — raised BEFORE any magnitude
  concern, as CPython does. Bools coerce through `asInt`
  (`True << 2 == 4`, an int) — CPython's bool-is-int. Non-int operands
  keep the faithful TypeError arm.
- **The count is BUDGETED (2026-08-15).** `shiftBudget = 1048576`, so
  the widest result is about a million bits; beyond it the arm refuses
  loudly (`unsupported`), fixed and therefore fuel-independent, exactly
  as `seqBudget` guards `rangeVals`/`tupleRepeat`. It is its own
  constant because it bounds a different resource. This closes a
  recorded live defect in shipped `<<`: the arm was `x * 2^n` with no
  bound on `n`, and measured on this toolchain `1 << (10^30)` neither
  computed nor refused — it died `INTERNAL PANIC: Nat.pow exponent is
  too big`, a runner abort rather than an answer. The bound is DECLARED
  rather than fitted to CPython: `1 << (10^9)` builds a real 125 MB
  integer there and is refused here, which is a tier gap and never a
  claim that CPython raises. Everything the corpus actually shifts
  (`1 << 63`) is orders of magnitude inside it.
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

**MEASURED CORRECTION (the tail batch, §bitwise `&`): the negative-`|`
refusal above is RETIRED.** "Infinite two's complement is not guessed"
was a design-time prediction, not a measurement. Nothing needs to be
guessed — see the next section. The bullet is left standing as the
record of what was believed at pass 5.

## Bitwise `&` (the tail batch, construct 4 — and it retires `|`'s refusal)

**STAGED-PATCH MARKER — DELETE THIS PARAGRAPH WHEN THE TRIAD IS GREEN.**
This section describes a `Semantics.lean` edit that has NOT been built:
it was staged as a patch so that it could land inside one rebuild cycle
together with the other held Lean work. Nothing here is a claim about a
build that has happened. What HAS been measured, before a line of it was
written: the CPython 3.9.19 rows below, and the `intAnd`/`intOr`
formulas, executed against CPython over a 77284-pair grid (154568
operations, 0 mismatches, 0 `ndiff` underflows) with a falsification
self-test — one arm deliberately broken, caught 18778 times.

`&` is admitted with its FULL int semantics, negative operands included,
and `|` is corrected to match in the same landing — landing one with
computed negatives while the other refused them would install exactly the
drift a single operator family must not have.

Lean's `Int` is ALREADY in the complement representation: `Int.negSucc n`
IS `-(n+1)`, so for a negative `x` the number `-x-1` — whose bits are the
complement of `x`'s — is the constructor's own argument, available by
matching and requiring no arithmetic whatsoever. Each operator is a
four-way match on the two constructors over core `Nat.land`/`Nat.lor`,
with one helper `ndiff a m = a - (a &&& m)` (`Nat.ldiff` does not exist on
this toolchain, and none is needed: removing the bits of `a` that are in
`m` IS the difference, and it never underflows).

* **Boolness is decided FIRST**, as it already was for `|`: two bools give
  a BOOL (`True & False is False`), any int operand makes it an int
  (`True & 3 == 1`).
* **The value tier is one function applied three times**, never three
  tables — `intAnd` and `intOr` are the same construction, and `intXor`
  is a rider that can be added the same way if `^` is ever wanted.
* **`{1} & {2}` is set INTERSECTION, not a `TypeError`** — the one trap in
  the row set, and the model already survives it: a set is a heap object,
  so `evalBinOp`'s `.ref` arm fires BEFORE the `TypeError` fallback and
  refuses loudly. No new arm, no invented exception.
* **`&=` arrives free**: one `ALLOWED_BINOPS` entry is consulted by the
  `BinOp` clause AND the `AugAssign` clause, exactly as `|=` was.
* Non-int operands keep the existing fallback, whose message is built from
  `BinOp.symbol` — so `unsupported operand type(s) for &: 'int' and 'str'`
  comes out verbatim for free.

ZERO proof arms, verified at the sites rather than assumed: `evalBinOp`
sits outside every `mutual` block, every walker binds the operator and
drops it, and `fuelMono`/`worldInv`/`ceExecStmt_succ` each `.bind` the
operand IHs and discharge the operator through `.liftRes`, which is
generic over the whole `Res`. There is no operator table in the proof
layer to keep in sync.

NOT in this landing, and deliberately: `>>` (it belongs to the SHIFT
family — `type(True >> True)` is `int`, not `bool` — and it needs a
budget decision it shares with a pre-existing hole in `<<`, whose
unbounded `x * 2^y` would HANG where CPython raises `OverflowError`).
That hole is recorded as a live defect in shipped `<<`, not created here.

*(That hole was closed by `shiftBudget` and the deferral outlived its
cause by four passes; `>>` and `^` land in §the operator remainder
below, found by the grammar census rather than by re-reading this
paragraph.)*

## The operator remainder: `>>`, `^`, unary `+`, unary `~` (§L39 rung 1)

The grammar census (`harness/refusal_census.py --grammar`,
docs/completeness.md) ran one witness per production of CPython 3.9's
`ast` grammar and measured four operators REFUSED whose siblings ran.
The completing landing, and it completes two inventories: `BinOp` is now
missing only `Div` and `MatMult` (both out by KIND — a float result and
an operand type nothing in or out of tier has), and `UnaryOp` is
complete.

**Why each was missing is a different story, and none of them is "it is
hard".**

| operator | the record before the census |
| --- | --- |
| `>>` | DEFERRED with a reason, in §bitwise `&` above: it "needs a budget decision it shares with a pre-existing hole in `<<`". `shiftBudget` closed that hole in the same batch. **The deferral outlived its cause and nothing revisited it.** |
| `^` | named in §bitwise `&` as "a rider that can be added the same way if `^` is ever wanted". It was never wanted, so it was never added. |
| `~` | measured as the **sole** static next wall of a stdlib module in the library sweep (docs/backlog.md, the next-wall table) and never designed. |
| `+x` | not mentioned anywhere in the repository. |

**The semantics.**

* **`>>` is CPython's ARITHMETIC shift**: it rounds toward -inf, which is
  exactly `Int.fdiv` by `2 ^ n` — `-5 >> 1 == -3`, not `-2`. Boolness
  DROPS (`type(True >> True)` is `int`), which the shared `asInt` route
  gives for free.
* **`>>` carries `<<`'s budget, for `<<`'s reason and not a weaker one.**
  Forming `2 ^ y` to divide by would hit the very
  `INTERNAL PANIC: Nat.pow exponent is too big` abort the budget exists
  to prevent. CPython SATURATES above it (a shift past the operand's bit
  length is `0`, or `-1` when negative) and answers instantly;
  saturating here would be exact only under a bound on `x`'s bit length
  that this tier does not have, so the model gives the same loud,
  fuel-independent refusal `<<` gives — never a claim that CPython
  raises. **Owed**: saturation behind a width argument.
* **`^` is `intXor`, and it is the simplest of the three** bitwise
  helpers, because XOR commutes with complement. `Int.negSucc a` IS
  `~a`; `~p ^ q = ~(p ^ q)` and `~p ^ ~q = p ^ q`, so each of the four
  arms is one `Nat` XOR with the sign read off the operands' parity — no
  `ndiff`, no subtraction, nothing to underflow. Boolness is decided
  FIRST as for `|`/`&`: `True ^ False is True`, and any int operand makes
  it an int.
* **`+x` is the identity on an int and `~x` is `-x - 1`** — two's
  complement by definition rather than a bit-level guess. Both DROP
  boolness (`+True == 1`, `~True == -2`): `bool` has no `__pos__` or
  `__invert__`, so int's slot runs. A `.ref` operand is refused loudly,
  exactly as unary `-` already did.
* **`>>=` and `^=` arrive free**: one `ALLOWED_BINOPS` entry is consulted
  by the `BinOp` clause AND the `AugAssign` clause, as `|=` and `&=`
  were.

**The proof-layer cost is TWO `rfl` arms, and the prediction that it
would be zero was wrong in an instructive way.** §bitwise `&`'s check
holds where it was made: `evalBinOp`/`evalUnaryOp` sit outside every
`mutual` block, every walker binds the operator and drops it, and
`fuelMono`/`worldInv`/`clockErase` `.bind` the operand IHs and discharge
the operator through `.liftRes`, which is generic over the whole `Res` —
so the two `BinOp` constructors really did cost nothing, and the build
carried 3545 of 3685 jobs before it stopped.

What it stopped on is the asymmetry between the two sorts. `evalBinOp` is
PURE, so no payload-blindness lemma mentions it; `evalUnaryOpH` exists
because `not` reads the heap for dict truthiness, and
`evalUnaryOpH_swapAt` therefore `cases op` EXHAUSTIVELY. Two new
constructors, two missing alternatives, two `rfl`s — because `+` and `~`
delegate to the pure `evalUnaryOp` exactly as `-` does and never look at
the heap. Recorded because the shape generalizes: **a new constructor of
an operator sort costs the proof layer exactly as many arms as there are
heap-aware dispatchers over that sort**, which is zero for `BinOp` and
one for `UnaryOp`.

**And the survey that priced it wrong has a reusable lesson.** The sites
were enumerated by grepping for `\.usub` — which finds every
`match`/pattern position, because those are written `| .usub =>`, and
misses every `cases op with` arm, because THOSE are written `| usub =>`
with no dot. `evalUnaryOpH_swapAt` was invisible to the survey for
exactly one character. **Grep an operator sort's constructors WITHOUT the
leading dot** (`grep -rn 'usub'`), or the census of its dispatchers is
guaranteed to be short by however many `cases` sites exist.

**Measured before a line was written**, the discipline §bitwise `&` set:
`intXor`'s four arms and `Int.fdiv`-as-`>>` were executed against CPython
3.9.19 over a 95481-pair XOR grid and a 24720-pair shift grid (plus the
`~`/`+` identities and the bool-type rules), 0 mismatches.

## Dict iteration — the census, and the tier it forces (§L51 rung 3)

The H1 inventory left `for k in d` out with "no snapshot shortcut", and
ten interpreter refusal messages ride on that decision. The census
(`harness/refusal_census.py --grammar`, the `dict.*` witnesses) measured
what CPython 3.9.19 actually does and **corrected the plan twice: once
about what is missing, once about what is modellable at all.**

### CORRECTION 1 — the cursor is already BUILT

`for k, v in d.items():` at MODULE scope runs today, and its guard is
already exact:

| witness | model | CPython |
| --- | --- | --- |
| `dict.items` (module scope) | **MATCH** | insertion order |
| `dict.items-update` (value update mid-loop) | **MATCH** | allowed |
| `dict.items-grow` (insert mid-loop) | **MATCH** | `RuntimeError: dictionary changed size during iteration`, VERBATIM |
| `dict.items-in-function` (same loop in a `def`) | **REFUSE** | runs |

So the script executor's `.items()` shell (and `initItemsLoop` beside it)
already implements the live cursor, the re-read per step and the faithful
size guard. **Rung 3 is an EXTENSION of a working cursor to the
closed-function surface and to the bare-key form — not the construction
of one**, and the `RuntimeError` it must produce is inherited rather than
invented. The `shapeVersion` field this document specified for the
purpose is in `Obj.dict` and `dictStore` maintains it (bumped on growth,
not on value update).

### CORRECTION 2 — a same-size key-set change is NOT modellable, ever

The recorded design treated `shapeVersion` as future-proofing for
"deletion/reinsertion". The census says deletion/reinsertion during
iteration cannot be modelled at all, because CPython's answer depends on
its entries-array layout:

| probe (size unchanged throughout) | CPython 3.9.19 |
| --- | --- |
| `del` a key BEHIND the cursor, then insert | `RuntimeError: dictionary keys changed during iteration` — a SECOND, different message |
| `del` a key AHEAD of the cursor, then insert | no error: `[1, 2, 99]` |
| bulk churn: delete 7, insert 7 | no error: `[0, 100, 101, …, 106]` |

The three differ only in where the deletion sits relative to the cursor
and whether the insert triggered compaction. Reproducing them means
modelling the tombstoned entries array AND CPython's resize schedule.
**So: a same-size key-set change during iteration is PERMANENTLY LOUD** —
refused, never guessed, and never given either RuntimeError, because
which one (if any) CPython raises is exactly the layout question.

**A cross-rung dependency falls out of this, and it is the census's most
useful product.** The hazard was unreachable while the sole way to shrink
a dict mid-iteration — `del d[k]` — refused first. **THAT DAY CAME**
(docs/backlog/python-completeness.md §pycomplete-15/16): dict deletion
landed, the churn guard is now REQUIRED rather than merely inherited, and
it is kept. Four shapes were measured before the inch: churning at the
middle or last key raises CPython's SECOND `RuntimeError` (*"dictionary
keys changed during iteration"*), while churning at the FIRST key, or
deleting a key and putting the SAME key back, completes SILENTLY — the
entries-array layout is what separates them. So the regime stays LOUD,
and `dict.keyset-churn` is its witness class. The one churn shape that
MATCHES is `del_churn_then_break`, and not because CPython was silent:
the loop EXITS before the cursor re-reads, so the guard is never reached.

**AND THE MECHANISM IS NOW NAMED, not merely bounded**
(§pycomplete-17). Reaching the same regime through an explicit
`iter`/`next` cursor rather than a `for` shows that "the entries-array
layout" is two facts, not one. `dictiter_iternextkey` raises *"dictionary
changed size"* when `di_used != ma_used` — a SIZE check the model has —
and raises *"dictionary keys changed"* only at the point marked *"We
found an element, but did not expect it"*: `di_len` has reached ZERO
while a live entry still lies ahead of the cursor. So the SAME churn
answers silently one step earlier and raises one step later:

| shape (size unchanged, `d = {1,2,3}`, one `del`, one insert) | CPython 3.9.19 |
| --- | --- |
| churn after yielding key 1 | `1, 3, 9` — **silent** |
| churn after yielding key 2 | `1, 2, 3` then `RuntimeError: dictionary keys changed…` |
| churn BEFORE any `next` | `2, 3, 9` — **silent** |
| churn then the iterator RAN OFF the end | `RuntimeError: dictionary keys changed…` |

`di_len` is a REMAINING-COUNT the model does not carry, and carrying it
would still not be enough: deciding "is a live entry ahead of the cursor"
needs the tombstoned array. **The refusal is therefore not a coarse
approximation of one CPython rule; it is the honest answer to two, and
both would have to be modelled together.** A model that reproduced only
the counter would answer where CPython is silent, and one that
reproduced only the layout would be silent where CPython raises.

### The `iter(d)` cursor (§pycomplete-17/18)

`iter(d)` is the same live key cursor as `enumerate(d)`'s, with the index
taken off — `GenFrame.iterDict (a cur n sv)` beside `enumDict`, stepped
by the same `dictStep` plan, so the three regimes above cannot drift
between the two spellings. Two properties are worth stating because they
are MEASURED rather than conventional:

* **Exhaustion is DISCOVERED, not implied.** An iterator that has yielded
  its LAST key is still live: growing the dict then raises. One that has
  been STEPPED PAST the end is dead — CPython clears its `di_dict`, and
  the model pops the frame on `.done` — so the same growth is silent and
  `next(it, x)` answers `x`. Both fall out of WHERE the pop happens; no
  guard states either. `dict.iter-exhausted` is the witness.
* **`iter` is the THIRD generator allocator.** `Expr.genAllocFree` listed
  `enumerate` and `count`; `iter(d)` allocates an `Obj.generator` exactly
  as they do, and a module classified generator-FREE while holding one
  reports ordinary Python as an internal heap well-formedness violation
  (the 2026-08-13 incident). `dict.iter-for` is the witness that would
  have caught it, and `Expr.heapFree` needed the same carve-out for a
  different reason: `funsHeapFree` is what lets `callNamePlan` conclude
  that a local holding a `.ref` in a heap-free module is a DICT.

The capability opens on the monadic rebuild ONLY: the trunk has no `iter`
arm at all, so — unlike `enumerate`, whose `enumFrame` is shared —
there is no trunk-side capability delta to rule on, and the trunk's
`iterDict` step arm exists to compile and to refuse, the `forDict`
arrangement exactly.

### The genexp cursor (§pycomplete-19) — and the price that was already paid

`next(k for k in d if k != root)` is the flagship's OTHER eviction key
(`sunfish.py:511`), and it cost **zero model sites**. Ingestion lowers an
admitted genexp to a synthesized generator function whose body is
`for k in .0: if …: yield k`, and that `for` over a heap dict is §3a's cursor
reached through `execGen` — so the composition was built before anyone asked
for it. What the inch added is EVIDENCE: every other genexp witness in the tree
iterates a range, a generator or a tuple, and none iterated a dict.

**Two boundaries here are the LOWERING's, not the cursor's, and confusing them
is the trap.** A genexp may capture a parameter the body never assigns (the
flagship captures `self`); it may not capture a body-assigned local, because
the by-value snapshot could go stale, and it may not be BOUND to a name first,
for the same reason. `dict_lab::genexp_next_key` and
`dict_lab::genexp_local_capture_still_loud` are the same construct either side
of that line, and only the second refuses.

**AND THE CURSOR IS BUILT AT CONSTRUCTION, as PEP 289 requires.** The
outermost iterable of a genexp is evaluated *and its iterator created* when the
genexp OBJECT is made, so `g = (k for k in d)` / mutate `d` / `next(g)` raises
here exactly as in CPython. `genInitCont` seeds a synthesized `<genexpr@n>`'s
continuation with its cursor already pushed; `dict.genexp-bound-is-loud` is the
witness. This was `pyc-div-2` between §pycomplete-19 and §pycomplete-20 — the
tier answered where CPython raised — and the row retired when its own guard
began failing.

**IT IS A GENEXP RULE AND NOT A GENERATOR RULE, and the distinction is
witnessed.** Calling a generator FUNCTION runs no code, so CPython has called
no `iter()`: mutate the dict between `g = gen(d)` and the first `next(g)` and
CPython answers `1`, then drains `[3]` — it walks the GROWN dict. That deferred
behaviour is CORRECT and the tier keeps it; `dict.genfun-mutate-after-create`
is the row that fails if a later change makes every generator eager. Only the
OUTERMOST clause is eager (inner `for` clauses stay lazy), and only a DICT
receiver can show the difference at all — `forList` re-reads live, value
sequences are immutable, `forGen` holds no counts.

### The tier this forces

Three regimes, and only three:

* **No mutation, or value updates of EXISTING keys only** — exact,
  insertion order, live re-read per step.
* **Size changes** — the faithful `RuntimeError: dictionary changed size
  during iteration`, raised at the NEXT step (measured: including when
  the change happens on the last iteration, where `StopIteration` would
  otherwise have ended the loop).
* **Same-size key-set changes** — LOUD.

Order itself is settled and needs no doctrine: insertion order,
`del`-then-re-add moves the key to the END, an overwrite keeps its
ORIGINAL position (all measured). This is not the hash-order question
that keeps sets out — it is specified behaviour the model already
stores.

### The inches, ordered by price

* **3b — the DRAINING consumers — BUILT.** `list(d)`, `tuple(d)`,
  `sorted(d)`, `sum(d)`, `max`/`min(d)`, `set(d)`, `any`/`all(d)` and
  `[*d]` (which lowers through `tuple`). **These have no mutation window
  at all**: they drain the keys with no user code running in between, so
  not one of the three regimes above can arise inside them. They need
  only "the keys, in insertion order" — `dictKeys`, one `Array.map`.
  *The recorded refusals cited "live dict iteration" for all of them:
  eight of the ten messages guarded a hazard only two of them can meet.*
  See §the draining consumers, as built.
* **3a — the cursor at function scope, and the bare `for k in d` form.**
  LANDED (2026-08-23-pycomplete-5), on the monadic definition only.
* **3c-i — views and `enumerate` in CONSUMING position.** LANDED:
  `for k in d.keys()`/`.values()`/`.items()` at every scope
  (§pycomplete-5's cursor plus a view KIND), `list(d.keys())` and its nine
  siblings through the ingestion rewrite (§pycomplete-11), and
  `enumerate(d)` on its own `enumDict` frame (§pycomplete-14). The trunk
  refuses to STEP these; the rebuild runs them.
* **3c-ii — the views as FIRST-CLASS values.** REMAINING: `k = d.keys()`
  held across statements, set algebra on keys/items, `==` against a set,
  `reversed`, and the identity-equality rule that makes
  `d.values() == d.values()` False. Needs an `Obj.dictView`.
  `enumerate(d.items())` and `dict(d.items())` are still out here too.
* **3d — `DictComp`**, which rides 3a.

### The draining consumers, as built (inch 3b)

One helper — `dictKeys es = es.map Prod.fst`, the entries array being the
insertion sequence already — and seven value arms, each the `.list` arm
sitting beside it in the same `match` with `dictKeys es` for `xs`. Nothing
allocates that did not already: `list(d)` pushes exactly as `list(xs)`
does, `tuple`/`sum`/`max`/`min`/`any`/`all` allocate nothing, and `set(d)`
runs the ordinary `setDedup` — a no-op on keys, which are distinct by the
dict-key doctrine, RUN rather than assumed away so a hand-built module
cannot slip a duplicate past it.

**The proof-layer price was 19 arms across two walkers, and §L53 called
it.** The census recorded the risk before the inch was written:
`PayloadBlind`'s and `ClockErase`'s dispatchers reach the same `match`,
and their `| _ => exact PBF.unsupported` / `cases obj <;> try exact
.unsupported` catch-alls were LOAD-BEARING on the dict arm being a
refusal. Twelve `ClockErase` arms and seven `PayloadBlind` arms, every one
the adjacent `.list` arm's tactic verbatim (`exact .liftRes hs2 _`,
`exact PBF.ok hs1 _`, `exact PBF.allocList hs1 _`, and the two
`sortedValH` helper blocks with `(dictKeys es).toList` for `xs.toList`).

**The rule this sharpens**: a change that makes a previously-REFUSING arm
DECIDE costs exactly as many proof arms as there are walkers whose
catch-all was leaning on that refusal. A refusal is not free in the proof
layer — it is a case someone else is standing on.

Payload-blindness holds for a structural reason worth keeping: a
`PayloadTwin` is `.generator … .running` on BOTH sides, so the swapped
slot can never hold a dict — the new arms read entries at an address the
twin cannot be, and `swapAt` leaves them alone.

**The regression guard that flipped is the acceptance signal.**
`Examples/python/star_lab/spec.lean` asserted `star_dict` refuses; `[*d]`
now answers CPython's `['x', 'y']`, so the guard became a `#py_check` of
the real value and its `cases.json` row moved `unsupported` → `match`.
That is the only pre-existing expectation the inch moves.

## Annotated assignment (`AnnAssign`, §L49 rung 2)

`x: int = 1` in a FUNCTION BODY is an ordinary assignment, rewritten to
one at extraction. Everywhere else it stays loud. The split is not a
narrowing of convenience — it is where CPython itself puts a semantic
boundary, and the census measured it rather than reading PEP 526 for it.

**What was measured** (CPython 3.9.19, `harness/refusal_census.py`'s
witnesses plus a one-off probe; every row run, none inferred):

| probe | function scope | module scope |
| --- | --- | --- |
| `x: boom() = 1` where `boom` raises | **runs clean** | **raises** |
| `x: Undef = 1` | **runs clean** | `NameError` |
| `x: Undef` (no value) | **runs clean** | `NameError` |
| `__annotations__` afterwards | does not exist | `{'x': <class 'int'>}` |

So in a function body the annotation is not merely unused — it is never
evaluated, and an annotation that could not even be evaluated does not
matter. That is what makes the rewrite EXACT with no condition on the
annotation expression: `List[int]`, a string forward reference, a
division by zero, all identical, because none of them runs.

**Three further measurements fix the boundary.**

* **Order at module scope is VALUE, then the store, then the
  ANNOTATION** — `r.a: t('ANN') = t('VAL')` prints `eval VAL`, `store a
  VAL`, `eval ANN`. A raising annotation therefore leaves the target
  BOUND (measured: `x bound? True 7`). Any future module-scope admission
  has to reproduce that order, which is why it is written down here
  before anyone needs it.
* **A value-less `x: int` binds nothing but LOCALISES its name.** In a
  function, `x: int` followed by `return x` is `UnboundLocalError` — and
  so is `g: int; return g` where `g` is a module global holding 5. This
  is the shape that must never be quietly dropped: a model that treated
  the statement as `pass` would resolve `g` to the module global and
  answer 5 where CPython raises. It is refused as a SHAPE rather than
  case by case, and `ann_lab.ann_novalue_shadows_global` is the row that
  says so.
* **`simple == 0` targets** (`(x)`, `c.a`, `d[k]`) get no
  `__annotations__` entry but still evaluate the annotation, so they are
  their own refusal.

**As built.** One extractor clause, no interpreter change, no proof-layer
change, no new AST node: a function-body `AnnAssign` with `simple == 1`
and a value converts to the `Assign` node it already is. The refusal
`py_kind` splits three ways — `AnnAssign:module-scope`,
`AnnAssign:no-value`, `AnnAssign:non-simple-target` — so the survey's
static telemetry ranks them separately, which is the point of splitting
them.

The one mechanical piece is a `func_scope` flag threaded through
`convert_stmt` beside the existing `module_scope`, set only by the
FunctionDef/NestedDef body conversion and passed down the eight compound
bodies. It is not decoration: `module_scope=False` alone would have
admitted the rewrite inside a CLASS body, where the annotation IS
evaluated. (A class body carrying one is loud today on two independent
counts — `class_unsupported: class-level statements` and
`creation_effects: True` — so the flag buys correctness by construction
rather than by that coincidence, which is the same reason the alias
census re-checks at ingestion.)

**The static binding census needed nothing.** `_target_bound_names` is
already reached for `ast.AnnAssign` through the `AugAssign`/`For` clause,
so the census already counted `x` as bound before the rewrite existed —
the rewrite tells it nothing new, and the value-less form was already
counted as a binding too, which is exactly CPython's localisation.

**Owed, with its price.** Module scope is admissible as a TWO-statement
ingestion rewrite — the assign, then the annotation as an expression
statement, in CPython's measured order — because `__annotations__` is
unobservable in tier (every module dunder but `__name__` refuses
loudly). It is not taken here because rewriting one statement into two
moves `Module.topLevel` indices, which the proof campaign's pins are
stated against (`nth n sbB`), and that blast radius belongs to a pass
that budgets for it.

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

The pass-7 re-pin hit ONE out-of-tier construct: the quiescent-search
ordering line became

```python
for val, move in sorted(((v, m) for m in pos.gen_moves() if (v:=pos.value(m)) >= val_lower), reverse=True):
```

(Engine master's pass-8 spelling is the same construct with the
threshold inlined and the sort DELEGATED — `yield from sorted(((v, m)
for m in pos.gen_moves() if (v := pos.value(m)) >= QS or depth),
reverse=True)` — so everything below applies verbatim; only the filter's
right-hand side changed.)

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
DELEGATES wholesale to `execStmt` holds its inner bindings in the frame
until it finishes — invisible to a function called from inside it.
`scriptFlushCoherent` refuses exactly that overlap: no name assigned
inside a delegated compound may be a name some function body reads. That
is the narrow residue of `suffixConsistent`, which refused it for the
WHOLE live top level.

**THE SEAM IS CLOSED (2026-08-13 for `for`/`try`; 2026-08-15 for
`while … else`.)**
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

* **`while … else` (2026-08-15) — the last one.** `execScriptWhile`
  gained the `orelse` block and now mirrors `execWhile` whole: the
  `else` runs on EXHAUSTION (the test goes falsy) and is SKIPPED by
  `break`, and a `break` inside the `else` belongs to an ENCLOSING loop
  and propagates. Both blocks run through `execScriptStmts`, so both
  publish per statement. The TIER is unchanged — `execStmt`'s `while`
  arm always carried the `orelse`, which is precisely why wholesale
  delegation was ANSWERING correctly and only publishing late.

`for … else` is refused by the shell itself (out of tier, as in the
interpreter), so with `while … else` shelled there is no compound the
executor RUNS without one, and `scriptFlushCoherent`'s only remaining
contributors are the `for … else` shapes it refuses anyway. The guard
stays: it costs nothing and it is the standing tripwire that would catch
the next shell that goes missing. Measured: the `for`/`try` landing
removed the refusal from both sweeps (it was 4 stdlib files) and flipped
`harness/scripts/loop_publish_script.py` — a function called from inside
a top-level `for`, reading a name that loop assigns — from refusal to
CPython-identical output; the `while … else` landing pins all three
exits in `harness/scripts/while_else_script.py` (else-taken by
exhaustion, else-skipped by `break`, and the degenerate false-on-entry
exhaustion), with `readn()`/`readtag()` called from inside each loop so
the file is one the guard used to refuse. It is the corpus's ONLY
`while … else` (and there is no `for … else`), so no pre-existing row
moved.

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

## Starred displays (`Starred` position 1, the tail batch — BUILT 2026-08-13)

`ast.Starred` is three constructs, not one (docs/backlog.md §the tail,
construct 5). Only the DISPLAY position is landed here, because it is the
one that costs nothing: it is a LOWERING in the extractor, so there are
ZERO new AST constructors, ZERO `evalExpr` arms, ZERO walkers and ZERO
proof arms — `fuelMono`, `worldInv` and `ceExecStmt_succ` do not move.
Assignment targets (position 2) and call sites (position 3) stay refused,
loudly.

### The lowering, and why the obvious one is WRONG

    (e1, *a, e2)  ⟶  (e1,) + tuple(a) + (e2,)
    [e1, *a, e2]  ⟶  list((e1,) + tuple(a) + (e2,))
    [*a]          ⟶  list(tuple(a))

`[*a, 3]` looks like `list(a) + [3]`. It is not. `list(x)` ALLOCATES a
fresh heap object, so it returns a `.ref`, and `evalBinOp`'s `.ref` arm
refuses concatenation of heap objects LOUDLY — the obvious lowering
compiles to a refusal. `tuple(…)` is the vehicle instead: it is the
IMMEDIATE-value constructor (str / tuple / namedtuple / `listV` / heap
list snapshot / range / generator all yield a plain `.tuple`), and `+` on
two immediate tuples is an existing `evalBinOp` arm. So `list(…)` appears
ONLY on the outside, where a fresh heap list is exactly what CPython
builds, and never as a concatenation operand.

Consecutive non-starred elements are grouped into ONE tuple display, so
`[1, *a, 9, *a]` costs three `+`, not five.

**Evaluation order survives**, which is what a lowering most easily
breaks: `+` associates left and `evalExpr`'s `binOp` arm binds left then
right, so the operands run in source order — CPython's own.
`harness/scripts/star_script.py` pins it through stdout
(`[p(0), *a, p(9)]` prints `eval 0` before `eval 9`), and the same script
pins that the display is a COPY (`b = [*a]; b.append(7)` leaves `a`
alone).

**What it does to the fragment**, measured at the definition and not
inferred: `Expr.heapFree`'s call arm already excludes `list` (it
allocates) and does NOT exclude `tuple` (it does not), so a lowered LIST
display leaves the fragment exactly as a comprehension does, and a
lowered TUPLE display stays inside it exactly as the plain `.tuple` node
did. Both are pinned in `Examples/python/star_lab/spec.lean`.

### Inherited refusals — the reuse dividend

A dict receiver (`[*d]`, CPython's key iteration) and a set receiver
refuse through `tuple()`'s existing order doctrine; a generator receiver
drains under the existing `moduleGenFree` guard. Nothing new decides
anything.

**One honest MISMATCH, recorded rather than glossed.** `[*5]` is
`TypeError: Value after * must be an iterable, not int` in CPython, while
the lowering raises `'int' object is not iterable` from `tuple()`. Same
exception CLASS, different message. Both harnesses compare the class, so
the row passes; the message divergence is real and is written down here.

### The shadow census — the ONE new boundary

The lowering spells the display as calls of the NAMES `list` and `tuple`,
lookups the source never wrote. CPython's display never performs one
(`BUILD_LIST_UNPACK` is a bytecode), but the interpreter reaches its
builtins only AFTER every shadow-resolving arm, so a module BINDING
either name would run the display through the shadow and be SILENTLY
WRONG. The extractor therefore censuses the whole module (any scope, any
binding form) and refuses every starred display in it —
`Examples/python/star_shadow/star_shadow.py` is the row that catches the
census being dropped. Whole-module and conservative by design: deciding
it per scope would mean re-deciding CPython's scoping rules inside the
extractor, and the f-string lowering's `str` census is the same shape for
the same reason.

### The target refusal is a MEASURED CORRECTION, not a restatement

Position 2 was expected to be refused already, on the ground that
`targetNames` admits plain names only. IT WAS NOT. `unpackSeq` checks
ARITY BEFORE element kinds, so `x, *y = [1, 2, 3]` — whose target ingested
as a structural tuple with an `Unsupported "Starred"` element — answered

    ValueError: too many values to unpack (expected 2)

where CPython binds `x = 1, y = [2, 3]`. A FAKE exception, i.e. a wrong
answer, not a refusal. The whole target now ingests as
`Unsupported "Starred:target"` and the assignment refuses loudly
(`star_lab.star_target`/`star_for`). This was a pre-existing defect the
landing found, and it is the reason position 2's refusal is pinned by row
rather than assumed.

**AS REBASED (2026-08-16): the defect was fixed TWICE, independently, and
both arms are kept because they are not the same rule.** While this
branch sat, master closed the same hole from the STATEMENT side
(`_target_has_starred` at `convert_stmt`'s `ast.Assign` arm — "Starred
assignment targets REFUSE instead of answering a wrong ValueError",
2026-08-15). That one is strictly stronger for an assignment: the whole
`Assign` becomes `Unsupported`, and it is the shape `star_lab.json`
re-extracts to now. The EXPRESSION-side arm here still pays for itself,
because master's covers `ast.Assign` and nothing else: a `for` target, a
`with … as (a, *b)` target and a comprehension target reach only this one.

And what the `for` target actually did was MEASURED rather than assumed,
against CPython 3.9.19, at all three arities that separated the wrong
answers from the loud ones in the `Assign` case:

| probe | CPython | model, master | model, rebased |
| --- | --- | --- | --- |
| `for x, *y in [[1,2,3]]` | `1 [2, 3]` | REFUSE `unpacking targets other than plain names` | REFUSE `assignment target 'Starred:target'` |
| `for x, *y in [[1,2]]` | `1 [2]` | REFUSE, same | REFUSE, same |
| `for x, *y in [[1]]` | `1 []` | REFUSE, same | REFUSE, same |

So `for` was ALREADY loud on master and this arm is a MESSAGE change
there, not a soundness fix — `execFor`'s target check is name-only and
fires BEFORE any arity check, which is exactly where `unpackSeq` differed.
Recorded because the obvious inference from the `Assign` defect — "the
same trap must be open in `for`" — is false, and only the probe says so.

Call sites (position 3) need nothing: `Expr.call`'s `callUnsupported`
already carries `starred args`, measured at implementation time rather
than assumed.

### One census, two lowerings (2026-08-16)

The rule this lane extracted — *a lowering that synthesizes a NAME owes a
census* — now has two payers, and it had two copies of the same code to
show for it: `binds_str` was `binds_any_name` with `names = {"str"}`
inlined, line for line. Collapsed to the one function with two named name
sets, `FSTRING_LOWERING_NAMES` and `DISPLAY_LOWERING_NAMES`, decided
together in `process_file`. Behaviour-neutral and checked as such: 74/74
extractor units, and re-extracting every tracked envelope moved nothing
but the `frontend.version` stamp.

## f-strings (`JoinedStr`, the tail batch, construct 2 — DESIGN)

Chosen over `Delete`, `Constant:bytes`, `Starred` and `With` by the
SEQUENCING PRINCIPLE (docs/backlog.md), which ranks by proof-layer shape
with the count only as a tiebreak. The measured shapes:

* `Delete` MUTATES. `del x` removes a binding and **no `Env` removal
  primitive exists**; `del d[k]` mutates the heap. Both mean `worldInv`
  must be re-established — a fragment change.
* `Constant:bytes` adds a new `RVal` CONSTRUCTOR, which touches every
  value-level match in the interpreter and adds a case to both 18-conjunct
  mutual inductions. The most expensive shape in the batch.
* `Starred` ALLOCATES (unpacking builds a sequence) and reaches into the
  call machinery. `With` retains state across a raise — the dearest.
* `JoinedStr` allocates nothing and mutates nothing: `.str` is an
  IMMEDIATE `RVal` (`| str (s : String)`), not a heap object.

### It is LOWERED, not interpreted — the design's whole point

`f"a{x}b"` is extracted as `"a" + str(x) + "b"`: literal text becomes
`Expr.constant (.str …)`, each field becomes a `str(…)` call, and the
pieces are joined with `binOp Add`. Consequences, all checked against the
existing definitions rather than hoped for:

* **ZERO new AST constructors, ZERO new `evalExpr` arms, ZERO new walkers,
  and ZERO new proof-layer arms.** `fuelMono`, `worldInv` and
  `ceExecStmt_succ` are untouched — there is nothing to prove, because no
  new semantic construct exists. `assert` needed three proof sites; this
  needs none.
* **It stays inside the heap-free fragment.** `Expr.heapFree`'s call arm
  excludes `sorted`/`next`/`enumerate`/`count`/`any`/`all`/`set`/`print`/
  `list`/`dict` — `str` is not among them — and `binOp` recurses
  structurally. So a lowered f-string is heap-free exactly when its fields
  are, which is the same condition a native arm would have given.
* **The rendering is REUSED, not re-decided** — the same property that
  made `assert` cheap, one construct later. `{x}` is `str(x)` is
  `printOne`, so f-strings, `print` and `assert` messages cannot drift,
  and the pinned refusals (a set's hash order, an instance's identity)
  come along unchanged.

### Where the lowering is VALID, and why that fixes the tier boundary

CPython's `{x}` is `format(x, '')`, not literally `str(x)`. The lowering
is therefore sound exactly where `format(v, '') == str(v)`, which holds
for every value in this tier. **That is precisely why the format
mini-language is REFUSED rather than approximated:** the moment a spec is
non-empty the two operations diverge, and a lowering that ignored it would
be a silent lie. The tier line falls out of the reuse criterion instead of
being drawn by taste — conversions are an EXISTING function applied, the
format mini-language is a PARALLEL TABLE, and this development refuses
parallel tables.

### Measured against CPython 3.9.19 before building (`fstring_lab.py`)

IN TIER — literal text, `{expr}`, several fields, expressions and calls
inside a field, `{{`/`}}` brace escapes, the empty f-string, and nesting
(`f"{f'{n}'}"` → `'3'`, which composes for free because an f-string is an
ordinary expression once lowered). The two-level rule is pinned by a PAIR:
`str_field` → `'[hi]'` (a `str` field uses `str()`, so no quotes) against
`list_field` → `"['a', 'b']"` (elements inside a container get `repr()`).

NON-ASCII IS IN TIER, AND WAS MEASURED RATHER THAN PREDICTED.
`nonascii_text` → `'héllo 3'` and `nonascii_field` → `'[héllo]'`. This is
the same fact the `assert` battery got wrong by predicting a refusal
(§the assert statement, MEASURED CORRECTION): a bare `str` renders as
itself, so there is no printability decision to guess. The refusal is real
only INSIDE a container, where `reprVal` must escape.

REFUSED LOUDLY, each for a stated reason, not for convenience:

* `{x:>5}` / `{x:03d}` — the format mini-language (see above). CPython
  gives `'    3'` / `'003'`.
* `{x!r}` — asks for `repr()`, and `repr` is only a name in
  `isPyBuiltinName`, not a tier callable. CPython gives `"'hi'"`.
* `{x=}` — the 3.8 debug specifier needs the field's SOURCE TEXT, which
  the extracted AST does not carry. CPython gives `'n=3'`.
* `{ {1, 2} }` — inherits `printOne`'s set refusal (hash order is never
  guessed). CPython gives `'{1, 2}'`; the model must be LOUD.

`{x!s}` is the one conversion that is IN tier: it measured `'hi'`,
identical to `str()`, so it is `printOne` under another spelling and costs
nothing to admit.

### AS-BUILT — and the design was WRONG about one thing

**UNCOMMITTED-TREE MARKER — DELETE THIS PARAGRAPH WHEN THE TRIAD IS
GREEN.** The section heading above still says DESIGN and this subsection
still says AS-BUILT because the landing is HELD: the widening below is a
`Semantics.lean` edit, and the rebuild it forces was sequenced away from a
timed match running on this box. Measured in this tree with the OLD `str`:
1068 differential cases, 2 failed — `list_field` and `tuple_field`, the
exact two the widening fixes — and 36 scripts, 1 failed, `fstring_script`,
likewise. Nothing here is a claim about a build that has happened.

The lowering is `convert_fstring` in `extractors/python/extract.py`, and
it is the whole implementation: no Lean node kind, no `evalExpr` arm, no
walker, and — as designed — not one line of `fuelMono`, `worldInv` or
`ceExecStmt_succ` moved. Everything below was MEASURED at implementation
time against CPython 3.9.19, and two of the measurements contradict the
design.

**CORRECTION 1 — `{x}` was NOT `printOne`, and the fix is to delete a
stale restriction.** The design's load-bearing claim was "`{x}` is
`str(x)` is `printOne`". The first equality holds; the second did not.
The `str` BUILTIN was pass 8's cast tier (`strOfVal`): value-only, LOUD on
every container and ref, while `printOne` renders containers exactly. So
the lowering as designed refused `list_field` and `tuple_field` — two rows
the design had measured IN TIER — and killed `fstring_script.py` outright
at `f"list={xs} …"`, stdout empty, exit 3.

The narrowness was stale, not principled. `strOfVal`'s own stated reason
was "repr recursion is not guessed", and that reason EXPIRED the same day
it was written, when §rendering landed `reprVal`/`printOne` and taught the
model CPython's two-level rule exactly. `str` had simply been frozen
before the renderer existed. So the fix is `strOfValH` — CPython's `str()`
is `printOne`, delegating to `strOfVal` on the immediates so the scalar
normal form every existing goal has is untouched and the two cannot drift.
It adds no capability: the surviving refusals are `printOne`'s own. It
also fixes the standalone builtin, where `str([1, 2])` had been refusing
for no remaining reason. FOUR references, none in a proof (the def, the
call arm, and the two simp-set lists); the arm keeps its shape
(`Run.liftRes st (…)`, same state in and out), so the meta-theorems see
nothing and `str` stays inside `Expr.heapFree`. **Do not re-freeze it:**
the reason it was narrow is gone, and the next reader should know that
before reading `strOfVal`'s docstring as current.

**CORRECTION 2 — `{x=}` is refused by its CONVERSION, not by missing
source text.** The design said the debug specifier needs source text "the
extracted AST does not carry". It does carry it: CPython bakes `n=` in as
a literal `Constant` at parse time, so `f"{n=}"` and `f"n={n!r}"` have the
SAME AST. What refuses is the specifier's DEFAULT conversion, `!r`. The
proof is `debug_spec_str`: `f"{n=!s}"` — same specifier, conversion made
explicit and in-tier — MATCHES at `'n=3'`. The refusal is real, its
recorded reason was not.

`!a` joins the refusals (the design named `!r` and forgot it): it is
`repr` THEN non-ASCII escaping, two out-of-tier operations, and an
unnamed conversion must never fall through to the in-tier path by
accident — `conversion_ascii` is the row that says so.

### The lowering's ONE new boundary: the `str` shadow census

The lowering spells rendering as a call of the NAME `str`, which is a
lookup the SOURCE NEVER WROTE. CPython's f-string performs no such
lookup — it calls the type's `__format__` — but the interpreter reaches
its `str` builtin only AFTER every shadow-resolving arm, so a module
binding `str` (a py2 shim's `str = unicode`, a parameter, a local) would
have rendered through the shadow and been SILENTLY WRONG. This is the
price of a lowering, and it is paid the way this development pays: the
extractor censuses the whole module for a binding of `str` in any scope
and any form (`binds_str` — `Store`/`Del` names, `def`/`class` names,
parameters, import aliases, `except as`, `global`/`nonlocal`) and refuses
every f-string in such a module LOUDLY. Whole-module on purpose: deciding
it per scope means re-deciding CPython's scoping rules inside the
extractor, a second table, to buy a file nobody writes.
`Examples/python/fstring_shadow` is the pin — `shadowed` and `elsewhere`
refuse (the census is module-wide), while `plain_concat` still runs an
EXPLICIT `str(n)`, which is subject to CPython's real scoping and agrees.

### Measured, as landed

`Examples/python/fstring_lab` is 28 rows — 22 match, 6 refusals
(`!r`, `!a`, two format specs, `{x=}`, a set field) — plus
`fstring_shadow`'s 3, and `harness/scripts/fstring_script.py` is stdout-
identical to CPython 3.9.19 through the top-level `for` shell. Nesting
composes for free (`f"{f'{n}'}"` → `'3'`) because a lowered f-string is an
ordinary expression, and the two-level rule is pinned by the PAIR the
design asked for: `str_field` → `'[hi]'` against `list_field` →
`"['a', 'b']"`.

## Import forms (Pass 0) — the guarded from-import tier (DESIGN)

Normative design, nothing as-built: the implementation is NOT started,
and it rides the next full rebuild (see the landing plan at the end).
This is the c-intrinsics memo's Pass 0 (docs/c-intrinsics-proposal.md
§4, commit f9ac737): NO intrinsics, no modeled module, only the import
FORMS the import-ceiling census measured as paying. One honest split up
front: the missing-module machinery below consumes none of the memo's
owner questions, but the guarded PRESENT-module arm — the one `bisect`
needs — stands or falls with memo question 2 (accelerator-fallback
equivalence, §2.5). A "no" there drops that arm, the rest still lands,
and the ceiling stands at 4/154 as measured.

### The census fixed the surface

docs/import-ceiling-census.md: of 154 stdlib files refusing with
`import` in the wall set, 0 have pure closures, 4 (`bisect`, `quopri`,
`stat`, `opcode`) are pure behind an optional C accelerator, and the
import forms those four need are EXACTLY: absolute
`from X import name, …` and `from X import *`, at module top level,
inside `try:`/`except ImportError:`, with a missing module raising a
CATCHABLE `ImportError`. Verified in the pinned 3.9.19 source: bisect.py
73–76 (`from _bisect import *` / `pass`), quopri.py 14–18 (`from
binascii import a2b_qp, b2a_qp` / handler binds both to `None`), stat.py
192–195 (`from _stat import *` / `pass`), opcode.py 18–21 (`from _opcode
import stack_effect`, then `__all__.append('stack_effect')` — the try
BODY has a second statement, so the guard position below is "direct body
statement", never "sole statement"). No plain `import X` binding, no
relative imports, no dotted packages, no aliases: the corpus never pays
for them, so they stay refused.

### What a from-import MEANS in Pass 0: the importable universe is EMPTY

There is no module system. The benign whitelist rows keep their exact
current treatment (below), and every other admitted from-import RAISES:
`PyErr.importError (modName : String)`, a NEW constructor. The boundary
renders CPython 3.9's exact surface: `errName` = `ModuleNotFoundError`
(3.9 raises the subclass), `errMessage` = `No module named '{modName}'`
— so the uncaught case is `status exn`, exit 1, class line identical to
the oracle. Nothing binds on the success path because there IS no
success path in Pass 0; the fallback path binds by ordinary handler
statements (`a2b_qp = None`), which the try shells already run from the
retained state.

The raise is faithful on two different grounds, split by the PINNED
PLATFORM INVENTORY — a committed data file captured by subprocess from
the pinned interpreter (`sys.builtin_module_names` + `lib-dynload` stems
+ top-level stdlib modules/packages; the census C-table discipline, the
`isPyBuiltinName` precedent — no absence is ever guessed, and the claim
is scoped to the pinned interpreter as shipped, not to arbitrary
site-packages):

* **Module ABSENT from the inventory** (`zzz_no_such_module`): the raise
  is CPython's own behavior. Admitted anywhere at module top level,
  guarded or not; uncaught it exits 1 with CPython's exact class line.
* **Module PRESENT but unmodeled** (`_bisect`, `binascii`, `_stat`,
  `_opcode`): CPython SUCCEEDS here, so a surfaced `ImportError` would
  be a WRONG ANSWER. Admitted ONLY in guarded position — a direct body
  statement of a `try` whose single v0 handler names `ImportError` — so
  the raise is caught by construction and the run continues on the
  fallback branch. Faithfulness of that continuation is the memo's §2.5
  accelerator-equivalence obligation: the model runs the pure fallback
  where CPython runs the C accelerator, and the assertion that nothing
  observable differs is DIFFERENTIALLY TESTED (battery below), never
  taken from the docs. Outside the guard position it refuses loudly,
  message naming the module and the branch problem ("module 'X' exists
  on the pinned platform but is not modelled — outside a
  `try`/`except ImportError:` guard the fallback branch is not
  asserted"). **Guard position is NECESSARY AND NO LONGER SUFFICIENT —
  see §per-module differential admission below.**

### Per-module differential admission (2026-08-16)

The paragraph above says the equivalence assertion is differentially
tested. Until today nothing enforced that, and the numbers say what
happened: measured over the library corpus, **24 distinct accelerators
in ~30 files sit in guard position on a platform-present module, and
exactly ONE had ever been driven.** Library mode then drove a second and
it FAILED — `stat`, 21 of 104 calls (docs/backlog.md §THE TWO DIVERGED
ROWS). An assertion made twenty-four times and checked once is not an
assertion.

So the admission is a REGISTRY, `ACCELERATOR_ADMISSIONS` in
`extractors/python/extract.py`: guarded position admits a
platform-present module **only** when the registry records a measurement
that PASSED, and the entry carries the fallback it was measured on and
the citation. No entry, no admission. The refusal names WHICH failure it
is, so the census can tell "nobody looked" from "we looked and it is
wrong":

| py_kind | meaning |
| --- | --- |
| `ImportFrom:accelerator-unmeasured` | no registry entry — the equivalence has never been driven |
| `ImportFrom:accelerator-diverges` | a registry entry that is measured FALSE |

Entries today, and nothing else is admitted:

* **`_bisect` — ADMITTED.** Library mode 2026-08-16: 15 of 15 comparable
  battery calls agree, 0 diverge, against the real `_bisect`. The rest
  of that battery is loud refusals (`<` across mixed types; the
  designed, unbuilt `list.insert`), never silent agreement.
* **`_stat` — REFUSED, measured.** 21 of 104 calls diverge: C `_stat`
  converts to an unsigned int, so `S_IFMT(-1)` raises `OverflowError`
  and `S_ISDOOR('a')` raises `TypeError`, where the pure fallback
  answers `61440` and `False`. The model is faithful to the file; the
  ADMISSION is what was false.
* **`_opcode` — REFUSED, by inspection, and this one has a COST.** The
  two branches differ in the NAMES they bind: CPython binds
  `stack_effect` and appends it to `__all__`, the `pass` handler binds
  neither. This document already called it "the recorded §2.5
  divergence, unseen because `__all__` is never printed" — and *unseen*
  is not *equivalent*. **`opcode.py`'s program-mode MATCH (the `%`
  landing's flip) is WITHDRAWN by this**: it was a match on empty stdout
  over a module namespace that differs, and the module system (L2) is
  exactly the work that makes that namespace observable. One line of the
  registry reverses it if the owner would rather keep the flip.
* **`binascii` and the other 21 — REFUSED, unmeasured.** `quopri`'s is a
  genuine pure-accel fallback (`if b2a_qp is not None: … else: <pure
  python>`) and may well pass; nobody has driven it, because `quopri`
  walls on `Constant:bytes` first. The rest are `_abc`, `_codecs`,
  `_collections`, `_datetime`, `_decimal`, `_functools`, `_hashlib`,
  `_heapq`, `_io`, `_locale`, `_operator`, `_pickle`, `_sha512`, `_ssl`,
  `_thread`, `_warnings`, `collections`, `grp`, `pwd`, `zipimport` — all
  behind other walls today, all admitted yesterday on nothing.

To ADD an entry: drive the module's public surface through
`harness/library_survey.py` — its CALLS phase IS this instrument, since
it runs the model's fallback against CPython's C accelerator — record
numerator and denominator, and cite the run.

### `except ImportError:` — the recorded first extension lands, narrowly

The exceptions tier (§exceptions) has NO import machinery today:
`PyErr` carries no import kind, and the statically-first handler
resolution refuses every non-admitted class name — both refusal sites
(`Semantics.lean` execStmt's tryStmt arm, ~5222; `Script.lean` try
shell, ~582) say in their own message that "builtin-name matching is
the recorded first extension, not v0". This design lands that extension
AT MINIMUM WIDTH: a PINNED two-row match table — handler names
`ImportError` and `ModuleNotFoundError` both match the kind
`.importError` (CPython's one relevant subclass edge, carried as a
table, never a hierarchy walk). Everything else is untouched: every
other builtin exception name, `except Exception:`, tuple patterns,
`as` bindings all keep today's refusals verbatim. A USER class named
`ImportError` resolves first (`findClass`, the existing
statically-first order) and then matches only `.user cid` — so
`.importError` propagates through it, which is CPython's behavior too
(an admitted `class ImportError(Exception): pass` is a different class
and catches nothing builtin). `raise ImportError` stays refused: `raise`
admits only admitted user classes, unchanged. No battery row pins the
old static-refusal message (checked: no row, no `#guard` names it), so
nothing flips in exc_lab.

### `from X import *`

Missing X (either inventory arm): the raise fires before any binding,
so star changes NOTHING in Pass 0 — same `.importError`, same guard
discipline, same uncaught surface. What star does change is the STATIC
side: its bind set is unknowable without a module, so it is unanalysable
by fiat (next subsection). FUTURE arm, modeled modules only: star = the
pinned export table (`__all__` if the module defines one, else the
underscore-free inventory — CPython's own rule, memo §2.4); anything
beyond the pinned table is loud. Nothing of that arm lands in Pass 0.

### The FUTURE modeled-module arm (owner-gated; sketch, not Pass 0)

When an intrinsics pass lands a modeled module, a from-import of it
binds per the memo's member tiers (§2.2): CONSTANT/FUNCTION/STATEFUL
names bind their in-tier values; everything else binds an OPAQUE
MODULE-MEMBER value. The value kind is an IMMEDIATE `RVal` (sketch:
`RVal.opaqueMember (mod name : String)`) — allocation-free, NO heap
identity, because CPython's value has identity the model must never
claim. Loudness rules: every observation refuses, naming `mod.name` —
call, attribute read, any operator, `==`, `is`, truthiness, rendering
(`print`/f-string/`str`). Binding it is observationally safe for
exactly the §2.2 reason: the tier already holds values it refuses to
observe. This arm is OWNER-GATED with the rest of the memo and is
recorded here only so the Pass 0 constructor is not built in a shape
that forecloses it.

### The admission change — where the refusal lives today, and what narrows

Today there is no bespoke import refusal site AT ALL. `convert_stmt`
(extractors/python/extract.py) has no arm for
`ast.Import`/`ast.ImportFrom`; both fall through to the terminal
`return unsupported(node)`, arriving as `Stmt.unsupported
"Import"/"ImportFrom" text span` with the source text TRUNCATED at
`UNSUPPORTED_TEXT_LIMIT = 200` — a limit the exact-text whitelist
(`benignImportBinds`, Ast.lean) silently depends on (harmless for its
three short rows; recorded, and retired for from-imports by the
structured node). The refusal is then decided at EXECUTION — execStmt's
`.unsupported` arm, `unsupported statement 'ImportFrom'`
(Semantics.lean:5240); script mode skips whitelisted texts and
delegates the rest (Script.lean:598–602) — and the WALL census mirrors
the whitelist by text (`BENIGN_IMPORTS`,
harness/leanpy_survey.py `census()`: `py_kind` Import/ImportFrom, text
not whitelisted → wall `import`). Text-keying on the Unsupported shape
spans five consumers: `benignImportBinds` (Ast.lean:361), `importBinds`
+ `isBenignNtImport` (Json.lean), `scriptImports` (Script.lean:346),
`Stmt.g1Binds` (Semantics.lean:2840), and the survey.

**The narrowing.** The extractor gains an `ast.ImportFrom` arm that
STRUCTURES exactly the paying shape: module top level (`module_scope`,
the flag `convert_stmt` already threads), absolute (`node.level == 0`),
single unqualified module name (no dots), plain names or star, no
`as` aliases — AND (module absent from the pinned inventory OR the node
is a direct body statement of a `try` guarded by `except ImportError:`).
The extractor reads the committed inventory data file; it is already
the envelope's trust boundary (`py_kind`, `text`, `exception_base`,
`has_global` precedents), so the Lean side needs NO inventory in Pass 0
— its semantics raises unconditionally, and the wrong-answer hazard for
present modules is discharged by the admission, plus §2.5's rows.
EVERYTHING ELSE keeps the Unsupported fallthrough VERBATIM, so the
still-refused forms are: plain `import X` (non-whitelisted), relative
imports, dotted/package modules, `as` aliases, non-top-level (function-
and class-body) imports, and the unguarded from-import of a
platform-present module. Consequence, paid for by the narrowness:
envelope-structured ⇔ admitted, so the survey's wall census is correct
with ZERO code change — walls key on `Unsupported` nodes, and a
structured from-import is rightly no longer an `import` wall.

**As-built (Pass 0 implementation, 2026-08-14).** (1) The admission
disjunction as written above (absent OR guarded) never fires for the
two benign whitelist ImportFrom rows — `itertools`/`collections` are
platform-PRESENT and sunfish's imports are unguarded — yet the
envelope-change and canonicalization paragraphs below require them
structured. As built, the extractor's admission carries the exact
benign texts as a third disjunct (`BENIGN_IMPORT_FROM`, extract.py — a
two-row mirror of `benignImportBinds`'s ImportFrom rows with a sync
comment, the `BENIGN_IMPORTS` survey precedent), which is what makes
"structured in the ENVELOPE and canonicalized back at ingestion" true
and keeps envelope-structured ⇔ admitted exact. (2) The pinned
inventory is `extractors/python/platform_inventory.json` (309 modules,
3.9.19), captured by `extractors/python/capture_inventory.py` —
subprocess-asked, never imported; the extractor loads it lazily and a
missing file is a hard `ExtractError`, never a silent empty set.
(3) Guard position is decided on the handler name alone (single
handler, literally `except ImportError:`); a try that is otherwise out
of v0 still carries `try_unsupported` and refuses whole at execution
before any guarded import inside could run — loud, never wrong.

New statement: `Stmt.importFrom (module : String) (names : Array
String) (star : Bool) (sp : Span)` (Ast.lean — a full-rebuild edit).
Ingestion (Json.lean) CANONICALIZES the whitelist collision: a
structured row whose reconstructed text `from {module} import {names}`
hits `benignImportBinds` is rewritten back to the legacy `.unsupported
"ImportFrom" text` node, so all five text-keyed consumers — the
namedtuple census, `scriptImports`, G1, the survey's benign rows — see
today's shape unchanged, one table (Ast.lean), one rewrite site.
Semantics: ONE new execStmt arm, `.importFrom mod _ _ _ => .exn
(.importError mod)` — fuel-free, state unchanged, never `.ok` in
Pass 0. Script mode needs nothing: `execScriptStmts`' generic
`| s => execStmt m fuel st s` fallthrough routes it, and both try
shells match through the new pinned table. `Main.lean` gains the
`errName`/`errMessage` rows. Top-level `importFrom` IS a
`g1ExecCandidate` (the "imports are not candidates" note was about
`.unsupported` statements, which execStmt REFUSES; this one RAISES, and
a raising candidate takes the fold's recorded `.exn` rollback-and-
poison path; the guarded try was already a candidate).

### Walkers, censuses, and the trace-clock invariant

Every binding census gains the arm, and the INVARIANT is: **no import
form is ever bind-invisible.** `Stmt.g1Binds`/`stmtBinds` for
`importFrom` answer the names form with `some names` — an
over-approximation on purpose (Pass 0 binds nothing, the future arm
will, and over-reporting is the poisoning-safe direction) — and the
star form with `Option.none`, unanalysable by fiat. Consequences,
which are the point:

* `moduleClockOk` clause (2) requires every non-clock-import top-level
  statement bind-analysable and not touching `time`. `from x import
  time` reports a `time` bind and FAILS the census; any top-level star
  import is unanalysable and FAILS it. A from-import therefore can NOT
  create a path around the trace-clock discipline: the clock call's
  admission survives only where the poisoned `time` binding provably
  remains the benign import's — exactly the existing statement, now
  quantified over one more statement form. `stmtIsClockImport` and the
  benign `import time` row are untouched (plain Import, legacy shape).
* The namedtuple census (`stmtBinds`) and `initBindable` inherit the
  same conservatism for free, same mechanism.
* `g1Stores`: `some []` (an import stores through no target);
  `binds_str` (the f-string shadow census) is unaffected in mechanism —
  it walks the raw `ast` in the extractor and already counts import
  aliases, so `from x import str` still refuses every f-string in the
  module.

Fragments and proof layer: `importFrom` allocates nothing and never
decides `.ok` in Pass 0, so it stays IN `Stmt.heapFree` by the
`raiseStmt` argument (worldInv is `.ok`-only, invariance vacuous); the
FUTURE binding arm must re-decide that (flip to `false` or re-prove) —
recorded so it is a review point, not a surprise. One new execStmt arm
⇒ one arm each in `fuelMono`/`worldInv` (Obs.lean) and `clockErase`
(ClockErase.lean), all in the fuel-free non-fragment shape; no new
judgment, no appended conjuncts. `PyErr` gains a constructor — derived
`BEq` extends; no `Run` match opens `PyErr` payloads, so no other proof
site moves.

### What breaks (named now, re-measured at landing)

* Survey headline: 167 seeds / 162 REFUSE → `bisect` flips
  REFUSE→MATCH; the census's program-mode flip set is exactly
  {`bisect`}, so 161 is the predicted count and anything else is a
  finding. The `import`-wall population (154) DROPS by the files whose
  admitted-shape from-imports were their only import walls — to be
  MEASURED, not predicted; the file-flip claim is the measured one.
* Envelopes: every re-extracted envelope containing an admitted-shape
  from-import changes — including sunfish's benign `from itertools
  import count` / `from collections import namedtuple`, structured in
  the ENVELOPE and canonicalized back at ingestion. That is the
  JSON-content trap: after re-extraction, edit `pins_common.lean` ONLY
  (the pass-7 split's rule; the per-capstone `pins_*`/`spec.lean` are
  never hand-edited for content).
* exc_lab: nothing flips (no row pins the old `except ImportError:`
  refusal); the `except Exception:` refusal row stands.
* Corpus/script sweeps (86-file in-repo, 27-script corpus): counts
  re-measured in the same triad; no specific flip predicted.
* `leanpy_survey.BENIGN_IMPORTS`: its two ImportFrom rows become
  unreachable in envelopes (structured before the census sees them) —
  harmless, keep the sync comment pointing at the one table.

### What it buys — the measured claim

`bisect` flips on this alone (the census's one program-mode flip).
`quopri`/`stat`/`opcode` become import-clean but still refuse on their
other walls — `del`, `BitAnd`, bytes literals, all tail constructs
already designed/staged — and land only as that tail lands. NOTHING
else moves; no import+other file flips on this design. Honest total:
+1 sweep file now, +3 more with the designed tail.

Battery — a NEW `Examples/python/import_lab` plus one script (the
star_lab discipline: a fresh directory whose rows are registered WITH
the implementation, measured against the pinned CPython first):

* `happy_fallback` — guarded from-import of a missing module, handler
  runs, module completes (differential MATCH).
* `missing_uncaught` — unguarded from-import of an inventory-absent
  module: exit 1, `ModuleNotFoundError: No module named 'zzz'`,
  CPython-identical.
* `star_missing` — `from zzz import *`, guarded and unguarded arms:
  the raise fires before any binding.
* `not_top_level` — a function-body from-import: refused loudly
  (unchanged Unsupported channel), never a fake ImportError.
* `rebind_after_fallback` — the quopri shape: handler binds the names
  to `None`, later code tests them (differential MATCH).
* the §2.5 rows — `bisect`'s pure fallback (`bisect`, `insort`,
  edge cases) differentially against CPython running the real
  `_bisect` accelerator: the equivalence obligation that ADMITS the
  guarded arm, a divergence a blocker, not a footnote.
* acceptance: the sweep's `bisect` row REFUSE→MATCH.

### Landing plan — ONE rebuild, shared with the staged f-strings tail

The f-strings landing is HELD on a `Semantics.lean` rebuild (the
`strOfValH` widening; §f-strings, the uncommitted-tree marker). Pass 0
touches `extract.py`, `Ast.lean`, `Json.lean`, `Semantics.lean`,
`Script.lean`, `Main.lean`, `Obs.lean`, `ClockErase.lean` — the same
FULL rebuild (~60 min; sunfish spec poles ~15 min each, `bound()`
~14.5 min). Composition note: one rebuild carries BOTH batches, in this
order — (1) extractor edits first, then re-extract every envelope;
(2) `pins_common.lean` only, per the JSON-content trap above;
(3) the Lean edits, one build; (4) both batteries (`fstring_lab`'s held
rows and `import_lab`) registered and measured in the SAME triad, and
the f-strings section's uncommitted-tree marker paragraph deleted in
that same landing. If the owner answers NO on memo question 2, the
present-module guarded arm is dropped from the extractor admission
before building; the absent-module machinery and the `except
ImportError:` extension still land, `bisect` does not flip, and the
ceiling stands as measured.

## The `del` statement (the tail batch, construct 3 — BUILT 2026-08-14)

The recorded design (docs/backlog.md §the tail, construct 3) is built as
written for FUNCTION scope, plus the reconciled MODULE-scope arm
(docs/backlog.md §`del` RECONCILED with the one pipeline — written and
committed BEFORE this implementation, with the flip prediction
pre-registered). The construct is `del name, …` over BARE NAMES, plus — since
§pycomplete-16 — a SINGLE SUBSCRIPT target, which extraction admits and
ingestion rewrites to `<dictdel>(recv, key)` under an `exprStmt` (the
THIRD decision site, as `list(d.keys())` becomes `list(<dictkeys>(d))`).
`del` has no value and `exprStmt` discards the value, so the lowering is
exact and the statement needs no `Stmt` constructor. That admission is
SYNTACTIC: `del o[k]` lowers for ANY receiver and the receiver's TYPE is
decided in the evaluator's arm, which refuses a non-dict
(`del.non-dict-receiver`). `del o.attr`, `del xs[i:j]` and multi-target
deletes mixing shapes stay `Unsupported` at extraction (clause 4).

**Surface.** One constructor `Stmt.delStmt (names : Array String) sp`;
`Env.remove` (structural recursion beside `lookup`/`set`) and the pure
fold `delNames : env → List String → env × Option String` threading the
PARTIAL left-to-right effect (CPython really removes `x` before raising
on `nosuch` in `del x, nosuch` — measured row 5); one `execStmt` arm;
the `execScriptOne` arm; the ingestion arm; the trailing rewrite; the
extractor clauses. Proof sites, exactly the recorded pricing:
`Stmt.heapFree` unconditionally `true` (no sub-expression, locals are
not a `World` field), `fuelMono` `Run.le_refl` (fuel-free), `worldInv`
the non-vacuous `.okF rfl` on the ok path, `clockErase` a leaf pair
with NO `ce_norm` (nothing reads heap or clock — `withClock_locals`
aligns the seeded scrutinee). The script arm is OUTSIDE the mutual
block and outside all three inductions.

**Function scope (the recorded census).** Clause 1: `del` targets BIND
(`_assigned_names` gains `ast.Delete`, repairing its recorded
disagreement with `_binding_linenos` — which also makes a deleted
capture a REBIND for the H7 snapshot admission, and a deleted callee a
`_shadowed_calls` hit, both for free). Clause 2: any Load of a del'd
name anywhere in the body refuses the function through
`locals_unsupported` — the channel's third instance; the stated
over-refusals (`rebind_after`, `loop_del` — programs CPython accepts)
are pinned in `del_lab`. The runtime arm's miss case is therefore only
ever `del` of a never-bound name (`del g`/`del nope`/double-del): loud,
never a fabricated `UnboundLocalError`.

**Module scope (the reconciled arm, script surface only).** By §the
publish the frame's locals ARE the module globals and the one pipeline
keeps them complete, so in `execScriptOne`: a locals HIT removes and
publishes; a MISS is decided in measured order — dunder targets loud
(CPython's `del __name__; print(__name__)` prints `builtins`: the
removal uncovers the builtins module's own binding), benign-import
names loud (`benignImportNames` — they bind statically, `import time;
del time` succeeds silently in CPython and a NameError would be
WRONG), definition names loud (static table entries), and anything
else the faithful `.exn (.nameError n)` with the partial effect
retained. Deletion never consults builtins — CPython's `del len` is
the same `NameError` (measured), so no `isPyBuiltinName` gate.

**The trailing rewrite (ingestion, the aliasing precedent).** In the
maximal all-`Delete`/`Pass` SUFFIX of the top level, a del target that
is a `def`/`class`/namedtuple/alias name occurring as a del target
exactly ONCE module-wide is dropped at ingestion (`delTargets` census,
nested compounds included; a statement left empty becomes `pass`).
Sound because the name is certainly bound there and nothing observable
follows; `del f; del f` keeps both and refuses on the second. This is
what runs opcode.py's `del def_op, name_op, jrel_op, jabs_op`
(`del_trailing_script.py` is the opcode-shaped pin).

**Closed-function surface.** A top-level `del` is an exec candidate
whose attempt always refuses (`initExecStmt` runs with EMPTY locals),
taking the rollback that POISONS the targets — `Stmt.g1Binds` is
`some targets`, NOT the recorded "`[]`": `globalsDirty` poisons exactly
`g1Binds ++ g1Stores`, and an empty set would resurface the deleted
name's stale static binding (measured against the definitions; the
recorded open note is superseded). Mention censuses (`stmtRefs`,
`stmtNamesXW`, `yfNames`, `Stmt.allNames`, `Stmt.assignedNames`) all
carry the targets — the conservative direction everywhere
(`defsBoundBefore` ordering, namedtuple/alias recognition,
`scriptFlushCoherent`).

**Battery.** `Examples/python/del_lab` (13 functions, all differential
— 4 in-tier, 3 census-refused incl. the two stated over-refusals, 3
runtime-refused, 2 shape-refused, the module global for `del_global`);
scripts `del_trailing_script` / `del_global_script` /
`del_never_script` / `del_partial_script` / `del_shell_script` (match)
and `del_def_mid_script` / `del_dunder_script` / `del_import_script`
(loud, notes record CPython's side). Pre-registered prediction:
**opcode.py does NOT flip** — its next wall is the DYNAMIC
`%`-formatting refusal at `opname = ['<%r>' % (op,) for op in
range(256)]`, invisible to the static wall census; the acceptance
signal for this landing is opcode's refusal MESSAGE moving from
`unsupported statement 'Delete'` to the `%` arm's.

## Module-level def aliasing (the narrow first-class slice — DESIGN, 2026-08-14)

The Pass 0 landing measured bisect's next wall exactly: behind the
guarded from-import sit `bisect = bisect_right` / `insort =
insort_right` — a top-level `def` referenced as a VALUE, refused by the
first-class-callables gate (`referencing function '…' as a value is
outside the v0 tier`). The refusal is right in general: the tier holds
NO function values — a module `def` is a static `Module.functions`
entry, not an object, so a function-as-value would need representation,
heap identity, a boundary story, and rendering, none of which exist.
This design lands the one shape where none of that is needed: a
MODULE-LEVEL ALIAS OF A TOP-LEVEL DEF, never rebound.

### The mechanism: resolution-level aliasing, pure ingestion

**The alias never becomes a value.** At ingestion (`Json.lean`, the
namedtuple-recognition/`splitChains` precedent — zero interpreter
change), a recognized `alias = name` at module top level (a) pushes a
SECOND `Module.functions` entry — the target's `FunctionDefn` with
`name := alias`, `span := ` the alias STATEMENT's span — and (b)
rewrites the assign to `pass`. Calls through the alias then resolve by
the existing `findFunction` dispatch to a byte-identical defn
(params, `argsOk`/`localsOk`/`hasGlobal`/`isGenerator`, post-lowering
body all copied verbatim), so an alias call runs exactly the direct
call's code under exactly the same `callIn`. Nothing else about the
alias is observable in tier: reading it as a value, `print`ing it,
`is`, rebinding it, crossing the boundary all keep today's loud
refusals. The pass runs LAST in `parseModule` (after the namedtuple
and exception censuses, which must see the original assigns, and after
`lowerGenExps`, so the copy shares the already-synthesized
`<genexpr@n>` helpers instead of duplicating them).

Why not a runtime value in `World.globals`: that IS the first-class
callable gate — the value would need an `Obj`/`RVal` kind, identity
(CPython function objects have addresses), a freeze decision, and every
observation arm — and the closure-dispatch path (`funsHeapFree`/
`topLevelDefFree` guarded) exists for HEAP closures, not static defs.
The static device is observationally equal to CPython's global binding
exactly under the census below: when the binding is single, final, and
ordered, every admissible observation of the alias is a CALL, and the
copy makes calls literally identical. (CPython note, recorded: after
`from _bisect import *` succeeds, CPython's alias points at the C
accelerator where the model's copy is the pure fallback — that is the
standing §2.5 accelerator-equivalence obligation of the guarded import
arm, differentially tested by the `import_lab` fallback rows; the alias
adds no new instance of it.)

**No theorem moves.** The interpreter, the mutual block, and every
induction (`fuelMono`/`worldInv`/`clockErase`) are untouched — there is
no new statement kind, no new arm. The module-level walks are invariant
by construction: `funsHeapFree`/`moduleGenFree` quantify over function
bodies and the copy IS an existing body; the assign→`pass` rewrite
stays inside `Stmt.heapFree`; `topLevelDefFree` never sees the alias
(the assign was not a `defStmt`). Two existing guards EXTEND to the
alias automatically because both key on `Module.functions`:
`defsBoundBefore` (the alias entry's span is the alias statement, so
any top-level mention before it refuses the script — the ordered
admission covers alias names with zero new code) and `initBindable`
(a live rebinding of an alias name is a functions-table name rebinding,
already refused loudly at the publish/flush). One RELOCATION, not a
change: `isBuiltinName`/`isPyBuiltinName` move verbatim from
`Semantics.lean` to `Ast.lean` (same namespace, no consumer changes) so
the ingestion census can consult them — `Json.lean` and
`Semantics.lean` are siblings above `Ast`/`Runtime`.

### The census (all conditions loud-on-failure: a rejected candidate
stays a plain assign, whose RHS keeps today's function-as-value refusal)

Module-wide preconditions (any failure rejects every candidate):

* every top-level statement bind-analyzable under the alias binds walk
  — `stmtBinds` with ONE amendment: a structured `.importFrom` (star
  included) contributes NO binds, because in Pass 0 it RAISES before
  binding (the model's own semantics; the guarded-present-module
  divergence is §2.5's, see above). An `.unsupported` statement (`del`,
  a non-benign import, …) keeps `none` and rejects everything —
  conservative, the namedtuple census's rule;
* no `def`/`class` subtree has `has_global` (the extractor-recorded
  fact; a `global` could rebind the alias or the target at call time).

Per candidate `alias = name`, a DIRECT top-level single-target assign
(post-`splitChains`, so `a = b = f` works via `a = f; b = a`):

* `name` resolves to a top-level def or an EARLIER-ADMITTED alias
  (source-order fold; alias-of-alias is transitive by construction),
  last-wins like `findFunction`. Ordering: a DEF target's span must END
  strictly before the alias statement's line — the check the `pass`
  rewrite would otherwise erase from `defsBoundBefore`'s view; an
  admitted-ALIAS target is ordered by the fold itself (its assign
  already executed — and `splitChains` gives every piece of a chained
  assignment the SAME span while preserving CPython's left-to-right
  execution order, so the span test would wrongly reject
  `chain2 = chain1` inside `chain1 = chain2 = f`; found by the box
  build's `#py_check` on the first battery run);
* `name` is bound by NO top-level statement — except, when `name` is
  itself an admitted alias, its own admitted assign (defs are not
  `topLevel` statements, so any other hit is a rebinding: before the
  alias it would make the copy stale, CPython aliasing the newer
  value; after it, refused anyway) — and is not a class/namedtuple
  name;
* `alias` is a plain non-dunder identifier, not a keyword, not in
  `isBuiltinName`/`isPyBuiltinName` (builtin-shadowing through a
  position-independent table is not claimed; the genexp lowering also
  keys draining builtins by name), not a def/class/namedtuple name
  (rebinding a definition — `initBindable`'s ground), and bound by
  EXACTLY ONE top-level statement (this assign): a later re-alias or
  plain rebinding rejects the candidate.

**Rebind-after-alias is REFUSED, not executed through** — decided
honestly: a static table entry cannot be rebound at runtime, and
execute-through would require exactly the runtime function value this
design declines to build. The refusal is two-layered: admission (the
bound-exactly-once census) and, for hand-built modules, `initBindable`
at the publish/flush. Out of scope, stated: aliases of NESTED defs
(never in `Module.functions`), aliases in class bodies (not top level),
`del alias` (the `del` statement is unsupported, so its file rejects
wholesale until del lands), `__all__` (no import system — it is an
ordinary list binding with no interaction), aliases of classes/
namedtuples/builtins (each keeps its own as-value refusal).

### What flips — measured prediction

From the landed rebuild's stdlib survey (166 seeds, box, python3.9.25):
**exactly one file has this pattern as its CURRENT first wall —
`bisect.py`** (`referencing function 'bisect_right' as a value`). Ten
seeds CONTAIN the pattern at top level (asyncore, bisect, cgi, dis,
gettext, locale, operator, ssl, threading, warnings — operator.py alone
has 47 alias statements), but the other nine sit behind earlier walls
(class-creation effects, mostly), so they cannot flip on this design.
Predicted: wild sweep 6→7 MATCH / 160→159 REFUSE, flip set exactly
{`bisect`}; in-repo corpus no flips (plus the new lab rows); anything
else is a finding. The honest chain for bisect: the FILE flips to MATCH
(its post-alias top level is empty — nothing calls `insort` at import
time), while `insort` CONSUMERS still refuse at `a.insert(lo, x)` —
`list.insert` is not in tier, the recorded §2.5 residue
(`import_insort_fallback` stays UNSUPPORTED until it lands).

### Battery

New `Examples/python/alias_lab` (differential, the star_lab
discipline): the ALIAS CALL ≡ DIRECT CALL pair (same args through both
names, including a keyword-argument row — the kwargs merge reads the
copied params — and a generator-def alias drained by `list`),
alias-of-alias, and the two-step chain via a split chained assignment.
Scripts (scripts.json, oracled against the pinned family):
`alias_script.py` (happy path, MATCH), `alias_before_def.py` (REFUSE —
the ordered admission), `alias_rebound.py` (REFUSE — the decided
semantics; CPython runs it, the model refuses loudly, never wrongly),
`alias_bisect_shape.py` (the bisect shape verbatim: defs, guarded
`from _zzz_nomod import *` fallback, aliases, alias calls printing —
MATCH). Acceptance: the sweep's `bisect` row REFUSE→MATCH.

## `list.insert` — the §2.5 residue (DESIGN, 2026-08-14)

The recorded residue of the Pass 0 / def-aliasing arc: `bisect.py`'s pure
`insort_right`/`insort_left` fallbacks end in `a.insert(lo, x)`, and
`attrCallPlan` knows `append`/`pop` only — so the FILE matches (its
post-alias top level calls nothing) while every insort CONSUMER refuses
(`import_insort_fallback` registered UNSUPPORTED, the honest verdict).
This design lands `list.insert(i, x)` with CPython 3.9 semantics and
closes the open memo-2.5 insort obligation: the row's flip to MATCH —
the pure fallback against CPython's C accelerator, results compared —
IS the discharge.

### Semantics (measured against the pinned 3.9)

CPython's `ins1` (listobject.c) never raises on the index — it CLAMPS:
a negative `i` counts from the end and floors at 0; `i` beyond the end
appends. Measured rows: `[1,2,3].insert(-1, m)` → `[1,2,m,3]`;
`insert(-100, lo)` prepends; `insert(100, hi)` appends;
`[].insert(5, v)` → `[v]`; `insert(True, x)` inserts at 1 (bool is
`__index__`-coerced, `asInt` — pop's rule). The call returns `None` and
mutates in place, visible through every alias. Faithful `TypeError`s,
messages verbatim: a non-int index
(`'str' object cannot be interpreted as an integer` — decided AFTER
argument evaluation, like pop's) and arity
(`insert expected 2 arguments, got {n}` for every n ≠ 2). No float tier
exists, so the int/bool coercion is total on in-tier values.

### The mechanism — append's frame exactly

* **Dispatch**: `AttrPlan` gains `| listInsert`; `attrCallPlan`'s list
  receiver gains the third literal comparison (and its refusal message
  now names `append`/`pop`/`insert`). `execAttrCall` gains the arm:
  evaluate arguments (plan decided BEFORE them, CPython order), then
  `[i, x]` → `asInt`-coerce → the worker; wrong arity/type the faithful
  `TypeError`s above. The KEYWORD call site gains the loud
  positional-only arm (`list.insert() with keyword arguments…`, the
  append/pop wording). No new mutual-block member, no new judgment.
* **Worker**: `heapInsert` beside `heapAppend`/`heapPop` — one
  `Heap.update` writing `(xs.toList.take n ++ v :: xs.toList.drop n)`
  with `n := (if i < 0 then i + xs.size else i).toNat`. The clamp is
  those two lines: `Int.toNat` floors the negative side at 0, and
  `take`/`drop` saturate the high side at `size` (core `List.insertIdx`
  is NOT used — it silently DROPS an out-of-range insert, the opposite
  of CPython's clamp). List-structural, kernel-reducible; joins
  `py_simp`/`interpUnfolds` beside append/pop (Logic.lean, VCTactic.lean).
* **`seqBudget`: no interaction, stated as a rule.** The budget guards
  SINGLE-STEP materialization — one expression that can build an
  unbounded sequence (`range` → list, `tuple * n`). Growth by ONE
  element per fuel-costing call is append's discipline: an insert loop
  is bounded by fuel (`.timeout`), never by budget, and `heapAppend`
  has never consulted the budget. So there is NO budget-exceeded
  battery row — recorded as N/A by design, not an omission.
* **Fragments**: nothing moves. Attribute CALLS are in `Expr.heapFree`
  only at `attr == "get"` (Semantics.lean, the `.get`-only whitelist),
  so an `.insert` call already leaves the fragment syntactically —
  `worldInv` never meets the arm.

### Theorem walks — one arm each at the plan fork, no new conjunct

The arm rides the existing `execAttrCall` frame like append:

* `fuelMono` (Obs.lean): one new plan arm, listAppend's shape
  (`Run.le_bind` over the argument walk, then `Run.le_refl` — the
  worker is fuel-free). The kwargs site's
  `cases attrCallPlan … <;> try exact Run.le_refl _` catch-all absorbs
  the new constructor (its kwargs arm is a plain refusal).
* `worldInv` (Obs.lean): ZERO new arms — its `execAttrCall` conjunct is
  pinned at `attr = "get"` and forks through
  `attrCallPlan_get_heapFree`, whose list-receiver proof gains one
  `if_neg` for the new literal comparison. That lemma edit is the
  whole worldInv cost.
* `clockErase` (ClockErase.lean): one real arm in `ceExecAttrCall` —
  listPop's `asInt` geometry at two arguments (`.bind` the args, cases
  on the list, `.exn` off-arity, `.liftRes` + `of_seed` on `[i, x]`) —
  plus `| listInsert => exact .unsupported` at the three enumerated
  kwargs/ntuple plan sites.

### Extractor and envelopes: untouched

Attribute calls are already structured generically — the
`import_insort_fallback` envelope carries `a.insert(lo, x)` today and
refuses DYNAMICALLY at the plan. Pure method-tier addition: no
extractor edit, NO envelope re-extraction.

### What flips — pre-registered prediction

* `harness/scripts.json`: `import_insort_fallback` UNSUPPORTED → MATCH
  outright — the model runs the pure `insort_right` where CPython runs
  the C accelerator, list printed once at the end; the flip IS the
  memo-2.5 insort discharge. Script corpus 37→38 matched / 9→8 loud
  (plus the new alias-composition script below → 39 matched of 47).
* in-repo survey: flip set among EXISTING files exactly
  {`import_insort_fallback`} — 89→90 MATCH / 20→19 REFUSE, 0 DIVERGE;
  the new script adds one more MATCH row (91/19 at landing).
* **stdlib sweep: NO change — 7 MATCH / 159 REFUSE.** This landing is
  consumer-level only: bisect.py (the one file whose wall chain ends
  here) already MATCHES because its post-alias top level executes
  nothing; no other seed has `list.insert` as its sole wall. Anything
  else is a finding.
* diff_test: the new list_lab rows all match; 0 failed stays.

### Battery

`Examples/python/list_lab` extensions (differential rows +
`#py_check`): the clamping grid through one `ins_at(i, v)` function
(0 / mid / end / beyond-end / −1 / −len / beyond-negative / bool
index), `ins_empty` (insert-into-empty at a beyond-end index),
`ins_alias` (aliasing-visible growth), `ins_ret` (returns `None`),
`ins_insort` (the §2.5 `insort_right` body verbatim, called direct),
and the two faithful `TypeError` rows (non-int index; wrong arity).
Scripts: `import_insort_fallback` flipped to `match`, plus NEW
`insort_alias_script.py` — `insort = insort_right` composed with the
alias tier, calls through the alias, list printed (MATCH). No
budget-exceeded row (N/A by design, above).

## `%`-formatting on strings (DESIGN, 2026-08-14)

`opcode.py`'s SOLE remaining wall, and the honest chain the `del`
landing named. Master's stdlib sweep says so in one number:
`'%' string formatting is outside the v0 tier` is the dynamic wall of
exactly ONE of 166 files, and that file's STATIC wall set is now EMPTY —
the `del` landing cleared its last `Unsupported` node, so nothing but
this operator stands between the sweep and `opcode.py`. It reaches
line 36, `opname = ['<%r>' % (op,) for op in range(256)]`.

### Semantics (measured against the pinned 3.9, before building)

`str % args` is CPython's `unicode_mod`: ONE left-to-right pass over the
format. Literals copy; `%%` emits one `%` and consumes NOTHING; each
conversion consumes the next argument. The argument LIST is the RHS
spread when it is a tuple, and the one-element list `[rhs]` otherwise.
Measured rows, all differential:

* `'<%r>' % (0,)` → `'<0>'`; `'%r' % 5` ≡ `'%r' % (5,)` → `'5'` (the
  bare-argument rule).
* `'%r' % 'x'` → `"'x'"`, `"%r" % "it's"` → `'"it\'s"'` (the quote
  choice), `'%r' % '\n'` → `"'\\n'"`; `'%s' % 'x'` → `'x'`.
* `'%d' % True` → `'1'` while `'%s' % True` → `'True'` (bool is an int
  for `%d` and a bool for `str`); `'%d' % -7` → `'-7'`.
* `'%d%%' % (5,)` → `'5%'`; `'%%' % (1,)` is the leftover TypeError —
  `%%` consumes nothing.
* Arity, both directions, verbatim: `'%d %d' % (1,)` →
  `TypeError: not enough arguments for format string`; `'%d' % (1,2)`,
  `'abc' % (1,)`, `'abc' % 1` → `TypeError: not all arguments converted
  during string formatting`; `'abc' % ()` → `'abc'`. **The leftover
  error has a condition the first version of this design missed — see
  §the mapping right operand.**
* Type: `'%d' % 'x'` → `TypeError: %d format: a number is required, not
  str` — the type name UNQUOTED, unlike this model's other messages.
* Order is the single pass: `'%d %d' % ('x', 1)` raises the `%d`
  TypeError, not the arity one.
* **A namedtuple SPREADS.** `'%s %s' % Move(1,2)` → `'1 2'` and
  `'%s' % Move(1,2)` → the leftover TypeError: `PyTuple_Check` succeeds
  on the subclass. This is not a nicety — a namedtuple treated as ONE
  argument would fabricate `not enough arguments` for a program CPython
  runs, so the arm is REQUIRED, not optional.

### The tier: bare conversions on the SCALAR inventory

Admitted conversions are `%s`, `%r`, `%d`, `%%` and nothing else — no
flag, width, precision, length modifier, or mapping key. Per conversion:

* `%s` is `strOfVal` VERBATIM (str raw; int/bool/None their
  digits/`True`/`False`/`None`).
* `%r` is the same, except a str goes through the shipped `reprStr`
  (quote choice, `\\`/quote/`\n`/`\r`/`\t`/`\xNN` escapes, non-ASCII
  refused) — because `repr` and `str` COINCIDE on int/bool/None. So a
  non-ASCII string refuses under `%r` exactly as it refuses inside
  `print([…])`, and prints raw under `%s` exactly as `print` does: one
  rendering boundary, not two.
* `%d` is `asInt` (bool coerces), else the faithful `TypeError` above.
* A CONTAINER argument (tuple/namedtuple/list/range) under `%s`/`%r` is
  LOUD: its `repr` is `reprVal`'s heap-recursive walk and this operator
  is a pure function of two values that cannot see the heap. A `.ref`
  nested inside a tuple argument is LOUD for the same reason and NEVER
  a `TypeError` built from `RVal.typeName`'s `"object"` placeholder (the
  recorded rule: the placeholder is never part of a decided outcome). A
  `.ref` in operand position never reaches the arm at all —
  `evalBinOp`'s heap-operand refusal already fires, which is why the
  `%(key)s` mapping protocol over a dict RHS is loud today and stays so.

The minilanguage stays refused, and so does every conversion character
outside the four: `%5d`, `%-s`, `%.2f`, `%(k)s`, `%x`, `%i`, `%c`, `%a`.
RECORDED RESTRICTION: the two forms CPython itself REJECTS — `%q`
(`ValueError: unsupported format character 'q' (0x71) at index 1`) and a
trailing `%` (`ValueError: incomplete format`) — are refused LOUDLY here
rather than raised. Deciding them faithfully means pinning CPython's
complete valid-character set and its index arithmetic; a loud refusal is
never a wrong answer, an invented `ValueError` would be. The refusal
message names the character, so the census can still see the demand.

### The mapping right operand (a WRONG ANSWER, fixed 2026-08-16)

The design above is missing one branch of `PyUnicode_Format`, and library
mode found it as a live divergence: **`'  x  ' % [1, 3, 5]` is `'  x  '`
under CPython and was a `TypeError` under the model** (baseline row
`arith.mod`, confirmed by hand at the runner). `'abc' % [1]` likewise.

The C source is the whole explanation. `PyUnicode_Format` sets

```
ctx.dict = args   iff   PyMapping_Check(args) && !PyTuple_Check(args)
                        && !PyUnicode_Check(args)
```

and the leftover check at the end of the pass is guarded
`if (ctx.argidx < ctx.arglen && !ctx.dict)`. So a right operand that
passes `PyMapping_Check` SUPPRESSES `not all arguments converted`
entirely. `PyMapping_Check` is `tp_as_mapping->mp_subscript ≠ NULL`,
measured through `ctypes.pythonapi` on the pinned 3.9.19: **true for
str, tuple, list, dict, range, bytes, bytearray; false for None, bool,
int, float, set.** str and tuple are then struck out by the two `!`
clauses, so within this tier the mapping RHS is exactly `listV` and
`rangeV` — `strFormatMappingRhs`, one predicate, threaded into
`strFormatWalk` as the `mapping` flag its base case consults.

Nothing else about the mapping path changes, and both reasons are
recorded:

* The positional state was ALREADY right. `arglen = -1, argidx = -2`
  means the first conversion receives the WHOLE object and the second is
  `not enough arguments` — which is what the one-element list `[rhs]`
  does. Measured: `'%s' % [1, 2]` → `'[1, 2]'`, `'%s %s' % [1, 2]` →
  `not enough arguments`.
* The `%(key)s` protocol — the OTHER half of `ctx.dict` — is refused
  LOUDLY by the walker and stays refused, so the fix cannot open a path
  to a guessed answer. Note the asymmetry it leaves, pinned as
  `fmt_dict_leftover`: `'abc' % {'k': 1}` is `'abc'` under CPython and
  LOUD here, because `evalBinOp`'s heap-operand refusal fires before the
  arm. That is a declared gap, not a wrong answer.

REVISIT AT H2: `listV` is the transitional value-semantics list. When
lists move to the heap the mapping RHS becomes a `.ref`, and this
predicate must move with them — today `.ref` answers `false` only
because `evalBinOp` refuses it first.

Measured rows, all differential (`fmt_bare_leftover`, `fmt_seq_arg`,
`fmt_dec_seq`, `fmt_range_leftover`, `fmt_dict_leftover` in `str_lab`,
plus the `arith.mod` row the baseline found it on):
`'abc' % [1,3,5]` → `'abc'`; `'abc' % []` → `'abc'`;
`'abc' % range(3)` → `'abc'`; `'abc' % 1`, `'abc' % 'z'`,
`'abc' % None`, `'abc' % True`, `'abc' % (7,)` → the leftover TypeError
still; `'%d %d' % [1,2]` → `TypeError: %d format: a number is required,
not list` (the FIRST conversion, before the second one's arity);
`'%d %d' % 1` → `not enough arguments`. And the loud pair: `'%s' % [1]`
is `'[1]'` under CPython and refuses here, because a container's `repr`
is the heap walk this operator cannot see — the tier's pre-existing
container rule, unchanged.

### Mechanism: one operator arm, and a verbatim MOVE

`evalBinOp`'s `.mod, .str` refusal becomes `strFormat fmt b`. Workers:
`strFormatWalk` (the single pass, `List Char → List RVal → Bool →
String → Res String` since the mapping fix above, structural),
`strFormatMappingRhs` (`ctx.dict`), `strFormatConv` (one conversion on one
argument), `strFormatStr`/`strFormatRepr` (the scalar renderers, defined
THROUGH `strOfVal`/`reprStr` so there is one source of truth for
rendering). Simp doctrine as always: the dispatcher `strFormat` joins
`py_simp`/`interpUnfolds`, the workers stay OUT (the `strSlice`/
`sortInts` freeze family).

The one structural edit: the scalar rendering primitives — `hexDigit`,
`hex2`, `reprQuote`, `reprChar`, `reprChars`, `reprStr`, `strOfVal` —
MOVE VERBATIM up the file, above the operator block, because
`evalBinOp` precedes §rendering and Lean has no forward references. The
alternative was refusing `%r` of a str, which would be a tier boundary
manufactured by FILE ORDER rather than by semantics — the model has the
exact answer and the `print` tier already ships it. No definition
changes, no signature changes; §rendering keeps `reprVal`/`printOne`/
`strOfValH` and now cites the moved block.

### Theorem walks: ZERO arms — the BitAnd precedent, exactly

`fuelMono`, `worldInv` and `clockErase` all handle `binOp` GENERICALLY
(`Run.le_refl` / `.liftResF` / `.liftRes` over the pure `evalBinOp`
result); not one of them cases on the operator. `Expr.heapFree`'s binOp
arm is unchanged: `%` on a str allocates nothing (a str is an
immediate). `evalBinOp` sits outside every `mutual` block, so no
recursion point moves and no conjunct is appended. The `%` arm is
reached identically from the expression arm and from `%=` (augAssign
evaluates through the same pure `evalBinOp`, which is what VC.lean's
recorded augAssign rule states) — one implementation, no second path.

### Extractor and envelopes: untouched

`BinOp:Mod` is the SAME node as integer `%` and has always extracted;
the refusal is DYNAMIC. That is exactly why the static census cannot see
it — `opcode.py`'s wall set is empty on master while the file still
refuses — and the still-refused forms keep the identical shape: a `%5d`
program extracts as a structured `BinOp` and refuses at execution. The
census's blindness to the minilanguage is deliberate and unchanged, and
no envelope is re-extracted for the operator (the battery files are
re-extracted because their SOURCES gain functions).

### What flips — pre-registered prediction

**`opcode.py` flips OUTRIGHT: there is no wall behind `%`.** Measured
before building, not guessed: the same file with line 36's `%` replaced
by an in-tier constant runs END TO END under master's binary and matches
CPython, values included — a probe printing `len(opname)`, `opname[1]`,
`opname[0]`, `opmap["NOP"]`, `len(opmap)`, `len(hasname)`, `hasname[0]`,
`hasconst`, `EXTENDED_ARG`, `HAVE_ARGUMENT`, `cmp_op` just before the
trailing `del` agrees exactly (`256 POP_TOP <op> 9 119 12 90 [100] 144
90 ('<', '<=', '==', '!=', '>', '>=')`). Everything behind the wall is
already in tier: the guarded `from _opcode import stack_effect` (Pass 0;
the model takes the except path — the recorded §2.5 divergence, unseen
because `__all__` is never printed), `__all__ = [...]`, the list
comprehension over `range(256)` (well under `seqBudget`), 119
`def_op`/`name_op`/`jrel_op`/`jabs_op` calls mutating module-global list
and dict through function bodies (the one-pipeline live-view
resolution), the module-level `hasconst.append(100)` lines, and the
trailing `del def_op, name_op, jrel_op, jabs_op` (the `del` landing's
ingestion rewrite).

* **stdlib sweep: 7 → 8 MATCH / 159 → 158 REFUSE, 0 DIVERGE, flip set
  exactly {`opcode`}.** That is the FULL measured price of this slice:
  `%` is the sole wall of exactly one file of 166 today. More flips, or
  fewer, is a finding.
* in-repo survey: flip set among EXISTING files EMPTY — no in-repo file
  has `%` as its wall (sunfish.py's five `%` are integer modulo, and so
  is `listcomp_script.py`'s). The new battery scripts add MATCH rows:
  97 → 99 MATCH of 121, REFUSE 22 → 22 (one new loud script).
* script corpus: 55 → 57 rows, 44 → 45 matched, 11 → 12 loud.
* diff_test: the new str_lab/seq_lab rows all match; 0 failed stays.

### Battery

**AS BUILT (master, 2026-08-14).** Every semantic claim above held on
the box (3659 jobs, 0 errors, oracle 3.9.25): `opcode.py` MATCHES,
stdlib 8/158 with flip set exactly {opcode}, in-repo 98 MATCH / 23
REFUSE of 121, script corpus 57/45/12, diff_test 1213 cases / 0 failed,
and ZERO proof arms moved. The pre-registered in-repo COUNT above
(99/22) is WRONG and is left standing as the record: the arithmetic put
the deliberately-loud new script in the MATCH column. The build's only
failure was `Tests.lean`'s own `%`-refusal regression guard — the
acceptance signal firing exactly where it should.

`Examples/python/str_lab` (differential rows + `#py_check`): the opcode
form `'<%r>' % (op,)` verbatim; `%r` over int/bool/None/str/quote-choice/
escape; the BARE argument (`'%r' % v`) against the 1-tuple; `%s` over
the inventory; `%d` over int/bool/negative; two conversions in one
string; the `%%` no-consume rule; the three faithful TypeErrors (short,
leftover, `%d` on a str) and the left-to-right ORDER row; and the loud
frontier — `%5d` (minilanguage), `%x` (unmodelled character), `%q`
(CPython's own ValueError, refused), a trailing `%`, a container
argument, `%r` of a non-ASCII str (with `%s` of it MATCHING beside it),
and a dict RHS (the pre-existing heap-operand refusal). `seq_lab` gains
the namedtuple SPREAD pair. Scripts: `fmt_script.py` (the opcode shape
at module scope — a `['<%r>' % (i,)]` comprehension, a `def_op`-style
mutator, printed) and `fmt_width_script.py` (expect `unsupported` — the
minilanguage at script level).

## The class tier: creation is an EXECUTION (v0 — DESIGN, 2026-08-14)

The sweep's dominant admission wall, priced BEFORE building it. Since the
`%` landing the dynamic first-wall telemetry reads `class-creation` 106 of
166 stdlib files — the largest single number on the page and, read naively,
the obvious next milestone. It is not, and the honest reason is in §what
this buys below. What follows is the tier this document would build if the
answer were yes, the soundness hole that is worth closing whatever the
answer is, and the measured price.

The instrument is `harness/class_census.py` (`--controls` is the gate: 19
synthetic fixtures with hand-computed verdicts, three real files, and on
every real file a cross-check that the census's feature demands are
non-empty EXACTLY when the extractor's own `creation_effects` is true —
0 violations over 679 top-level stdlib classes). Every number below is
that instrument's, over the pinned 3.9 Lib.

### THE THIRD DOOR — the hole the census found, worth closing alone

`creation_effects` closed two doors: `class C: print("x")` (a class-body
statement) and `class C(base())` (a base expression). There is a THIRD,
and it is open on master: **a decorated METHOD.** Both the extractor
(`extract.py`, `for s in node.body: if isinstance(s, ast.FunctionDef):
continue`) and ingestion (`classBodyStmtPure`, `if k == "FunctionDef" then
pure true`) skip a `FunctionDef` UNCONDITIONALLY, decorator list and all.
So

    def log(f):
        print("registered"); return f

    class C:
        @log
        def m(self): pass

is `creationPure`, `classesCreationPure` admits the module, `parseModule`
drops the `class` statement from `topLevel` entirely, and the decorator
never runs: CPython prints and the model does not. A WRONG ANSWER, not a
refusal — the exact failure mode the creation-effects flag exists to
prevent, through the one door it did not check.

Measured over the stdlib seeds: 15 creation-pure classes in 14 files
carry a decorated method, and in 2 of those files (`shlex`, `sre_parse`)
the class admission passes today. Every one of the 15 decorates with
`property`/`setter`/`classmethod`/`staticmethod` only, so no stdlib seed
actually diverges — the model is lucky, not sound.

**The cheap fix is separable from the tier and should ship whether or not
the tier does**: count a decorated method as a creation effect
(`bool(s.decorator_list)` in the extractor's body loop, one clause in
`classBodyStmtPure`). It costs those 2 files their class admission, flips
nothing (neither is a MATCH today), and closes the door.

### What "executing a class statement" MEANS here

CPython's `class C(B): <suite>` evaluates the bases, executes the suite in
a fresh frame, and hands that frame's locals to the metaclass as the class
dict. The model reproduces the middle step and STATICALLY resolves the
other two:

* **The class statement returns to `Module.topLevel`.** Today `parseModule`
  removes it, which is the last SKIP left after the one pipeline — and a
  skip is exactly what the one pipeline was built to abolish. It comes
  back as a marker `Stmt.classDefStmt (ci : ClassId) (span : Span)`, in
  position, so a class body that reads a module global reads the bindings
  that exist AT the class statement and not the ones that exist later.
* **The body is a suite in its OWN frame.** `execScriptClass` runs the
  body's non-`def` statements through the existing `execStmts` from a
  FRESH `FrameState` (empty locals, the SHARED world), which is CPython's
  class frame: local-then-global resolution, no enclosing-scope lookup —
  identical to the script frame's rule at module level, so the one
  pipeline's live-view resolution serves it unchanged.
* **The namespace is qualified names, not a new value.** On `.next`, the
  class frame's locals are prefixed `"<class>."` and merged into the
  enclosing frame's locals, which the one pipeline publishes as
  `World.globals`. This is the METHOD FLATTENING'S OWN TRICK reused
  verbatim (`"<class>.<method>"` in `Module.functions`; a Python
  identifier can never contain `.`, so plain-name resolution never sees
  them). Zero new `World` component, zero new heap object kind, zero new
  `RVal` constructor, and a class stays UNAVAILABLE as a value — exactly
  as today.
* **`def`s in the body execute to nothing.** They are already represented:
  ingestion flattens them into `Module.functions` under the qualified
  name, and that is the surface `CallsIn m w "Searcher.bound" …`
  specifies. So `execScriptClass` runs the body with its `def`s REMOVED —
  precisely the statements ingestion drops today, in their original order.
  Two admission checks pay for that removal (`classBodyMethodClean`): a
  class-body statement may neither READ nor BIND a name that is one of the
  same class's method names. Both are loud. Measured cost: 2 occurrences
  across the 24 files v0 clears.

### The v0 boundary

**Bases — SINGLE, resolved STATICALLY at ingestion, three forms:**

| form | admitted | `ClassDefn.base` |
| --- | --- | --- |
| no base | yes (implicit `object`) | `none` |
| `class C(object)` | yes | `none` |
| `class C(B)` where `B` is a same-module class | yes | `some ci` |
| `class E(ValueError)` — a builtin exception name | CREATION only, `ok := false` | — |
| two or more bases | **LOUD** — no MRO in v0 | — |

The exception-base row is the two flags doing exactly the job they were
separated for, and it is the single biggest step on the ladder (+15 seed
files), so it is stated rather than implied: a class whose one base is a
builtin exception name has a FAITHFUL creation — the base is a builtin
name lookup with no effect, the body executes, the name binds — and is
**UNINSTANTIABLE**. `E("msg")` is LOUD, because CPython's
`BaseException.__init__` sets `args` and gives the instance exception
protocol, and a plain `Obj.instance` with no `__init__` would fabricate
an object that behaves like neither. `raise E` and `except E` stay
exactly as loud as they are today. The one recognized shape keeps its
own path: `class N(Exception): pass` remains the exceptions tier's
`PyErr.user`. This is the `class Tag: kind = "tag"` precedent —
creation-admissible, not instantiable — and it is why the script runs
while the class refuses.
| `pkg.mod.Class`, an imported name, `dict`/`list`/`str`, a call, a subscript | **LOUD** | — |

Base resolution is by NAME against `Module.classes` at ingestion, so the
world-symbolic covenant is untouched: `findClass` stays static-first and
`ClassId` stays the index. The chain `classChain ci : List ClassId` is a
pure, kernel-computable fold, CYCLE-CHECKED at ingestion (a chain that
revisits a `ClassId` demotes the class loudly — it cannot happen in a
source-ordered module, and it is checked rather than assumed).

**Class-body statements — the executed grammar:**

admitted: `pass`, a docstring, an undecorated `def` (removed, see above),
a plain-NAME assignment whose target is not a dunder, and a bare
expression statement. The right-hand side is any ordinary in-tier
expression, evaluated in the class frame — a literal, a name, a display, a
call, an operator, a subscript, an f-string.

LOUD, each for a stated reason:

* **a decorated method** — the decorator is a call whose result replaces
  the name, and `property`/`classmethod`/`staticmethod` are the DESCRIPTOR
  protocol, which the model does not have. This is the third door, now
  refused instead of skipped.
* **`__slots__`** — binding the name without the STORAGE rule would let
  `self.x = 1` succeed where CPython raises `AttributeError`. Modelling it
  is cheap and it is the first priced extension (§extensions), but a
  half-model is a wrong answer.
* **any other dunder binding** (`__hash__ = None`, `__eq__ = _eq`) —
  a protocol change, and the dunder guard's whole argument is that no
  instance can have one.
* **a comprehension or a lambda on the right-hand side, and a nested
  class** — a class body is not a closure scope in CPython (a
  comprehension inside one cannot see class-level names except its
  first iterable), and a model that ran them in the class frame would
  quietly get that backwards.
* **control flow** (`if`/`for`/`while`/`try`/`with`), `import`, `del`,
  `global`, `raise`, `assert`, `async def`, an annotated assignment, an
  augmented assignment, a non-name target.
* **`metaclass=` and class DECORATORS** — unchanged from today.

**Attributes, methods, instantiation, along the chain.** Lookup order is
CPython's, flattened for single inheritance: instance attrs → this class's
namespace and methods → the base's namespace and methods → … →
`AttributeError`. `attrReadPlan`/`attrCallPlan` gain the chain walk and
stay PURE free-scrutinee plans (the H3 meta-proof discipline is
load-bearing and unchanged). `C(args)` allocates `Obj.instance ci #[]` and
runs the first `__init__` found ALONG THE CHAIN; no `__init__` anywhere on
the chain plus arguments is the faithful `TypeError`. `super()` is LOUD
(it needs the `__class__` cell v0 does not model) — measured cost: 3 of
the 24 v0-cleared seed files call it.

**The dunder guard survives, widened at exactly one clause.** `ok` still
requires no dunder beyond `__init__`, no metaclass, no class decorator, no
multiple bases — and now demands that of every class ON THE CHAIN, which
is what keeps "every live instance has default protocol" true. The clause
that GOES is "class-level statements", because those now execute. So
`class Tag: kind = "tag"` becomes instantiable and `Tag().kind` reads
`"tag"`, where today the class is represented and refuses.

**The two recognized class kinds are untouched.** A `class N(Exception):
pass` stays `PyErr.user` and a `namedtuple(…)` base stays value-like; the
ordinary-class path is the THIRD kind. Their demotion rule extends
verbatim: a demoted candidate gets `creationPure := false` AND
`creationExecutable := false`, i.e. stays loud.

### Admission: `creationPure` narrows, `creationExecutable` is new

`classesCreationPure` stops being a purity gate and becomes
`classesAdmissible`: every class is `creationPure` (nothing observable, so
skipping is sound) OR `creationExecutable` (the effect is one this tier
reproduces). The two flags remain independent and both are recomputed at
ingestion over the parsed body — never trusted from the envelope.

The move is MONOTONE except at one place, and the census proves it:
`unexplained demands ≠ ∅ ⟺ creation_effects` holds with 0 violations over
679 stdlib classes once three forms are excused (a recognized `Exception`
base, a recognized `namedtuple` base, and a decorated method). Which means
**the decorated method is the ONLY shape that is creation-pure today and
not executable under v0** — the single narrowing, and it is the third
door's fix, not a regression.

### What breaks — and the induction question, answered honestly

**It does NOT restructure the 18-conjunct inductions.** The load-bearing
fact, verified at the statements rather than inferred: `fuelMono`
(Obs.lean, 18 conjuncts), `worldInv` (11) and `clockErase` (18) quantify
over the SEMANTICS mutual block only. Script.lean's executor
(`execScriptStmts`/`execScriptOne`/`execScriptFor`/…) is its own mutual
block and appears in NONE of them. Class-body execution lives there, so
its recursion is outside all three.

What each theorem actually sees:

* `Stmt` gains ONE constructor. Sites that name `Stmt.pass` explicitly —
  the proxy for a match that enumerates constructors rather than
  defaulting — number **17** (7 Semantics.lean, 8 Json.lean, 2
  Script.lean), most of them still carrying a catch-all; the arm is a
  one-liner at each. `Stmt.heapFree`,
  `Stmt.genAllocFree`, `Stmt.defFree`, `Stmt.allNames`,
  `Stmt.assignedNames`, `Stmt.g1Binds`, `Stmt.g1Stores`, `Stmt.hasYield`
  are the walkers that need a considered answer rather than a default.
* `execStmt` refuses the new constructor (a class inside a FUNCTION body
  is out of tier), so the three inductions gain **one CASE each inside an
  existing conjunct and ZERO new conjuncts** — `fuelMono` a `Run.le_refl`,
  `worldInv` a `simp at h` on `Stmt.heapFree = false`, `clockErase` a leaf
  pair. This is the `del` landing's recorded pricing, one notch cheaper
  because the arm refuses instead of deciding.
* `worldInv` is **vacuous on the whole tier**: `Module.heapFree` already
  requires `classes = #[]`, so no class-bearing module is in the fragment.
  Nothing about class namespaces can disturb it.
* Script.lean gains one mutual member (`execScriptClass`). Its block
  carries no meta-theorems, so the cost is the definition.
* The REAL proof work is `attrCallPlan`/`attrReadPlan`'s chain walk and
  the frame theorems' side conditions (`attrCallPlan_get_heapFree`,
  `findClass_heapFree`, `getClass?_heapFree`) restated over it — small,
  because in the heapFree fragment `classes = #[]` makes every chain
  empty.

**The value BOUNDARY is where the new loudness lives.** `callFunction`
builds a fresh world, so class namespaces (which are module globals) are
EMPTY there: the closed-function surface cannot see a class attribute. An
attribute miss on an instance whose class has a non-empty static attribute
set must therefore REFUSE on that surface rather than raise
`AttributeError` — a fabricated error would be a wrong answer. Recorded
precedent: the namedtuple boundary refusal. **Class attributes are
`CallsIn`-visible and `CallsTo`-invisible.**

**Censuses that move**: `classesCreationPure` → `classesAdmissible`;
`classBodyStmtPure` gains the decorated-method clause; new
`classBodyMethodClean`, `classBaseResolved`, `classChainAcyclic`;
`defsBoundBefore` is UNCHANGED (it already orders class names, and now the
statement it orders really runs). `leanpy_survey.census`'s `class-creation`
wall predicate must follow the extractor, or the ranking instrument starts
lying about its own frontier.

### What this buys — MEASURED, and the answer is not what the 106 suggests

`harness/class_census.py` over the pinned 3.9 Lib (this laptop: 167 seeds
at 3.9.19; the box's sweep is 166 at 3.9.25 — expect ±1 on every count).

| ladder step | seeds: class wall CLEARED | seeds: FLIPS | library: cleared | library: FLIPS* |
| --- | --- | --- | --- | --- |
| T0 today | 0 | 0 | 0 | 0 |
| T1 body executes, no base | 3 | 0 | 2 | 1 |
| T2 + `object` base | 4 | 0 | 5 | 2 |
| **T3 + same-module base** | 9 | **0** | 11 | 3 |
| **T4 + builtin exception base = v0** | **24** | **0** | **16** | **3** |
| T5 + `__slots__` | 28 | 0 | 18 | 3 |
| T6 + decorated methods | 31 | 0 | 23 | 3 |
| T7 + imported/dotted base | 42 | 0 | 32 | 5 |
| T8 + builtin-type base | 47 | 0 | 38 | 5 |
| T9 + multiple inheritance | 50 | 0 | 42 | 5 |
| T10 + metaclass/decorators/dunder bindings | 78 | 0 | 65 | 8 |
| T11 + everything else | **103** | **0** | 87 | 8 |

\* the library column discounts `import`, the wall the layer below answers.

The table is the census as taken BEFORE the third-door fix, and is left
that way because it is the measurement that produced the verdict. The fix
moves it exactly as much as it should and no more: the two files it newly
walls demand `body:decorated-def` and nothing else, so the denominator
goes 103 → **105**, T0–T5 are unchanged, T6 onward gain 2 (T6 33, T11
105), **v0 still clears 24**, and every FLIPS entry is still 0.

**Read the FLIPS column.** A class tier that admits EVERY form Python has
clears all 103 class-walled stdlib seeds and flips ZERO of them, because
the class wall is the sole wall of exactly none. Six seeds come closest —
`abc`, `code`, `getopt`, `io`, `py_compile`, `string`, whose only walls are
`class-creation` and `import` — and all six are C-REACHING, so even a
Python-only module system underneath does not free them. `graphlib` is the
one class-walled seed that imports nothing at all, and behind its class
wall sit four more constructs (`del d[k]`, an f-string `!r`, a walrus, a
`Starred`).

This is the import-ceiling verdict a second time, and the sole-blocker
rule saying the same thing it said in August: the 106 is a cliff of
ADMISSION ORDER, not of reach. `classesCreationPure` is `runScript`'s
FIRST check, so 106 files stop there and 106 would stop somewhere else
tomorrow.

What the tier IS worth, ranked and honest:

1. **The third door** — a live silent-divergence hole, closable
   independently and cheaply (above). This is correctness, not coverage,
   and it does not need the tier.
2. **The library batch** — 87 of the 141 pure-Python modules in the
   seeds' import-time closures are class-walled, and `class-creation` is
   their top blocker. The full tier clears all 87 and flips 8 with imports
   discounted; v0 clears 16 and flips 3. Real, and still behind a module
   system that is itself priced at single digits (§the import ceiling).
3. **The language surface** — inheritance is the biggest hole left in the
   class model, and `CallsIn` over an inheriting class is a theorem shape
   the project does not have. Worth building for its own sake; not
   justifiable by the sweep.

### Pre-registered flip prediction (written before building)

* **stdlib sweep: 8 MATCH / 158 REFUSE → 8 / 158. The flip set is EMPTY.**
  What moves is the wall census, not the score: `class-creation`'s dynamic
  first-wall count falls by the 24 files v0 clears and rises by the 2 the
  third-door fix newly walls — **106 → 84 ± 1** — with `Import` rising by
  the same 24. Any MATCH flip at all is a finding.
* **in-repo survey: +2 MATCH**, and they are the two class-walled in-repo
  files, both cleared by v0 with no other wall: `cls_lab.py` and —
  pointedly — `cls_effect_script.py`, the file that PINS the
  class-creation refusal. Its `print` in a class body stops being refused
  and starts being reproduced, which is the arc closing rather than a
  regression; the refusal pin MOVES to the new boundary (a decorated
  method, a metaclass, a second base). 98/23 → 100/21 among existing
  files, plus the new scripts.
* **script corpus**: +6 rows (3 matched, 3 deliberately loud).
* **diff_test**: the new `cls_lab` rows land; 0 failed stays.
* **library reach**: v0 clears 16 of 87; unchanged by anything the seeds do.

### Battery

`Examples/python/cls_lab` gains the differential rows: a computed class
attribute (`x = f()`), an attribute read off the class through an
instance, single inheritance with a method resolved on the BASE, a
subclass method SHADOWING the base's, `__init__` inherited from the base,
`__init__` overridden, an attribute shadowed by an instance attribute, the
faithful `AttributeError` at the end of the chain, and the loud frontier —
`__slots__`, a decorated method, a metaclass, two bases, a dotted base, a
`super()` call, a comprehension in the body, a class-body statement
reading a method name. Scripts: `cls_attr_script.py` (computed attributes
at module scope, printed), `cls_inherit_script.py` (the chain, printed),
`cls_effect_script.py` FLIPPED to MATCH, plus `cls_deco_script.py` /
`cls_meta_script.py` / `cls_slots_script.py` as the new loud pins.
`cls_deco_script.py` carries the third door explicitly: a decorator that
PRINTS must refuse, and must never print nothing.

### Priced extensions, in the order the census ranks them

Of the 79 seed files v0 does not clear: decorated methods 42, dunder
bindings 34, `__slots__` 28, dotted base 24, multiple inheritance 15,
imported base 15, builtin-type base 14, body control flow 10, metaclass 9.
`__slots__` is the cheapest real one — `ClassDefn.slots : Option (Array
String)`, an attribute STORE outside the set becoming the faithful
`AttributeError: 'C' object has no attribute 'x'` — and it is worth 4
seed files and 2 library modules on top of v0. Decorated methods are the
descriptor protocol and are not a slice.

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
