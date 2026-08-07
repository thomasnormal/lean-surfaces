# The Python heap layer: memory model (v2 — review-corrected design)

Status: NORMATIVE; the H1 core (threading, 2026-08-06), the H1-proper
dict tier (2026-08-07), and the H2 list tier's IN-WORLD half (2026-08-07:
heap `Obj.list` everywhere the interpreter builds a list — literals, G1
module tables, `sorted` results — with the §list-semantics inventory
below) are BUILT to this document. Still pending from it: the H2
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
  -- H3: | instance (cls : ClassId) (attrs : Array (String × RVal))
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
  `.insert/.remove/.index/.sort/...`, slices (H5-adjacent, with strings),
  `del lst[i]`, comprehensions, `.get`-style method calls on lists
  (a faithful `AttributeError` awaiting a `PyErr` form).

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
* **H3: classes.** `Obj.instance (cls : ClassId)` — a unique id, NOT the
  class name (redefinition/nesting/shadowing); class objects eventually
  need heap identity and mutable class attributes themselves.
  `namedtuple` as frozen instances; `Searcher`'s tables and the
  cross-call-state surface land here on top of `CallsIn`.
* **H4: generators.** `Obj.iterator` frames carry a DEFUNCTIONALIZED
  CONTINUATION (expression context, loop/block position, pending
  `try/finally`/`with` state, `send` destination, and status
  created/running/suspended/closed) — not just "paused position +
  locals". sunfish's `moves()` consumed lazily by `bound` is the
  acceptance test.
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
