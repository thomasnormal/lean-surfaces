# The Python heap layer: memory model (design, normative once implemented)

Status: DESIGN — written before implementation, per the completeness
mandate (2026-08-06). Nothing in this file is built yet; the current tier
is value-semantic and refuses aliasing-visible constructs loudly. This
document is the artifact to review/veto BEFORE the threading refactor
lands.

## Goal

100% semantic completeness is the asymptote: the interpreter should
eventually give faithful semantics to any Python program, with
`Res.unsupported` (loud, never wrong) marking the shrinking frontier.
Dicts, mutable class instances, mutable lists, sets, and generators all
require *object identity*: mutation through one name observable through
another. That requires a heap.

## The model

### Values vs objects

`Val` (immediate values, copied freely, no identity):

| constructor | Python |
|---|---|
| `none`, `bool`, `int`, `str` | the immutable scalars |
| `tuple (xs : Array Val)` | tuples OF VALUES (see "tuple identity" below) |
| `list (xs : Array Val)` | TRANSITIONAL — value-lists of the current tier; migrates to the heap in stage H2 |
| `ref (a : Addr)` | NEW — a reference to a heap object |

`Obj` (heap objects, identity-bearing, mutable in place):

| constructor | Python | stage |
|---|---|---|
| `dict (entries : Array (Val × Val))` | insertion-ordered dict (CPython 3.7+) | H1 |
| `list (xs : Array Val)` | mutable lists (migration of `Val.list`) | H2 |
| `instance (cls : String) (attrs : Array (String × Val))` | class instances (`self`) | H3 |
| `iterator (state : IterState)` | generator frames | H4 |

`Addr := Nat`. `Heap := Array Obj` — the address IS the index;
allocation appends. Addresses never leave the interpreter: the surface
layer (`CallsTo`, theorem statements) is heap-free by construction (see
"call boundary").

### Identity, `is`, `==`

* `is` on two `ref`s is address equality — now FAITHFUL for mutable
  objects (today `is` is in tier only against the `None` literal).
* `is` between immediates other than `None` stays out of tier
  (CPython small-int caching / str interning is implementation-defined).
* `==` on dicts: structural over entries after deref, insertion order
  IGNORED for equality (CPython), recursion through the heap fuel-bounded
  (self-referential objects: `d["x"] = d` — `==` on cyclic structures
  raises RecursionError in CPython; we return `unsupported` at fuel
  exhaustion rather than fake an answer — loud).

### Dict keys

Keys must be hashable = immutable: `none/bool/int/str/tuple`-of-hashables.
A `ref` key (list/dict key) raises the faithful `TypeError: unhashable
type`. Key equality is `==` (with bool/int coercion: `d[True]` is
`d[1]`). Lookup is linear scan over the entry array — semantics, not
performance; insertion order preserved on update-in-place, append on new
key (CPython).

### Tuple identity

Tuples are immutable but CAN contain refs (`(d1, d2)`), and CPython gives
tuples identity too (`is`). `Val.tuple` of possibly-`ref` elements keeps
tuple CONTENTS faithful (aliasing through a tuple works: mutation of
`t[0]` where `t[0]` is a dict ref is visible). Tuple `is` stays out of
tier. This is a deliberate, documented deviation-by-omission: no wrong
answer is ever produced, `is` on tuples is just loudly unsupported.

### Garbage

Unreachability is unobservable in the tier (no `__del__`, no `id()`
reuse, no `weakref` — all loudly unsupported). The heap therefore only
grows during a call; no collector is modeled, and no theorem can tell.

### The call boundary (what keeps the proof surface stable)

`callFunction m fname args fuel : Res Val` KEEPS its signature and its
meaning. Internally the mutual block threads state:

    evalExpr  : Module → Nat → Heap → Env → Expr → Res (Heap × Val)
    execStmt  : Module → Nat → Heap → Env → Stmt → Res (Heap × (Env × Flow))
    …

with `callFunction` allocating a fresh empty heap per TOP-LEVEL call.
Args arriving from the surface (`ToVal` marshalling) are heap-free by
construction; a returned `ref` is resolved by DEEP-FREEZE if the object
graph is acyclic and immutable-representable (a dict cannot be — a
returned dict is `unsupported` until the surface grows a dict-value
form), else loud. Consequence: `CallsTo`/`==>`/`⇓`/`~~>`, every theorem
statement in every example, and the `@[spec]` shapes are UNCHANGED.
Nested (Python-to-Python) calls share the caller's heap — that is the
whole point (a callee mutating a dict argument is visible to the
caller).

CAVEAT (reviewable): fresh-heap-per-top-level-call means module-level
mutable state (a global dict mutated across calls, e.g. sunfish's
`Searcher.tp_score` living across `bound` calls) is NOT yet expressible
at the theorem surface. Sunfish's acceptance test (`Searcher` instance
threading its tables through the search) works because the whole search
runs under ONE top-level call. Cross-call persistent state needs a
surface judgment carrying heap pre/post — deferred to the class stage
(H3), where it can be designed together with `self`.

### Loudness inventory for H1 (dicts)

In tier: dict literals `{k: v, …}`, read `d[k]` (`KeyError` faithful),
write `d[k] = v` (in-place, aliasing-visible), `len(d)`, `k in d` /
`k not in d`, `d.get(k)` / `d.get(k, default)`, `==`/`!=`, truthiness,
iteration `for k in d` (insertion order), `d == d` structural.
Loud (`unsupported`): `.keys/.values/.items/.update/.pop/…` (until
added), `del d[k]`, dict comprehensions, `**kwargs`, `|` merge, returning
a dict from the top-level call, `is` between non-ref operands other than
None-links.

## Staging

* **H0 (landed with this doc): representation.** The extractor emits
  structured `Dict` literals and `Attribute` nodes (schema v0.1
  additions); the interpreter refuses them loudly. Sunfish's census
  gains 19 structured nodes; no semantics change.
* **H1: the threading refactor + dicts.** One commit for the state-shape
  refactor (`Heap` through the mutual block, `fuelMono` re-proved with
  the heap in every conjunct, `py_simp`/`interpUnfolds` updated, the
  VC layer's `EvalsTo`/`PyTriple` shapes re-based, walker repair) — no
  behavior change, all 230 harness rows and all example proofs stay
  green — then a second commit adding `Obj.dict` semantics + differential
  cases + a proved example (target: `piece["Q"]`-style table reads and
  the REAL defining expression `MATE_LOWER/UPPER = piece["K"] ∓/+ 10 *
  piece["Q"]` as module constants, `sf_pst` acceptance example). This is
  a session-scale refactor: `VC.lean`/`VC2.lean`/`VCTactic.lean` build
  Hoare rules directly over the interpreter shapes.
* **H2: lists move to the heap.** `Val.list` becomes `Obj.list`;
  `list +=`, `.append`, slice assignment come IN tier (they are refused
  loudly today). Existing list-example statements keep their surface form
  (args still marshal from `List Int`); proofs need repair where they
  matched on `Val.list`.
* **H3: classes.** `Obj.instance`, attribute get/set, method calls
  (`self` = ref), `namedtuple` as frozen instances; `Searcher`'s
  `tp_score`/`tp_move` tables are the acceptance test, plus the
  cross-call-state surface judgment (see caveat).
* **H4: generators.** First-class iterator objects: a generator frame is
  a heap object holding the paused statement position and locals
  (step-indexed resumption, fuel-bounded), `for` consumes any iterable
  or iterator ref; `yield` inside arbitrary control flow. sunfish's
  `moves()` (search effects interleaved into iteration, consumed lazily
  by `bound`'s cutoff loop) is the acceptance test. NOT a desugaring:
  the mechanism is general (`next()`, partial consumption, multiple live
  generators).

## Proof-layer covenants (must survive the refactor)

1. `fuelMono` extends pointwise: every conjunct gains the heap argument;
   monotonicity is in fuel only, heap is data.
2. Frozen-recursion-point doctrine unchanged: `callFunction`,
   `execWhile`, `execFor` (+ later the generator stepper) stay out of the
   default simp sets; `.eq_n` one-step unfolds remain the manual route.
3. The `#py_check` kernel-reduction convention: everything in the heap
   path is STRUCTURAL recursion (mergeSort trap).
4. `#print axioms` stays `[propext, Classical.choice, Quot.sound]`.
