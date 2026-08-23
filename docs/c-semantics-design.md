# M2 — the C semantic model: DESIGN

**Status: the plan. No interpreter exists.** M1 delivered ingestion
(`docs/backlog.md` §L50): `tools/ctwin/sunfish.c` round-trips into a
literal Lean term and 19 `#guard`s hold. M2 gives that term meaning.

This document is written under the §L25 law — plan before grind, census
before pricing — with `RecursionStep`'s re-pricing as the cautionary
precedent. Every number cited was measured by an instrument in this
repository: `harness/c_construct_census.py` (the corpus),
`harness/c_profile_probe.py` (the host facts),
`harness/c_suite_census.py` (the goal corpora). Nothing is quoted from
memory.

**The target M2's inches climb toward is rung-1 SCORING**
(`docs/c23-goal.md` §4.1): the exit-status corpora at rung-0 vocabulary,
which need no output modeling at all.

> **THE SPEC-MIRROR LAW, adopted at inch 2** (Thomas): *"our lean surface
> for C will read like a Lean translation of the C23 spec — one might read
> the two documents side by side and everything makes sense."* The
> convention — which draft is cited (N3220), the citation form, the
> clause-mirroring layout, and Annex J's three roles — is
> **`docs/c23-spec-mirror.md`**, and it governs every file below.
>
> Adopting it cost three published claims, all corrected in place: C23 did
> NOT define out-of-range conversion to a signed type (§1.2 below), C23
> renumbered every §6.5 operator subclause, and the library clauses moved
> such that C17's `7.24` (`<string.h>`) is C23's `7.24` (`<stdlib.h>`).
> The surface is now namespaced `LeanModels.C.C23` for that reason.

---

## 1 The value model

### 1.1 `CVal` — fixed-width, and the width comes from the profile

```
inductive CVal
  | int   (ty : IntTy) (v : Int)     -- v is the MATHEMATICAL value, in range for ty
  | ptr   (p : Ptr)
  | undef                            -- an indeterminate value that reached a use
```

`IntTy` carries `(signed : Bool, bits : Nat)`, and the bits come from
`docs/c-profile.json` — the ABSTRACT profile, not a host. The corpus uses
**10 integer types** (measured): `int` 4733 nodes, `long` 340, `char`
254, `unsigned char` 173, `uint64_t` 153, `unsigned long` 33,
`unsigned long long` 15, `unsigned int` 6, `uint32_t` 5, `uint8_t` 1.
Under the profile's 8 depended-on facts these collapse to five widths
(8/16/32/64 signed and unsigned) plus `char`'s **signedness, which the
profile pins and which is depended on** — `CLS[(int)p->b[j]]` indexes a
128-entry table by a board byte.

The stored `v` is the mathematical integer, always in range for its type.
That is the invariant every arithmetic rule must re-establish, and it is
what makes "did this overflow?" a decidable question rather than a
convention.

### 1.2 The split the census forced: unsigned WRAPS, signed REFUSES

This is the one value-model decision that cannot be retrofitted, and
`docs/c-tier-charter.md` §2.2(a) measured why: the corpus needs both
behaviors **in adjacent operands**.

* `mix64` (L191-195) is `x *= 0xff51afd7ed558ccdULL` — deliberate
  unsigned wraparound, which C **defines**, at both `*=` sites.
* `PACK_VM` (L649) biases a signed value by `(uint32_t)(val) ^
  0x80000000u`, and `VM_VAL` (L652) converts it back with `(int)(…)` —
  an out-of-range unsigned→signed conversion.

  > **This bullet used to say C23 §6.3.1.3 MANDATES the two's-complement
  > result and that C17 left it implementation-defined. Both halves were
  > wrong.** N3220 §6.3.1.3p3 is word-for-word identical to C11 and C17
  > — "either the result is implementation-defined or an
  > implementation-defined signal is raised" — and `J.3.6(3)` still lists
  > it. What C23 changed is signed REPRESENTATION — normatively at
  > §6.2.6.2p2, whose C17 counterpart offered three representations;
  > §6.2.6.2p6 NOTE 2 is the change-history note. The deleted J.3
  > sign-representation entry is the mandate's auditable trace, and the
  > edition-sensitive definition in `Value.lean` is therefore
  > `IntTy.minVal`, not `convert`. So this is **depended-on implementation-defined behavior**,
  > which is precisely what `docs/c-profile.md` exists to pin, and the
  > pin is a measurement on every host rather than a sentence in the
  > standard. `docs/c23-spec-mirror.md` §4.1.

So:

| operation | rule |
| --- | --- |
| unsigned `+ - *` out of range | **wraps**, modulo 2^bits — defined, never refused |
| signed `+ - *`, unary `-`, `++`/`--` out of range | **REFUSE** (`ub.signedOverflow`) |
| signed → unsigned conversion | modulo, defined since C89 |
| unsigned → signed out of range | **two's-complement wrap — by the PROFILE, not the standard.** §6.3.1.3p3 leaves it implementation-defined (`J.3.6(3)`), in C23 exactly as in C17; the fact is `uint_to_int_wraps`, measured on both hosts and depended on by `VM_VAL` |
| `/` or `%` by zero, and `INT_MIN / -1` | **REFUSE** (`ub.divide`) |
| shift count ≥ width, negative count, negative left operand, signed left-shift overflow | **REFUSE** (`ub.shift`) |

Measured exposure in the flagship corpus: **327 overflow-capable sites**
(211 binary, 101 unary, 15 compound), 19 division/modulo, 17 shifts — and
**zero signed right shifts**, so the profile's `arithmetic_right_shift`
fact is measured and deliberately not depended on.

### 1.3 Floats are a TIER, not a hole

Unchanged from `docs/c-tier-charter.md` §6.2 and confirmed by
`docs/c-profile.md`: **neither development host defines
`__STDC_IEC_60559_BFP__`**, so neither claims Annex F. v0 admits `double`
values, assignment and comparison, and REFUSES every operation whose
rounding it would have to guess. On ctwin's fixed-depth path exactly one
float operation is evaluated — `deadline != 0.0`, both operands exactly
representable — so the claim is exact rather than scoped away.

The suite census sharpens the stakes without changing the decision:
floats are **21% of c-testsuite's format specs and 10% of Fujitsu's**
(§6). They gate a real slice, and the approach remains a named
Thomas-decision (`docs/c23-goal.md` §5.3).

---

## 2 The memory model — what a pointer IS

### 2.1 The decision

```
structure Ptr where
  obj : Option ObjId     -- `none` IS the null pointer
  off : Int              -- byte offset from the object's base
```

**A pointer is (object, offset) with provenance. There is no integer
address to lose provenance to.** This is `docs/c-tier-architecture.md`
§2's decision, re-confirmed against the re-census, and it is
un-retrofittable.

### 2.2 Why locals must be OBJECTS, measured

The Python tier's locals are `REnv := List (String × RVal)` — bindings
with no address. C cannot do that, and the census says so numerically:
**31 sites take `&` of an automatic object and 20 take `&` of a
subobject** (9 of them rooted in an automatic). `struct kcctx c = { … };
gen_moves(p, kc_cb, &c);` (L369-370) is not a corner — it is the corpus's
callback protocol, the mechanism behind all **19 indirect calls** and
every one of its six `*ctx` structs.

> **Correction, made at this inch.** This section previously read "86
> sites take `&` of an automatic object", and so did
> `docs/c-tier-charter.md` §2.2(b) and `docs/backlog.md` §L35/§L57. The
> number came from a guard that could not see the fact it tested:
> `harness/c_construct_census.py` classified a target by
> `referencedDecl.storageClass != "static"`, and **clang's
> `referencedDecl` stub carries no `storageClass` at all** — so the test
> was vacuously true and counted every object designator. Resolving the
> declaration by `id` instead splits the 106 `&` sites into **31
> automatic, 55 file-scope, 20 subobject**. The decision is untouched — 31
> is still 31 more than an environment binding can support — but the
> evidence is a third the size, and `--selftest` now pins the frontend
> fact so the guard cannot go blind again. It is the §L25 law's own
> failure mode: *a guard that cannot see its numbers is decoration.*

So every automatic variable is allocated as an object on block entry with
all bytes indeterminate, and killed on block exit. A pointer to a dead
automatic is a well-formed VALUE; dereferencing it refuses.

### 2.2a Where pointers actually come from — and it is not `&`

The re-census asked a question §2.2 had not: which operations in the
corpus PRODUCE a pointer, and which CONSUME one. The answer reorders the
inch's work.

| produces a pointer | sites | | consumes a pointer | sites |
| --- | ---: | --- | --- | ---: |
| **array-to-pointer decay** | **405** | | lvalue→rvalue load | 1837 |
| function-to-pointer decay | 307 | | `p->f` | **226** |
| `&` (all forms) | 106 | | `x.f` | 184 |
| null-pointer constant | 110 | | `a[i]` | 328 |
| `void*` ↔ `T*` bitcast | 52 | | `*p` | **24** |

**`&` is the third-largest pointer producer, behind decay by 4×**, and
the explicit `*` is the *smallest* consumer — `->` outnumbers it 226 to
24. A memory model built around `&`/`*` would have been built around the
corpus's rare cases. Decay (C23 §6.3.2.1) and `->` (§6.5.2.3, defined as
`(*p).f`) are the operations that carry the traffic, so they are the ones
the inch states first and gates hardest.

Two more rows the model rests on, both measured:

* **250 block-scope objects, of which 0 are `static`.** A block-scope
  `static` has block SCOPE and static DURATION, so it outlives its frame;
  the corpus has none, which is what lets a frame be created and
  destroyed as a unit. The census now reports scope and duration
  separately so this stays a measurement rather than an assumption.
* **Subscript bases**: 139 automatic, 98 file-scope, 73 through a member,
  18 nested. Every one is an array object reached by decay, not an
  integer address — so `(obj, off)` is the shape the corpus indexes in.

### 2.3 Why the allocator is v0, measured

`malloc` 2, `calloc` 1, `realloc` 2, `free` 5 — **all ten on the search
path**, reached through `tpm_store`/`tpm_get` on every search. And
`realloc` (L453-454) **MOVES the transposition table**, so the corpus
exercises **provenance transfer** — old object dies, a fresh object
receives the copied bytes — in its hottest data structure. `Addr := Nat`
cannot express that; `(obj, off)` can.

### 2.4 The byte lattice, and why per-byte

```
inductive CByte | conc (b : UInt8) | ptrByte (p : Ptr) (k : Nat) | indet
```

*(Landed at inch 2 with `k : Nat`, not the `Fin 8` this section first
proposed. `Fin 8` would carry the bound in the type and then need
`Fin.mk` proofs at every construction site, including inside `#guard`s;
the bound is instead enforced where it is actually checked — `loadPtr`
accepts a run only if it is exactly `(List.range 8).map (.ptrByte q)`, in
order, so a torn or short run refuses. Recorded here because the model
and the code land together.)*

Needed per-BYTE and not per-object because `setup_fen` declares `Pos p;`
then `memcpy(p.b, board, 120)` (L1130), leaving `p.score`, `p.h`, `p.ep`,
`p.kp` indeterminate until `pos_seal` runs. A model that refused any read
from a partly-initialized object would refuse the corpus; one that
allowed it would invent values.

A `load ty p` has three outcomes: all-`conc` and a valid representation →
that value; a full in-order pointer run read as a pointer → that pointer,
provenance intact; **anything else REFUSES** — any `indet` byte, a torn
pointer, a pointer run read as an integer.

### 2.5 Effective types — installed now because they fire on nothing

Per-byte `effTy`, per `docs/c-tier-architecture.md` §2.3. The corpus has
**zero `T*`→`U*` punning casts and zero unions** (measured: all 95
explicit casts are `NULL` or arithmetic; all 52 implicit `BitCast`s are
`void*`↔`T*`). That is exactly the condition under which the wall is
cheap to install correctly and expensive to install later — and no
sanitizer on either host detects a strict-aliasing violation, so if the
model does not carry effective types the project has no instrument that
would ever notice one.

### 2.6 What v0 does NOT model

Unions, bit-fields, flexible array members, temporary lifetime (0 sites),
VLAs (0), `volatile` (0), `_Atomic` (0), integer↔pointer casts (0 — which
is what lets the PNVI-vs-PVI question be deferred at zero cost).

---

## 3 The UB taxonomy — REFUSE, with a cause

### 3.1 Three causes, never pooled

`docs/c23-goal.md` §3.1 fixed this for the scoreboard; the semantics has
to produce it. The three retire on completely different schedules:

| cause | retires by | example |
| --- | --- | --- |
| `unsupported` — out-of-tier construct | climbing a rung | `switch` today |
| **`ub` — undefined behavior, refused loudly** | **NEVER — it is the product** | `INT_MAX + 1` |
| `libc` — unmodeled library function | widening the slice (§6 says it is small) | `qsort` |

**"UB-refused never retires: it is the product."** A definitional
interpreter that must DETECT undefined behavior does strictly more work
than a compiler that may assume its absence, and that extra work is the
whole thesis of the lane.

**Annex J.2 is this taxonomy made official, and in C23 it is NUMBERED** —
entries `(1)`-`(221)`, where C17 and C11 had unnumbered bullets. Every
refusal names its J.2 index and its normative clause; the index-to-class
map is `docs/c23-spec-mirror.md` §3, along with the three places the
annex has no entry for something the model refuses (`realloc(p, 0)` among
them) and the one place N3220's own cross-reference is wrong.

### 3.2 The eleven armed classes, and where each fires

| class | detected by | corpus sites |
| --- | --- | ---: |
| signed overflow (`+ - *`, unary `-`, `++`/`--`, compound) | the arithmetic rule's range check | 327 |
| out-of-bounds array/pointer access | **structural** — `(obj, off)` against a size | 328 subscripts |
| pointer arithmetic leaving the object | structural | — |
| null / dead-object dereference | structural (`obj = none`, `live`) | 5 `free` sites |
| invalid shift | the shift rule | 17 |
| division/modulo by zero, `INT_MIN / -1` | the division rule | 19 |
| strict aliasing / effective type | §2.5 — **no sanitizer can** | 0 |
| indeterminate read | §2.4 byte lattice — **no sanitizer available** | 1 real site |
| `realloc(p, 0)` | the allocator rule | 2 |
| unsequenced modification | the sequencing census (§4.4) | 20 residual |
| library-contract UB | per function, in the libc slice | 146 external calls |

Two of these are detectable by NO instrument on either host, and they are
precisely the two the memory model was chosen for.

---

## 4 The evaluation judgment

### 4.1 `Run σ α` transfers verbatim; σ is `CWorld`

`docs/c-tier-charter.md` §2.3 established that the outcome type is
already parametric and its four constructors are the covenant, not
Python. C needs exactly those four. What M2 supplies is σ:

```
structure CWorld where
  mem     : Mem                 -- §2: the object array
  stdout  : List String         -- world DATA, as in the Python tier
  stderr  : List String
  stdin   : List String         -- an INPUT TRACE, loud on underrun
  env     : List (String × String)   -- getenv, marshalled at init
  clock   : List Int            -- the trace clock; EMPTY on the v0 path
  status  : Option Terminal     -- §5
```

The `PyErr` payload of `Run.exn` is the one wart, named in §2.3 of the
charter and now due: either `Run` gains an error parameter (`Run σ ε α`)
or C's terminal outcome rides in `α`. **The decision belongs to the inch
that first needs it** (§7, inch 4), not before.

### 4.1a The evaluator is MONADIC — architecture directive, inch 3 onward

The family is converging on one monad stack plus Lean's `Std.Do`
(WP/`Triple`) machinery with per-language `Spec` lemmas, and the C tier
is to be its first native citizen rather than its second retrofit. So the
evaluator is written in do-notation, not as a hand-rolled
`evalExpr`-returning-`Result` in the Python lane's style.

**THE LAYER ORDER, and it is not the obvious one:**

```
SemM ρ α := ExceptT ρ (StateT CWorld Halt) α        -- state-RETAINING
```

**NOT `StateT CWorld (ExceptT ρ Halt)`.** The `mvcgen` pilot proved by
`rfl` that the state-outside order **DISCARDS THE WORLD ON A RAISE** — a
refusal would forget everything the program had already written, which is
precisely what `Run.exn`'s state field exists to prevent (`Run.exn (state
: σ)`, §4.1). The C tier needs the retaining order for the same reason
Python's `Run` carries state on its error constructor: a refusal must be
able to say *what had happened by the time it refused*, and the
scoreboard's REFUSE rows are worth much less if they cannot.

**Fuel is NOT a monad layer.** It stays an explicit argument threaded at
calls and loops. The pilot's finding is blunt — as a layer it does not
typecheck — and the consequence is welcome: a fuel-free fragment
(everything below a call, which is most of §6.5) is `mvcgen`-native, and
fuel appears only where recursion does. **Decide fuel's fate before
writing each interpreter piece**, not after.

Four consequences, all of which the inches below are shaped to:

1. **Primitive operations are named functions with Spec-lemma-shaped
   contracts** — memory read/write, conversion, the short-circuit step.
   The SHAPE is what makes the comparison possible whether or not
   `mvcgen` is invoked yet.
2. **`@[spec]` IS the altitude-lemma registry.** Same idea the Python
   lane learned the hard way, with the pilot's measurement attached:
   unfolded primitives produced **259 VCs and failed**; four `spec`
   triples produced **12 and closed**. An expensive-operand chain wants a
   spec lemma for exactly the reason it wants an altitude lemma.
3. **Specs must be output-determined, and a bare polymorphic `throw` is
   forbidden** — a `Std` bug makes it unusable, so every refusal routes
   through a NAMED primitive carrying its own `@[spec]`. That is the same
   discipline as "never pool the three causes", arrived at from the
   tooling's side.
4. **The drain amendment survives intact.** A short-circuiting
   construct's out-world rides in the monad's state, and §4.3's
   hypothesis-side discipline becomes a WP precondition — the same rule,
   expressed where the tooling can use it.

**Toolchain check, measured:** `Std.Do` is present in the pinned
toolchain (`v4.33.0-rc1` ships `Std/Do/{WP,Triple,SPred,PredTrans}.olean`),
so nothing here is blocked on a bump.

**Inch 2 is unaffected**, and deliberately so: the memory model's
operations are PURE functions over `Mem`, taking and returning it
explicitly. That is what lets them be lifted into the stack above without
one of them being rewritten — and it is why the layer-order correction
arrived at no cost to work already landed.

### 4.1b Fuel's fate, decided at inch 3 — the expression layer is FUEL-FREE

The family checklist's step 7 (`docs/family-architecture.md` §8.4) makes
this a decision about the interpreter's TYPE, taken before the
interpreter is written. **Taken: `evalExpr` is structurally recursive on
`Expr` and carries no fuel.** Calls — the one expression that can recurse
into an arbitrary body — are delegated to a `CallHandler` that takes the
argument expressions UNEVALUATED, so the recursion needing fuel lives
where fuel will live.

**And that is TWO places, which inch 4's census corrected**: fuel arrives
at **inch 4 with LOOPS** (84 of them — 50 `for`, 29 `do`, 5 `while`; an
iteration count is not structurally bounded, and **20 of the 84 contain
no call at all**, so calls are not what makes them need it) and again at
**inch 5 with CALLS**. Expressions are fuel-free because neither
construct is an expression.

Measured on the shipped corpus: of **1169 full expressions, 871 (74.5%)
contain no call at all.** So the fuel-free fragment — the half the
checklist says gets the shared `mvcgen` and ~120 lines of `@[spec]` — is
the majority of what the corpus is made of, and the cut maximizes it.
Kernel-reducible `#guard` runs come free with structural recursion, which
inch 6's scorer needs and inch 2 already shipped 50 of.

### 4.1c The type-spelling trap, found by inch 3's census

`CType` is clang's unparsed `qualType` string (`docs/c-envelope-schema.md`
§3), so **type equality is SPELLING equality** — and the corpus has **19
binary-operator sites whose operands spell the same type differently**
(`uint64_t` vs `unsigned long long`, `uint32_t` vs `unsigned int`). A
model that compared spellings would see conversions that are not there.

The evaluator therefore RESOLVES rather than compares, through a table
that is the census's own list of the integer spellings that occur, with
widths from the profile. The qualified spellings are tabled too rather
than stripped, because a table refuses an unmeasured spelling where
string surgery would quietly accept one.

**This also validates §4.1's "conversions arrive PRE-SOLVED" claim, which
had never been checked**: of 563 arithmetic and comparison sites, **542
have operand types that resolve equal**, and the 21 that do not are the
19 spelling aliases plus 2 pointer arithmetic. Shifts are excluded on
purpose — §6.5.8p3 promotes each operand separately, so their operands
legitimately differ (17 sites).

### 4.2 The ∃-fuel threshold form transfers unchanged

Every spliced run is stated as *"∃ n, ∀ fuel ≥ n, … = .ok …"*, with
`fuelMono` the monotonicity lemma and side conditions by `omega`.
Induction is on math variables, never on fuel. `#c_check`-style
non-vacuity gates precede any theorem, and kernel-reducibility is a tier
constraint: every helper the interpreter computes with is STRUCTURAL
recursion.

### 4.3 The drain amendment: short-circuit out-worlds

**A short-circuiting construct's out-world is a function of its ANSWER;
the world goes in the hypothesis, not the conclusion.** C makes this
load-bearing at three constructs the census counts precisely:

**Landed at inch 3, as three theorems** (`and_shortCircuits`,
`or_shortCircuits`, `cond_takesOneArm`). Read what they do NOT say: the
unevaluated operand appears in no hypothesis and in no part of any
conclusion, and the out-memory named is the one the HYPOTHESIS introduced
for the operand that ran. A statement of the other shape is unprovable
there, which is the point.

| construct | sites | why it matters |
| --- | ---: | --- |
| `&&` | 111 | the right operand is evaluated ONLY if the left is nonzero |
| `\|\|` | 28 | …only if the left is zero |
| `?:` | 42 | exactly one arm is evaluated |
| `,` | 1 | both, in order, with a sequence point |

So the rule for `&&` is not "evaluate both and combine". It is: evaluate
the left in `w`; **if its value is 0 the answer is 0 and the out-world is
the left's out-world** — the right operand's world never exists to be
spoken about. Stating it the other way round (a conclusion mentioning a
world the run may never reach) is exactly the shape the amendment forbids,
and C has 181 sites of it.

Each of `&&`/`||` is also a SEQUENCE POINT, so the left's side effects are
complete before the right begins — which is what makes the rule
expressible as a two-step threading at all.

### 4.4 Unspecified evaluation order: canonical + census

`docs/c-tier-architecture.md` §3.2's decision stands — execute
left-to-right, and REFUSE where a static census cannot show the order
unobservable. Re-measured on today's corpus with the method now recorded:
**1169 full expressions, 73 with ≥2 effect sites, 53 admitted by
inspection** (an assignment's store is sequenced after the whole right
operand), leaving **20 for the may-alias check** — against the
architecture memo's estimate of 32. Four-effect full expressions are the
worst shape, at 20 sites.

### 4.5 Unspecified behavior: the J.1 register, and Thomas's ∀-order ruling

§4.4's canonical-order decision is superseded in its CLAIM, though not in
its implementation. Thomas ruled:

> **"A program is only correct if it would be correct under any argument
> evaluation order. Since you don't know which the hardware is going to
> choose."**

So the evaluation order becomes an explicit PARAMETER of the semantics —
declared like the profile, never ambient — the interpreter stays
deterministic given the parameter (the ∃-fuel threshold form is
untouched), and **correctness theorems quantify: ∀ order, the same
observable.** Left-to-right remains the canonical order for extracting
witnesses and for scoring suites; it is simply no longer the claim.

**The partition does half the work, and it is spec work.** §6.5.1p2's
*unsequenced* conflicting side effects are already UB — `J.2(34)`,
REFUSE, not a quantifier. §6.5.3.3p10's *indeterminately sequenced*
argument evaluations are the actual ∀ domain — `J.1(16)`. Getting that
line right is what keeps the quantifier small.

**And it is small. Measured** (`harness/c_construct_census.py`):

| row | value |
| --- | ---: |
| call sites with ≥2 args and an effect in any of them — the whole `J.1(16)` domain | **7** of 320 |
| call sites with TWO effectful arguments | **0** |
| binary operators with an effect in BOTH operands (of 891 unsequenced) | **0** |

The seven are `map_find_h:L428`, `fmt_move:L978`, `printf:L1301` and four
`set_knob` sites; at every one the effectful argument is a nested call
and its siblings are address computations or plain scalar reads. So the
per-site obligation is "can this callee write what these siblings read" —
an effect-summary question, priced at 7 sites rather than 320, and owed
at the calls inch.

**Scoring gains a class**: a suite test whose expected output depends on
one particular order is, under this ruling, an INCORRECT PROGRAM — not a
MATCH even when the reference compiler's order agrees. Whether any
reachable test is in that class is a measurement owed at inch 6, not an
assumption.

The full register, with the pick-and-declare / refuse / measure
disposition of every J.1 item the tier touches, is
`docs/c23-spec-mirror.md` §5. **An item enters the register when an inch
touches it and is decided then — never silently.**

---

## 4.6 Inch 4's shape, decided from its census

The statement census, run while queued for the build lock:

| kind | sites | | kind | sites |
| --- | ---: | --- | --- | ---: |
| **(expression statement)** | **297** | | `DoStmt` | 29 |
| `IfStmt` | 253 | | `BreakStmt` | 8 |
| `DeclStmt` | 228 | | `GotoStmt` | 7 |
| `CompoundStmt` | 224 | | `ContinueStmt` | 6 |
| `ReturnStmt` | 103 | | `WhileStmt` | 5 |
| `ForStmt` | 50 | | `LabelStmt` | 3 |
| | | | **TOTAL** | **1213** |

### 4.6.1 Fuel arrives HERE, and the census is why

§4.1b established that expressions are fuel-free. Statements are not:
**84 loops** (50 `for`, 29 `do`, 5 `while`), and an iteration count is
not structurally bounded. **20 of the 84 contain no call at all**, so it
is the loop, not the call, that forces fuel — which is what corrects the
inch-3 draft's "fuel arrives at inch 5".

So `execStmt` takes fuel and recurses on it at exactly one place: the
loop step. Everything else stays structural on `Stmt`. The
`∃ n, ∀ fuel ≥ n` threshold form (§4.2) is assembled around `execStmt`,
and `fuelMono` is owed for it.

### 4.6.2 TIMEOUT is not a refusal, so it does not live in `Except`

`docs/c23-goal.md` §3 is explicit: *"TIMEOUT — fuel exhausted. The only
exhaustion outcome; never conflated with REFUSE."* And the Python tier's
`Run` agrees structurally — `.ok` and `.exn` carry state, **`.timeout`
carries none**, because a timeout is not an observation of anything.

That is precisely what the family stack's `Halt` base is for:

```
ExecM α := ExceptT Refusal (StateT Mem Halt) α
```

with `Halt` carrying fuel exhaustion and nothing else. A timeout
discards the memory, correctly: there is no world to report because
nothing was observed.

**One deliberate divergence from Python, recorded rather than drifted
into.** Python's `Run.unsupported` carries no state either; C's
`Refusal.unsupported` **does**, because it rides in `ExceptT` with the
other refusals. That is wanted: the inch-6 scoreboard's REFUSE rows are
worth more when they can say what had happened by the time the model
declined, and "out-of-tier construct" is a refusal the reader wants
located. Only TIMEOUT loses its world.

### 4.6.3 What the completion type has to carry

A C statement does not simply finish. `execStmt` answers a `Flow`:

| constructor | from | sites |
| --- | --- | ---: |
| `normal` | falling off the end | — |
| `brk` | §6.8.7.3 `break` | 8 |
| `cont` | §6.8.7.2 `continue` | 6 |
| `ret` | §6.8.7.4 `return`, with an optional value | 103 |
| `goto` | §6.8.7.1 `goto` | 7 |

**`goto` is the one that is not free.** Measured: the 7 `goto`s reach
exactly **3 labels** (`after_moves` ×3, `out` ×3, `reset_ok` ×1), every
one of them a FORWARD jump to a label in the same function and at the
same or an enclosing block level. That is the shape a `Flow.goto`
propagating outward to a labelled statement can serve; a general
`goto` needs a CFG, and the census says this corpus does not.

### 4.6.4 The rows that price the rest

* **51 of 253 `if`s have an `else`** — the else-less arm is the common
  path and gets the first gate.
* **Three of the 50 `for`s omit a clause** — 48 carry `init`, 49 carry
  `cond`, 50 carry `inc`, so two omit `init` and one omits `cond`. The
  "omitted clause" cases are 3 sites, not a third of them.
  An omitted `cond` means *true* (§6.8.6.3p2), which is one line and one
  gate.
* **98 of 103 returns carry a value.**
* **273 of 321 `VarDecl`s have an initializer, and 34 are
  `InitListExpr`** — so **aggregate initialization is inch 4's work, not
  a corner to defer**. It is also the first construct that needs the
  layout table for *writing* rather than reading.
* `DeclStmt` carries up to **5** declarators (212 of 228 carry one), and
  C23 §6.7p5 sequences them left to right, each fully before the next.

## 5 `abort` and `exit` — rung 1's entire scorer

```
inductive Terminal
  | returned (status : Int)   -- fell off main, or `return n`
  | exited   (status : Int)   -- exit(n)
  | aborted                   -- abort(): a distinguished TERMINAL, not a refusal
```

`docs/c-tier-architecture.md` §6 already fixed `abort` as *"a
distinguished TERMINAL outcome, not a refusal."* The suite census turned
that into the cheapest scoreboard in the program.

**The exit-status oracle**, measured (`docs/c23-goal.md` §1.2): GCC's
torture and c23-run corpora score by exit status — `abort()` on failure,
fall off `main` on success. Their top calls are `abort` 162, `exit` 95,
`__builtin_abort` 72 of 246 parsed. So:

> **MATCH** = the run terminated with `.returned 0` (or `.exited 0`).
> **DIVERGE** = it terminated `.aborted`, or with a nonzero status.
> **REFUSE** = one of §3.1's three causes.

**No stdout modeling is required for rung 1 at all.** The flagship corpus
also happens to contain exactly one `abort()` site (L669-672, the
move-list overflow guard, already written as a loud terminal), so the
construct is exercised by rung 0's own fixture.

---

## 6 `printf`, scoped BY MEASUREMENT

The dispatch's instruction was to census the format strings that actually
appear, not to speculate. `harness/c_suite_census.py` now extracts every
format string from the printf family and tallies C23 §7.23.6.1's parts
separately.

**Measured — c-testsuite (202 specs) and Fujitsu (997 specs):**

| part | c-testsuite | Fujitsu | C23 has |
| --- | --- | --- | --- |
| conversions | `d`106 `s`43 `f`42 `c`6 `x`2 `X`1 `i`1 `u`1 | `x`580 `d`320 `f`97 | 16 |
| flags | `0` ×2 | none | 5 |
| length modifiers | `L`16 `l`6 `ll`1 | `ll`126 `l`110 `L`8 | 11 |
| width | literal digits ×2 | none | digits or `*` |
| precision | literal digits ×64 | none | digits or `*` |

**Eight of sixteen conversions, one of five flags, three of eleven length
modifiers, and `*` never appears** — neither for width nor precision, in
1199 specs across two corpora. Entirely absent: `o e E g G a A p n %`.

**The integer-only subset is rung 2, and it is worth a lot.** Counting
tests whose libc calls are all in the printf family and whose conversions
avoid `eEfFgGaA`:

| corpus | printf-family only | **integer-only** | in-vocab | needs a float conversion |
| --- | ---: | ---: | ---: | ---: |
| c-testsuite | 61 | **59** | 49 | 2 |
| Fujitsu (300 sampled) | 261 | **242** | 242 | 19 |

So `printf` restricted to `d i u x X c s`, with literal width/precision,
the `0` flag, and `l`/`ll` — **no `*`, no float conversions** — unlocks
242 of 300 sampled Fujitsu tests and 49 more c-testsuite tests. The float
conversions are 21% of c-testsuite's specs and 10% of Fujitsu's, and they
wait behind the float decision.

---

## 7 The inch ladder for M2, priced

Each inch is separately green, separately landable, and the triad stays
green at every one. Prices in sessions, anchored to the Python lane's
measured record and to M1's actuals (M1's seven inches were ~2 sessions).

| # | inch | what it lands | price |
| ---: | --- | --- | ---: |
| **1** | **the value model** | `LeanModels/C/C23/Value.lean`: `IntTy` from the profile, `CVal`, the wrap/refuse arithmetic of §1.2, with `#guard`s on the boundary cases (`INT_MAX+1` refuses, `UINT_MAX+1` wraps, `INT_MIN/-1` refuses, `(int)0x80000000u` = `INT_MIN`) — **LANDED** | 1 |
| **2** | **the memory model** | `C23/Memory.lean`: `Ptr`, `CByte`, `CObj`, `Mem`, `alloc`/`free`/`load`/`store` + WF lemmas, stated around DECAY and `->` per §2.2a. Pure functions, no monad, no interpreter — **LANDED**, 4 WF theorems, 50 gates | 2-3 |
| **3** | **the expression semantics** | `C23/Expr.lean`, §6.5: the conversion lattice's 8 `castKind`s, `evalLValue`'s five census-chosen cases, arithmetic, **the §4.3 short-circuit rules at §6.5.14/§6.5.15** — do-notation over the §4.1a stack, **FUEL-FREE** — **LANDED**, 3 drain theorems, 37 gates | 3-4 |
| 4 | statements + `CWorld` | `C23/Stmt.lean` at §6.8: the 11 statement kinds, `Run CWorld`, the `Run.exn` payload decision (§4.1), `abort`/`exit` terminals | 3-4 |
| 5 | calls and the frame | §6.5.3.3: function calls, parameters, the 19 indirect sites through `movecb`, and the **7-site `J.1(16)` discharge** (§4.5) | 2 |
| 6 | **rung-1 scorer** | `harness/c_refusal_census.py` per `docs/c23-goal.md` §4.2, run on the gcc-torture exit-status subset — **the first real score** | 2 |
| 6a | **clause coverage** | `harness/c_clause_coverage.py` (`docs/c23-spec-mirror.md` §7): scan the surface's citations, emit the conformance map against N3220's own table of contents. Cheap, and it is the scoreboard to read BESIDE the suite score | 1 |
| 7 | the libc slice, integer `printf` | §7.23.6.1's measured subset; scores c-testsuite's 49 + Fujitsu's 242 | 2 |

**~15-20 sessions to a first scoreboard**, with the first score arriving
at inch 6 rather than at the end. Inches 1-2 are the un-retrofittable
half and are worth doing slowly; 3-5 are mechanical against a fixed
vocabulary; 6-7 are harness work the Python lane has already solved once.

**Two scoreboards, not one.** Inch 6 says "agrees with what these
compiler projects test"; inch 6a says "and here is which of N3220 the
surface has actually spoken about". Neither substitutes for the other,
and publishing only the first would be the more flattering half.

**The target the ladder climbs toward** is `docs/c23-goal.md` §4.1's rung
1: the 196 reachable torture tests in the 300-test sample, scored on exit
status with no output modeling. Rung 2 (inch 7) adds 291 more.

---

## 8 What this design does NOT decide

* **The `Run.exn` error payload** — deferred to inch 4, the first inch
  that needs it (§4.1). Note §4.1a narrows the choice: the stack is
  `StateT CWorld (Except Refusal)`, so the question is what `Refusal`
  carries, not whether the outcome type is parametric.
* **Whether a C17 surface is a copy or a delta of the C23 one.** The
  version namespace exists (`LeanModels.C.C23`) and
  `LeanModels/C/C23.lean` records the measured differences; deciding what
  a second version costs belongs to the architecture lane, with its own
  C17→C23 delta census.
* **Where `Run` lives.** `docs/c-tier-charter.md` §2.4 priced the move to
  `LeanModels/Core/` at 149 lines / 24 files / 1251 sites and deferred
  it. Inch 4 is when a second consumer finally exists, so inch 4 is when
  the question becomes concrete — not before.
* **Floats.** Named Thomas-decision, unchanged (`docs/c23-goal.md` §5.3).
* **`switch`.** Rung 1 of the construct ladder, not of the semantics
  ladder; it is 5 of the 8 constructs in `docs/c23-goal.md` §4's greedy
  walk and belongs after a scoreboard exists to measure it.
* **Anything about clause 7.** The goal is scoped to the language
  (`docs/c23-goal.md` §4.3), and the libc slice is only what the corpora
  call.
