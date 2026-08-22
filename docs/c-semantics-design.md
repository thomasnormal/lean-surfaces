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
  > it. What C23 changed is signed REPRESENTATION (§6.2.6.2p6 NOTE 2);
  > the deleted J.3 sign-representation entry is the mandate's auditable
  > trace. So this is **depended-on implementation-defined behavior**,
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
inductive CByte | conc (b : UInt8) | ptr (p : Ptr) (k : Fin 8) | indet
```

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
evaluator is written in **do-notation over a fuel-indexed
`StateT CWorld (Except Refusal)`**, not as a hand-rolled
`evalExpr`-returning-`Result` in the Python lane's style.

Three consequences, all of which the inches below are shaped to:

1. **Primitive operations are named functions with Spec-lemma-shaped
   contracts** — memory read/write, conversion, the short-circuit step.
   The SHAPE is what makes the comparison possible whether or not
   `mvcgen` is invoked yet.
2. **The drain amendment survives intact.** A short-circuiting
   construct's out-world rides in the monad's state, and §4.3's
   hypothesis-side discipline becomes a WP precondition — the same rule,
   expressed where the tooling can use it.
3. **The stack's definition may live in this tier for now**; lifting it
   to shared substrate belongs to the architecture lane.

**Toolchain check, measured:** `Std.Do` is present in the pinned
toolchain (`v4.33.0-rc1` ships `Std/Do/{WP,Triple,SPred,PredTrans}.olean`),
so nothing here is blocked on a bump. The monadic structure stands
regardless of the `mvcgen` pilot's verdict — it is better structure even
if the verification conditions stay hand-generated.

**Inch 2 is unaffected**, and deliberately so: the memory model's
operations are PURE functions over `Mem`, which is what lets them be
lifted into whatever stack the family settles on without being rewritten.

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
| **1** | **the value model** | `LeanModels/C/C23/Value.lean`: `IntTy` from the profile, `CVal`, the wrap/refuse arithmetic of §1.2, with `#guard`s on the boundary cases (`INT_MAX+1` refuses, `UINT_MAX+1` wraps, `INT_MIN/-1` refuses, `(int)0x80000000u` = `INT_MIN`) | 1 |
| 2 | the memory model | `C23/Memory.lean`: `Ptr`, `CByte`, `CObj`, `Mem`, `alloc`/`free`/`load`/`store` + WF lemmas, stated around DECAY and `->` per §2.2a. Pure functions, no monad, no interpreter | 2-3 |
| 3 | the expression semantics | `C23/Expr.lean`, §6.5 subclause by subclause: literals, `declRef`, the conversion lattice's 8 `castKind`s, arithmetic, **the §4.3 short-circuit rules at §6.5.14/§6.5.15** — in do-notation over the §4.1a stack | 3-4 |
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
