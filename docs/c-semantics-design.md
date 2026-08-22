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
  an out-of-range unsigned→signed conversion that **C23 §6.3.1.3
  mandates** and C17 left implementation-defined.

So:

| operation | rule |
| --- | --- |
| unsigned `+ - *` out of range | **wraps**, modulo 2^bits — defined, never refused |
| signed `+ - *`, unary `-`, `++`/`--` out of range | **REFUSE** (`ub.signedOverflow`) |
| signed → unsigned conversion | modulo, defined since C89 |
| unsigned → signed out of range | **two's-complement wrap**, C23-mandated; the `-std=c23` pin is load-bearing here, not a formality |
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
**86 sites take `&` of an automatic object and 20 take `&` of a
subobject.** `struct kcctx c = { … }; gen_moves(p, kc_cb, &c);`
(L369-370) is not a corner — it is the corpus's callback protocol, the
mechanism behind all **19 indirect calls** and every one of its six
`*ctx` structs.

So every automatic variable is allocated as an object on block entry with
all bytes indeterminate, and killed on block exit. A pointer to a dead
automatic is a well-formed VALUE; dereferencing it refuses.

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
| **1** | **the value model** | `LeanModels/C/Value.lean`: `IntTy` from the profile, `CVal`, the wrap/refuse arithmetic of §1.2, with `#guard`s on the boundary cases (`INT_MAX+1` refuses, `UINT_MAX+1` wraps, `INT_MIN/-1` refuses, `(int)0x80000000u` = `INT_MIN`) | 1 |
| 2 | the memory model | `Memory.lean`: `Ptr`, `CByte`, `CObj`, `Mem`, `alloc`/`free`/`load`/`store` + WF lemmas. No interpreter | 2-3 |
| 3 | the expression semantics | `Semantics.lean` part 1: literals, `declRef`, the conversion lattice's 8 `castKind`s, arithmetic, **the §4.3 short-circuit rules** | 3-4 |
| 4 | statements + `CWorld` | the 11 statement kinds, `Run CWorld`, the `Run.exn` payload decision (§4.1), `abort`/`exit` terminals | 3-4 |
| 5 | calls and the frame | function calls, parameters, the 19 indirect sites through `movecb` | 2 |
| 6 | **rung-1 scorer** | `harness/c_refusal_census.py` per `docs/c23-goal.md` §4.2, run on the gcc-torture exit-status subset — **the first real score** | 2 |
| 7 | the libc slice, integer `printf` | §6's measured subset; scores c-testsuite's 49 + Fujitsu's 242 | 2 |

**~15-20 sessions to a first scoreboard**, with the first score arriving
at inch 6 rather than at the end. Inches 1-2 are the un-retrofittable
half and are worth doing slowly; 3-5 are mechanical against a fixed
vocabulary; 6-7 are harness work the Python lane has already solved once.

**The target the ladder climbs toward** is `docs/c23-goal.md` §4.1's rung
1: the 196 reachable torture tests in the 300-test sample, scored on exit
status with no output modeling. Rung 2 (inch 7) adds 291 more.

---

## 8 What this design does NOT decide

* **The `Run.exn` error payload** — deferred to inch 4, the first inch
  that needs it (§4.1).
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
