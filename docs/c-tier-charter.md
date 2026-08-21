# The C tier: FOUNDING CHARTER

**Status: the workstream's founding document.** The owner chartered
"building out C in lean" on 2026-08-21, which answers the gate
`docs/c-tier-architecture.md` was left under. This charter does four
things and no more: it RE-CENSUSES the flagship corpus with an instrument
that lands beside it, it takes the one architecture decision the
architecture memo never had to ask, it prices THREE endgames for the
owner to choose between, and it plans the first milestone — the prefix
all three share.

**It recommends no endgame.** §3 presents; §5 lists what the owner still
has to answer.

**What already existed, and what each of the three prior memos is.**
Nothing below re-derives them; every one is cited where it is used.

| memo | question | verdict |
| --- | --- | --- |
| `docs/c-extension-bridge-census.md` (commit `ae70a69`) | C-as-a-Python-bridge: model C **plus CPython's C API** so `_struct.c` executes under the Python tier | priced (41 API names for bridge v0), owner-gated, no recommendation |
| `docs/c-intrinsics-proposal.md` | the cheaper alternative: name-only bindings, no C executed | priced, owner-gated |
| `docs/c-tier-architecture.md` | C-as-a-first-class-language: its own corpus, oracle, differential claim | five decisions taken, three questions left open, GATED |

This charter continues the third. The first two stay gated and nothing
here unblocks either — but §1.5 measures the delta to `ae70a69`
precisely, because "someone already priced this" is only true if the two
censuses overlap, and they do not.

---

## 1 THE CONSTRUCT CENSUS

### 1.1 The instrument, and why it lands

`harness/c_construct_census.py`, landed with this charter, run as

```
python3 harness/c_construct_census.py <sunfish.c> -o docs/c-construct-census.json
python3 harness/c_construct_census.py <sunfish.c> --compare docs/c-construct-census.json
```

It walks `clang -std=c23 -D_FORTIFY_SOURCE=0 -Xclang -ast-dump=json`,
carrying clang's STICKY `loc.file` forward so only nodes attributed to
the censused source are counted — without that filter the census measures
libc's headers, not the corpus. Output is sorted and a double run is
byte-identical (verified).

**All three refusal paths were RUN, not admired, and the third was a
defect found that way.** A missing file refuses; a source that attributes
ZERO nodes refuses (an empty census is an instrument fault, never a
finding); and a source clang REJECTS refuses — that last one originally
did not. clang emits a partial AST alongside its diagnostic, so the first
version of this instrument censused a program that does not compile and
exited 0, reporting a plausible table of near-zeros. That is a silent
wrong answer of exactly the kind this repository does not ship, it was
invisible until the broken-input fixture was actually executed, and it is
the reason the fixture was executed.

The architecture memo's census was taken by "a scratch script" that did
not survive. That is the whole reason this one lands, and the reason it
has a `--compare` mode: **the corpus lives in another repository and
moves on its own schedule, so staleness has to be mechanically
detectable rather than merely possible.** It was in fact stale, by
exactly one engine release (§1.4).

**It is deliberately NOT wired into `tools/ci.sh`**, and the reason is
the same one that keeps its predecessor `harness/c_api_census.py`
un-wired: the corpus is not in this repository and is not on a stock
runner, so a gate would be a permanent SKIP pretending to be a check.
`--compare` against the committed JSON is the re-run, and it is a
deliberate act. When the C lane owns a corpus in-tree, the `maybe
<name> <required-file> <cmd>` helper is where this belongs.

The profile is recorded in every output because it is an INPUT to the
AST, not a stamp on the side of it — the architecture memo §4.3 measured
that `_FORTIFY_SOURCE` rewrites four libc calls and injects
`__builtin_object_size` nodes present in nobody's source. The instrument
stamps the compiler FAMILY (`apple-clang-17`), never the point release,
which is the correction `docs/backlog.md` records twice.

### 1.2 The corpus, and the four pins that have to agree

The flagship is `tools/ctwin/sunfish.c` in the SUNFISH repository — a
node-identical C twin of classic `sunfish.py`, whose own README states
the fidelity contract as *"same position in, same chosen move, same node
count, same score out — verified differentially, not assumed."* It is a
TRANSCRIPTION, which is what makes it a semantics corpus rather than a
second engine.

Three facts the architecture memo could not state, all checked today:

1. **`tools/ctwin/` is now on sunfish MASTER.** The memo recorded it as
   "not on sunfish master; carried on the sunfish-packed / -eval / -tm /
   -eventual-trichotomy checkouts". It is on master now, which removes
   the branch-dependence from every claim below.

2. **All four of the square's source pins agree at ONE engine commit,
   today.** Measured:
   * `Examples/python/sunfish/sunfish.py` (this repo's corpus) —
     sha256 `f6c481a6a2c9f4c3686c13115adb36719693676d47b0121af03347d3a01219a1`
   * sunfish master's `sunfish.py` — the SAME sha256, byte for byte
   * `git rev-list --count e670434..master -- sunfish.py` = **0**
   * `git rev-list --count e670434..master -- tools/ctwin/sunfish.c` = **0**

   So both twins have been stable since engine commit `e670434`
   (2026-08-18) and this repo's corpus is that exact file. The memo's
   standing worry — *"the two pins are maintained in different
   repositories, so the square's Python-side identity is only as current
   as the OLDER of them"* — is SATISFIED as of today. It is satisfied by
   observation, not by construction, so the check stays a standing one;
   `--compare` is now the cheap way to run it.

3. **The square's A ≡ C edge is SETTLED under the pinned oracle, and
   this repository's record says otherwise.** `tools/ctwin/README.md`
   records a 2026-08-16 interpreter cross-check: the full 7-line gate,
   run twice on one commit, swapping only the reference interpreter,
   byte-identical coverage and 0 mismatches under CPython 3.9.19. That
   is the memo's M0, done — one day after `docs/backlog.md` recorded it
   as still owed, and never carried back. §4.2 states what is actually
   left, which is smaller and different.

The censused file: sha256
`7d5e0ff8782f804844f383d6f72314dbf948f8e3a26f4033794d6357140b77d7`.

### 1.3 What is there — measured

Machine-readable rows in `docs/c-construct-census.json`. Line references
are into the censused file.

| dimension | measured | witness |
| --- | --- | --- |
| lines | 1458 total, 1378 non-blank; preprocessed TU 3335 | — |
| functions with bodies | **58** — 57 `static` plus `main` | `main` L1305 |
| file-scope objects | **71** (46 with initializers, 25 zero-initialized) | the knob block L75-155 |
| structs / typedefs / enums | 13 `RecordDecl` / 7 typedefs / 3 anonymous enums, 62 fields | `Pos` L179, `Move` L178, `Map` L393 |
| **distinct AST node kinds** | **45** — the entire v0 vocabulary | listed in the JSON |
| binary operators | 20 distinct, 1007 sites | `=` 287, `&&` 111, `+` 96, `-` 90 |
| compound assignment | 5 distinct (`*=`, `+=`, `-=`, `^=`, `\|=`), 24 sites | `x *= …` L192 |
| unary operators | 6 distinct (`& ! ++ - * --`), 311 sites | — |
| **overflow-capable arithmetic** | **327** sites (`+ - *`, unary `-`, `++`/`--`, compound forms) | — |
| implicit conversions | 3123 `ImplicitCastExpr`, **8 distinct `castKind`s** | `LValueToRValue` 1837, `ArrayToPointerDecay` 405 |
| explicit casts | 95 `CStyleCastExpr` = 57 `NullToPointer` + 38 `IntegralCast` | — |
| calls | 320 sites; 78 distinct callees; **27 external names** over **146** sites | — |
| indirect calls | **19**, all through the `movecb` parameter `cb` | `typedef` L301; `cb(_m, ctx)` L304 |
| control flow | 253 `if`, 50 `for`, 29 `do`, 5 `while`, 7 `goto`, 3 labels, 8 `break`, 6 `continue`, 42 `?:` | `goto after_moves` L809 |
| **`switch`** | **0** | the sole `switch` in the file is the word, in a comment at L283 |
| array subscripts / member exprs | 328 / 410 | — |
| **`&` on an automatic object** | **86** | `&c` L370, `&fc` L1071 |
| **`&` on a subobject** | **20** | `&tpm.cold[idx].nmv` L621 |
| member read off a call RESULT | **0** | temporary lifetime never exercised |
| function-like / object-like macros | 6 / 3 | `YIELD` L302, `PROCESS` L775 |
| `sizeof` | 12 | — |
| dynamic allocation | `malloc` 2, `calloc` 1, `realloc` 2, `free` 5 | `map_put` L453-454 |
| `setjmp` / `longjmp` | 2 / 2 | `setjmp` L968, L1021; `longjmp` L746, L747 |
| floats | 15 float literals, 13 `IntegralToFloating`, `double` at 9 source lines | all on the deadline path |
| shifts | 17 (`<<` 11, `>>` 6) | `mix64` L192-194 |
| division / modulo | 19 (`/` 11, `%` 8) | `pyfloordiv` L160, `pymod` L165 |
| string literals | 126 | — |
| compound literals | 1 | `VM_MOVE` L653 |

Absent, verified by grep on the source AND by the AST: `union`,
`_Atomic`, `volatile`, `restrict` (in the corpus's own text — it reaches
the model only through libc prototypes), `_Generic`, `#if`, `#pragma`,
`__int128`, `alloca`, `thread_local`, VLA. Zero `T*`→`U*` punning casts:
all 95 explicit casts are `NULL` or arithmetic, and all 52 implicit
`BitCast`s are `void*`↔`T*` around the allocator and `memcpy`.

The libc surface, exactly 27 names: `abort atoi atol calloc clock_gettime
fclose fflush fgets fopen fprintf free getenv longjmp malloc memchr
memcmp memcpy printf puts realloc setjmp snprintf sprintf strchr strcmp
strcpy strtok`.

The scalar type vocabulary the arithmetic tier must carry, by node count:
`int` 4733, `long` 340, `char` 254, `unsigned char` 173, `uint64_t` 153,
`double` 117, `unsigned long` 33, `unsigned long long` 15, `unsigned int`
6, `uint32_t` 5, `uint8_t` 1.

### 1.4 THE DELTA to the architecture memo — measured at both ends

The memo (2026-08-15) censused sha256 `66c569c1…` at 1310 lines. The
instrument locates that exact file at sunfish commit `4d4974f`
(2026-08-14) and censuses it, so the delta is MEASURED and not
transcribed from prose:

```
node kinds  45 -> 45   added: none   dropped: none
libc names  27 -> 27   added: none   dropped: none
  lines_total                          1310 ->   1458  (+148)
  functions_with_bodies                  54 ->     58  (+4)
  file_scope_objects                     50 ->     71  (+21)
  binary_op_sites                       898 ->   1007  (+109)
  unary_op_sites                        262 ->    311  (+49)
  implicit_cast_sites                  2732 ->   3123  (+391)
  call_sites                            290 ->    320  (+30)
  external_call_sites                   124 ->    146  (+22)
  array_subscripts                      295 ->    328  (+33)
  addr_of_automatic                      67 ->     86  (+19)
  overflow_capable_sites                292 ->    327  (+35)
  float_literals                         10 ->     15  (+5)
  string_literals                        96 ->    126  (+30)
  sizeof_sites                            9 ->     12  (+3)
```

**The instrument re-derives every headline the memo published**, on the
memo's own file: 1310 lines, 1236 non-blank, 3200 preprocessed, 54
functions (53 `static`), 50 file-scope objects (28 initialized), 45 node
kinds, 8 `castKind`s, 898 binary sites, 262 unary sites, 2732 implicit
conversions, 290 call sites, 27 libc names over 124 sites, 19 indirect
calls, 295 subscripts, 17 shifts, 9 `sizeof`, 10 float literals, 78
explicit casts, 96 string literals, `switch` 0. One number needs its
rule stated: the memo's *"75 distinct callees"* is this instrument's
**74 named callees plus the one indirect callee class** (`cb`), which
the instrument reports separately as `indirect_calls`. That agreement is
the instrument's validation, and it is why the deltas above can be read
as facts about the CORPUS rather than about two different scripts.

**THE HEADLINE, and it is the census's most decision-relevant result:
the corpus grew 11.3% and the tier's SURFACE did not move at all.** Not
one new AST node kind, not one new libc name, not one new operator, not
one new `castKind`, and every absent feature still absent. Every single
delta is a COUNT. The memo had one data point and could only assert its
45-kind vocabulary was the v0 vocabulary; two data points across a real
engine release make it a measured claim about the corpus's development,
not a snapshot. **A v0 scoped to those 45 kinds and 27 names is not a bet
on a frozen file.**

Three deltas that are not merely counts, and what each means:

1. **Floats grew (+5 literals, +7 `IntegralToFloating`) and grew AWAY
   from v0's path.** Every new site is in `go`'s time-control arm
   (L1418-1439: `wtime`/`btime`/`winc`/`binc`/`movestogo` → `mt`), which
   feeds `go_game`. The fixed-depth entry point `go_depth` (L965) still
   sets `deadline = 0.0` at L967 before `setjmp` at L968, and the only
   float operation the fixed-depth path evaluates is `deadline != 0.0`
   at L747 — an exact comparison of an exactly-representable value, no
   rounding anywhere. The memo's finding 5 HOLDS, and the growth
   direction strengthens it: the corpus is putting its float work where
   v0 does not go.

2. **File-scope objects grew 50 → 71 (+21), 25 of them
   zero-initialized.** This is the knob block (`QS_TAIL`, `FUEL_NULL`,
   `FUEL_MIN_DEPTH`, `DERIVE_FRESH`, `FEN_HIST`, the eviction battery).
   Static duration with mutable module state is the corpus's NORM, and
   it is growing. Any C tier for this corpus models static duration from
   line one.

3. **The sequencing census is CHEAPER than the memo priced it, and its
   method is now recorded.** The memo's "828 full expressions in
   statement position, of which 64 carry ≥2 effects" reproduces to the
   digit under the rule *"expression whose parent is a statement,
   excluding declarator initializers"* — 828 and 64 exactly, on the
   memo's file. The memo's further split (*"32 are `x = f(…)`"*) does
   not: the correct rule is that an assignment's store is sequenced
   after the WHOLE right operand, whatever its shape, so
   `arr[i] = f(g(y))` is a one-effect-POSITION site too. Under that
   rule the memo's own 64 split 45/19, not 32/32. On today's corpus,
   under the C23 §6.8 definition the instrument uses (which correctly
   INCLUDES declarator initializers): **1169 full expressions, 73
   candidates, 53 admitted by inspection, 20 left for the may-alias
   check** — against the memo's estimate of 32. The may-alias analysis
   has to handle at most four-effect full expressions at 20 sites.

### 1.5 THE DELTA to `ae70a69` — the two censuses are DISJOINT

`ae70a69` is the workstream's starting capital and it is worth being
exact about what it bought, because "someone already priced this" would
be wrong.

`ae70a69` priced the CPython C API surface of twelve extension modules:
bridge v0 (`_bisect` + `_heapq` + the `_contextvars` shim) = 41 distinct
API names over 912 LoC; 219 semantic names at eight modules; C-exclusive
file flips ZERO. Its unit of account is the `Py*`/`_Py*` name.

**`tools/ctwin/sunfish.c` uses ZERO CPython API names.** The two censuses
do not share a single row. Joined against each other:

| axis | `ae70a69` bridge v0 | this census |
| --- | --- | --- |
| unit | CPython API name | C language construct |
| CPython API names | 41 (25 semantic, 16 boilerplate) | **0** |
| libc names | **0** | **27**, over 146 sites |
| file-scope mutable state | none (const tables only) | **71 objects**, 25 zero-initialized |
| floats | none | 15 literals, confined to the clock arm |
| `goto` density | 0 (`_bisect`/`_heapq`) | 7 + 3 labels — between the bridgeable core (0-5) and the engines (46-89) |
| dynamic allocation | the bridge's heap tier, by pattern | 10 sites, `realloc` MOVES the hot table |
| the C LANGUAGE tier | **explicitly not priced** | this document |

`ae70a69`'s §5 says so itself: *"LoC is not effort, and none of this
prices the C definitional interpreter itself — declarations, pointers,
structs, arrays, function pointers, `switch`/`goto` …, the libc slice …
The per-module numbers say only what each module ADDS on top of that
tier."* This census prices exactly the tier `ae70a69` excluded, on a
corpus with none of `ae70a69`'s subject matter.

**What DOES transfer from `ae70a69`, stated so the capital is not
written off:** one sentence and the whole method. The sentence is its
§5 covenant line — *"UB in the C tier = loud refusal … a C tier that
must DETECT UB is strictly harder than a compiler that may assume its
absence"* — which is the architecture memo's premise and this charter's.
The method is the house method and it transfers entire: census before
pricing; bucket the surface by what amortizes and what is a behaviour;
join the count against a ceiling that decides whether the work FLIPS
anything; publish an instrument and a machine-readable table; and make
no recommendation on a covenant question. This charter is that method
applied to the language instead of to the bridge.

### 1.6 What the census settles, and what it does not

**Settles.** The v0 vocabulary (45 kinds, 27 libc names) is stable under
real engine churn. `switch` is genuinely absent, so R1 is genuinely a
rung and not a v0 hole. The effective-type wall still fires on nothing
(0 punning casts, 0 unions), which is exactly when it is cheap to
install correctly. `malloc`/`realloc` are v0, not a rung. Temporary
lifetime is still 0 sites. The `setjmp` restriction still admits the
corpus end to end. The sequencing residue is 20 sites, not 32.

**Does not settle.** Whether the 45 kinds are the SAME 45 as the memo's
— the memo did not record the list, so only the count is comparable. The
list is recorded now, so the next re-census can diff the SET; that is a
methodology repair, not a finding. Nothing here re-measures the memo's
sanitizer probes (§5.2) or its implementation-defined profile (§3.3);
both are unchanged claims about the same host and both are still owed a
verification on the build box, ASan especially.

---

## 2 THE ARCHITECTURE DECISION

The architecture memo took five decisions — memory model, semantic
latitude, front end, oracle/harness, effect walls — and this charter
re-confirms all five against the re-census (§1.6). It never had to ask
the sixth, because it assumed a standalone `LeanModels/C/`. The charter
asks it, because the workstream is "C in lean" and the Python tier is
sitting right there:

> **Does the C tier get its own semantic model, or does it share the
> Python tier's world infrastructure?**

### 2.1 THE DECISION

**Own semantic model. Shared world DISCIPLINE. Shared code only where
the Python tier is ALREADY parametric — which, measured, is the outcome
type and the span, and nothing else.**

`LeanModels/C/` is a SIBLING of `LeanModels/Python/`, never a client of
it. The C tier defines its own values, its own memory, its own
arithmetic and its own refusal classes. It inherits the outcome type,
the effects-as-traces treatment, and the entire gate/oracle/batch
apparatus.

The census decides this three times, and each time the answer is the
same for a different reason.

### 2.2 What CANNOT be shared — three, each measured

**(a) The value model, because C's integers have widths and a UB
boundary and Python's do not.** `RVal.int (n : Int)` is UNBOUNDED
(`LeanModels/Python/Runtime.lean:31`). C's arithmetic is fixed-width in
**10 integer types** (plus `double`) across **327 overflow-capable
sites**, and the
boundary is not a wrap — signed overflow must REFUSE. Adding a width to
`RVal.int` would change every arithmetic lemma in the Python tier for
the benefit of a language that is not Python.

The corpus makes the split unavoidable in a single expression.
`mix64` (L191-195) is

```
x ^= x >> 33; x *= 0xff51afd7ed558ccdULL;
```

— deliberate UNSIGNED wraparound, which C DEFINES, at both `*=` sites in
the file; while
`PACK_VM` (L649) biases a signed `int` into unsigned order by
`(uint32_t)(val) ^ 0x80000000u` so that `uint64_t` comparison IS Python's
tuple order. So the tier needs "unsigned wraps, defined" and "signed
overflows, refuse" **simultaneously and in adjacent operands**. One
`Int` constructor cannot express the distinction, and a model that
blurred it would be wrong about the corpus's hottest sort key.

**(b) The memory model, because in C a local has an ADDRESS.** Python's
locals are `REnv := List (String × RVal)` — a binding with no address at
all; its heap is `Heap := Array Obj` where `Addr := Nat` and the address
IS the array index. Measured against that:

* **86 sites take `&` of an automatic object**, and **20 take `&` of a
  subobject**. An environment binding has nothing to take the address
  of. `struct kcctx c = { … }; gen_moves(p, kc_cb, &c);` (L369-370) is
  not an exotic corner — it is the corpus's CALLBACK PROTOCOL, the
  mechanism behind all **19 indirect calls** and every one of the six
  `*ctx` structs (L360, L655, L683, L706, L1005, L1296). The very first structural choice differs, and the
  census is what says so.
* **`realloc` MOVES the transposition table** (L453-454, on the search
  path). Every pointer derived from the old object must die. `Addr :=
  Nat` cannot carry the provenance that says so; `Ptr = (Option ObjId,
  Int offset)` can. This is the architecture memo's §2 decision and the
  re-census leaves it untouched.
* **Objects are partly indeterminate.** `setup_fen` declares `Pos p;`
  and `memcpy(p.b, board, 120)` (L1130), leaving `p.score`, `p.h`,
  `p.ep`, `p.kp` indeterminate until `pos_seal`. Python has no
  indeterminate value and no notion of a byte.

**(c) The refusal surface, because Python has no undefined behavior.**
`.unsupported` in the Python tier means "this construct is not modeled
yet" — a property of the program TEXT, retired by building the tier out.
In C it means that AND "this run has no meaning" — a property of the RUN,
never retired. Eleven UB classes are armed at v0, and two of them
(strict aliasing, indeterminate reads) are detectable by NO sanitizer on
the pinned host, which is why they must live in the model. There is no
Python analogue to inherit from, and pretending the two `.unsupported`s
are the same thing would let a C-tier UB refusal be read as a tier gap.

### 2.3 What DOES reuse, and why it can

**The outcome type, verbatim, because it is already parametric.**

```lean
-- LeanModels/Python/Runtime.lean (excerpt)
inductive Run (σ : Type) (α : Type) where
  | ok          (state : σ) (value : α)
  | exn         (state : σ) (error : PyErr)
  | timeout
  | unsupported (message : String)
```

Those four constructors are the COVENANT, not Python: state retained on
`.ok`; `.timeout` is fuel exhaustion and nothing else; `.unsupported` is
loud and fuel-independent. C needs exactly these four and no fifth. The
census confirms the fit rather than assuming it: the eleven armed UB
classes are `.unsupported`; fuel exhaustion is `.timeout`; and the
corpus's **one `abort()` site** — L669-672, the move-list overflow
guard, already written in C as a loud terminal rather than a silent
truncation — is the `.exn`-shaped terminal outcome. The corpus was
written under this project's own "never hide errors" discipline before
the tier existed, which is a small piece of luck worth naming.

`σ` is a type PARAMETER. `Run CWorld CVal` typechecks against the
existing definition today. `bind`, `liftRes`, and the
`withLocals`/`toWorld` projections are all σ-parametric, as are the
`fuelMono` monotonicity shape and the ∃-fuel threshold form the whole
proof surface is stated in. `LeanModels/Core/Basic.lean`'s `Span` is
already used by 29 files spanning the Python, Circuit and Verilog-A
lanes — the existence proof that this repo's `Core` is a real sharing
point and not a decoration.

**The `PyErr` payload is the one wart, and it is named rather than
papered over.** `Run.exn` carries a `PyErr`. C's terminal outcome is not
a Python exception. Either `Run` gains an error-type parameter (`Run σ ε
α`) or the C tier's terminal outcome is carried in `α`. That is a real
decision; it is small; it does not have to be taken before the first
milestone (§2.4), and taking it early without a C-side consumer would be
designing against nothing.

### 2.4 The shared-core refactor — priced, and DEFERRED past M1

The clean end state is `Run` and friends in `LeanModels/Core/`, with
`LeanModels/Python/Runtime.lean` re-exporting so no Python call site
changes. Priced:

* the movable block is `LeanModels/Python/Runtime.lean:329-477` — **149
  lines**;
* it is referenced by **24 files**, **1251 `Run.` occurrences**, **143
  `: Run` signatures**, the heaviest being `Obs.lean` (40), `Runtime`
  (22), `ClockErase` (21), `PayloadBlind` (16), `Semantics` (14);
* a namespace move plus an `export` keeps all 1251 compiling, so the
  edit is mechanical — but it is a Python-lane-wide edit that touches
  every file sibling lanes are currently mid-campaign in.

**Decision: do not do it now, and it does not gate anything.** Measured:
`LeanModels/Python/Ast.lean` and `Json.lean` — the ingester tier, which
is the first milestone's entire Lean content — do not use `Run` at all.
So the first Lean the C tier writes has no opinion on where `Run` lives.
The refactor is un-urgent precisely because `Run` is already parametric;
it gets CHEAPER once a second consumer exists to justify it, and doing it
first would be a large blast radius spent on a hypothesis. It becomes a
gate at the milestone that writes the C interpreter, not before.

This is also the only place the charter deliberately leaves duplication
on the table, so it is stated plainly: **if the C interpreter ever lands
with its own copy of `Run`, that is a defect, not a design.** The
sequencing above exists to make sure it never has to.

### 2.5 Shared as DISCIPLINE, not as code

None of the following is Lean the C tier imports; all of it is
machinery the C tier reuses unchanged, and each already has a precedent
this charter is not inventing:

* **The `#guard` / non-vacuity gate**, `#print axioms` on every recorded
  theorem, zero `sorry`, zero `native_decide`. Ported verbatim.
* **The gate-composition discipline** — a gate per hard RULE, not per
  feature; a negative suite is as much of a battery as a positive one.
* **The census/`#guard` methodology**, of which §1's instrument is an
  instance: the headline is suspect until an instrument re-derives it.
  §1.4 is that law paying for itself twice — it validated the
  instrument against the memo AND corrected the memo's sequencing split.
* **Envelope discipline**: schema version, `source_sha256`, frontend
  FAMILY, `Unsupported` leaves for anything outside a pinned vocabulary,
  deterministic double-run output, and the cache key
  `(source, extractor, PROFILE)`.
* **The batch protocol**: `jobs.jsonl`, ONE runner process for the whole
  batch, exactly one output line per job in job order, a
  `{"status":"runner-error"}` row rather than a missing row.
* **The exit-code convention** 0/1/3/4/5 and the invariant behind it:
  **3 and 4 are never agreement**. Plus the standing prohibition on
  `"expect": "unsupported"` whitelist rows to silence a mismatch.
* **Effects as world data and inputs as traces**: stdout is `World`
  data; the clock, stdin, `getenv` and `argv` are INPUT TRACES with a
  loud underrun. The C corpus needs all four and the shapes are
  identical.
* **The `maybe <name> <required-file> <cmd>` CI helper**: present ⇒ run,
  absent ⇒ SKIP, reported, never silently omitted.

### 2.6 The decision in one line

> The C tier shares the project's COVENANT and its INSTRUMENTS. It does
> not share its VALUES or its MEMORY, because C locals have addresses,
> C integers have widths, and C runs can be meaningless — and the census
> measured all three.

---

## 3 THE ENDGAME OPTIONS — priced, not chosen

Three endgames. They share a prefix (§3.4), which is why §4 can plan the
first milestone before the owner picks. Prices are in the program's
units: an INCH is one landable, separately-green step; a SESSION is a
working block that lands one to three inches. Session counts are
anchored to the Python lane's measured record (`docs/backlog.md` §L1-L34
is ~34 landed sessions to get one theorem's two arms most of the way
closed) and to the architecture memo's line estimates
(`~7,000-11,000 Lean + ~2,000-3,000 Python` for v0).

### 3.1 Option (a) — VERIFIED C-SUBSET SEMANTICS, ctwin ingested and running

The architecture memo's v0, mirroring the Python arc's milestones. The
product is a definitional C interpreter that RUNS the corpus and agrees
with a pinned clang, with UB loudly refused.

**Milestones.** M0 the oracle pin (zero Lean) → M1 extractor + envelope
schema + profile (zero Lean) → M2 `Ast` + ingester + `#guard` round-trip
(no semantics) → M3 the memory model + WF lemmas (no interpreter) → M4
the interpreter + libc slice + batch arms → M5 the battery, then the
scalar leaves, `gen_moves` order, and `bound()` node-identity against
the compiled oracle.

**Price.** ~7,000-11,000 Lean + ~2,000-3,000 Python, per the memo's
five-pole estimate, which brackets between the SV lane (8,166 Lean) and
the Python lane (23,306) and is correct because **v0 builds NO proof
layer** — that is 11,550 of the Python lane's lines it does not write.
In sessions: M0-M2 ~6-10, M3 ~8-14, M4 ~15-25, M5 ~6-10 — **roughly
35-60 sessions to a running, differentially-tested C interpreter.**

**What it buys.** Undefinedness detection on a real program, and the
`.unsupported` covenant extended to a second language. **What it does
not buy: a single theorem.** Option (a) is an interpreter and a battery.

**First three inches.** (1) the census instrument + charter — LANDED with
this document; (2) M0's residue — the oracle-pin RESULT is already in
(§4.2), so what is left is landing the env-gated interpreter flag that
makes it re-runnable; (3) the profile document
`docs/c-profile-<id>.md` + `c-profile.json`,
pinning `char` signedness, `__STDC_IEC_60559_BFP__`, `_FORTIFY_SOURCE=0`
and LP64 — the input the extractor cannot be written without.

### 3.2 Option (b) — THE TWIN-BRIDGE THEOREM: ctwin ≡ sunfish.py per node

The prize: `make gate` — the rule-14 fidelity gate the sunfish repo runs
continuously — stops being a test and becomes a theorem. This is the
memo's §5.4 capstone (B ≡ D), promoted to an endgame.

**It is the most valuable of the three and the charter has to be blunt
about four things it requires that are not currently true.**

**(i) The gate's observable is STRICTLY STRONGER than anything either
tier currently proves.** `difftest.py` compares, per its own docstring:
phase 1, `gen_moves()` order and `value()` of every move at the position
and one ply below; phase 2, every MTD-bi probe on **`(depth, gamma,
score, killer move, node count)` — node-identity, not just bestmove.**
The Python tier's target is `RefinesAt`
(`Examples/python/sunfish/basecase_depth0.lean:385`), whose conclusion is
`Report gamma r (V pos d)` where

```lean
-- Examples/python/sunfish/bound_depth.lean (excerpt)
def Report (gamma report value : Int) : Prop :=
  (report < gamma ∧ value ≤ report) ∨ (gamma ≤ report ∧ report ≤ value)
```

That is a fail-soft BRACKET. Two runs can both satisfy it at the same
`gamma` and return DIFFERENT `r`. And the node count appears in
`BoundWF` only as a HYPOTHESIS (`clock : ¬((n+1).fmod 2048 = 0)`), never
in the conclusion. **So B ≡ D through the current target would not imply
the gate**, and stating otherwise would be the exact overclaim the
covenant exists to prevent.

**(ii) But the right SHAPE already exists, and it is not a two-model
comparison.** B ≡ D should never be proved by relating two interpreters
directly; it factors through a shared vertex:

> `(Lean-C bound refines S) ∧ (Lean-Python bound refines S) ⟹ B ≡ D`

and the Python arc is ALREADY building `S` — the abstract value function
`V : RVal → Int → Int` and the `Report` contract. The C side's
obligation is therefore *"aim at the same `S`"*, not *"invent one"*. That
is a real structural saving and it changes what the C tier should build:
its proof layer should be stated against the Python arc's `V`, not
against a C-flavoured re-statement.

Two wrinkles, both named: `V` is typed `RVal → Int → Int`, so it must
generalize over the position representation before a C-side statement can
mention it; and a third Lean body already states the same contract —
`formal/` in the sunfish repository (`formal/Sunfish/Bound.lean`,
`GameTree.lean`), core-only, no `sorry`. This repo deliberately RESTATES
`Report` rather than importing it (*"this lane depends on no package"*),
so `Report` reconciles by rename. The rest of `formal/` does not, and
whether `S` should BE `formal/`'s model is an open question, not a
detail.

**(iii) To imply the gate, `S` must be strengthened from a bracket to an
observable tuple** — `(score, node count, chosen move)` — for both tiers.
That is a change to the Python arc's own frozen statement, which
`docs/backlog.md` records as an expensive kind of edit (§L15's re-pin had
a blast radius four files wider than priced).

**(iv) Where the Python side actually is.** `BoundRefines` was REFUTED
(§L26) and repaired to `BoundRefinesW`. The `RecursionStep` campaign is
at §L34 — R3b's arithmetic half landed, its call half censused and left
whole — with the fail-low arm re-priced as a SECOND induction (§L27,
§L30). This is a campaign proving refinement inch by inch, not a tier
about to close.

**Price.** Option (a) in full, PLUS a C-side proof layer of the shape the
Python lane measured at 11,550 Lean lines, PLUS the Python arc's
remaining campaign, PLUS the (iii) strengthening on both sides. Honestly:
**150+ sessions, and it is gated on a Python-side campaign this
workstream does not own.** It is a program, not a milestone.

**First three inches.** (1) the census instrument + charter — LANDED;
(2) write down the gate's observable as a Lean-level STATEMENT — the
tuple, the two refinement obligations, the shared `S` — with no proof,
so the target is legible and the (iii) strengthening can be priced by
someone; (3) generalize `V`'s position type in the Python arc, the
smallest edit that makes a C-side statement expressible — and the cheapest
possible test of whether the shared vertex is real.

### 3.3 Option (c) — A GENERAL C COMPLETENESS LADDER

C-as-a-language, with ctwin as a first corpus rather than the point. The
product is the memo's rung ladder (R1 `switch` → R2 layout/unions/
bit-fields → R3 `longjmp` → R4 floats → R5 VLA → R6 concurrency → R7 the
rest of C23) with a sweep metric over real C, mirroring the Python
lane's stdlib sweep.

**Price.** Option (a), then each rung. R1 is small (`switch` is 0 sites
in ctwin, so it needs a new corpus first — measured). R2 and R3 are
mid-size and the memory model was designed for them (the memo's §6.1
notes `longjmp`'s indeterminate-value rule IS the `indet` byte). R4 is
GATED on a toolchain that DEFINES `__STDC_IEC_60559_BFP__`, which the
candidate oracle does NOT — that is a hardware/toolchain decision before
it is a Lean one. **R6 is the one rung that is not a widening**: it
replaces a state function with a memory-ORDER relation, which would
change the interpreter's TYPE and break `fuelMono`, `#py_check`
kernel-reducibility and the one-line-per-job batch protocol at once.
**~35-60 sessions for (a), then ~10-20 per rung for R1-R3, R4 gated,
R5 small, R6 a different project.**

**What it buys.** The broadest surface, and the one endgame whose value
does not depend on sunfish at all. **What it does not buy:** the square.
A general ladder has no second language modelling the same program, so it
cannot catch the class §5.4 of the memo exists for — a misreading shared
by a model and its oracle.

**First three inches.** (1) the census instrument + charter — LANDED, and
note the instrument is already corpus-general: it takes any `.c` path;
(2) census a SECOND, non-sunfish C corpus with the same instrument and
publish the union curve of node kinds — the number that says whether 45
is a corpus fact or a C fact, and the only cheap evidence for (c) over
(a); (3) the profile document, shared with (a).

### 3.4 What all three share

Every one of the three begins with the same four things, in the same
order: **the census (landed), the oracle pin (M0 — its result is already
in, §4.2, leaving only the flag), the pinned profile, and the extractor
+ envelope + ingester.** None of that work is wasted under any choice,
and none of it takes a position between them. That is what §4 plans —
and two of the four are done or nearly so, which is the cheapest the
start will ever be.

The choice becomes load-bearing at the FIFTH step, and it is a clean
fork: (a) spends it on the memory model; (b) spends it on a Lean-level
statement of the gate; (c) spends it on a second corpus.

---

## 4 THE FIRST MILESTONE — planned in full

**M1: the corpus is INGESTED. One function of `sunfish.c` round-trips
source → envelope → Lean AST literal → `#guard`.** No semantics, no
memory model, no interpreter. The shared prefix of (a), (b) and (c).

The inches, in dependency order. Each is separately green and separately
landable; the triad (`lake build && tools/docs_check.py &&
harness/diff_test.py && harness/script_corpus.py`) stays green at every
one, and none of them touches `lakefile.toml`, `LeanModels.lean` or
`lean-toolchain`.

### 4.1 Inch 1 — the census instrument and this charter. **LANDED.**

`harness/c_construct_census.py` + `docs/c-construct-census.json` +
`docs/c-tier-charter.md` + `docs/backlog.md` §L35. Zero Lean, zero risk
to the Python tier, and it is the artifact every later inch cites.

### 4.2 Inch 2 — M0, the oracle pin. **ALREADY DONE — and this repo's record did not know.**

`docs/backlog.md` (2026-08-15, §"The square's FRONTEND edge") closed this
repo's half of M0 and recorded the sunfish half as **STILL OWED**:
*"over there the edge is still A ≡ pypy3(sunfish.py)."* That is no longer
true and has not been since the following day. `tools/ctwin/README.md`
records, dated **2026-08-16**:

> **Interpreter cross-check: `make gate` is INTERPRETER-INVARIANT on this
> corpus.** … Ran the full 7-line gate twice on the same rebased `master`
> commit, same positions/config both times, swapping only the reference
> interpreter … every one of the 7 lines produced byte-identical coverage
> (positions × depth, probe counts, movegen-list counts) and 0 mismatches
> under CPython 3.9.19, matching the pypy3 baseline exactly. The square's
> edge is settled.

**So A ≡ C holds under the pinned oracle, measured, on the full gate.**
M0's RESULT is in. Nobody carried it back across the repository boundary,
and this repository has been carrying a stale "still owed" for five days
— the same cross-repo staleness §1.1 built `--compare` against, hitting a
second time on a different artifact. Recording that is inch 2's first
half.

**What actually remains is smaller and different from what was owed.**
The README is explicit that the swap was *"a one-line, env-gated,
**uncommitted** change to `difftest.py`'s `Engine(["pypy3", …])` call"*,
and that `pypy3` stays the default for a measured reason: CPython is
~3.2× slower on a smoke config and, on the gate's
`QS=0 EVAL_ROUGHNESS=40` line specifically, on the order of two hours
against pypy3's share of a 351 s total-gate run. So the RESULT exists but
is **not reproducible from a clean checkout**, because the flag is not in
the tree.

Inch 2 is therefore: land the env-gated interpreter flag in
`tools/ctwin/difftest.py` so the cross-check is re-runnable rather than
re-derivable only by hand — keeping `pypy3` the default, for the recorded
performance reason.

**DONE, as sunfish PR #256** (`ctwin: make the interpreter cross-check
reproducible`), awaiting review. `SF_PYREF` is in the tree, every
difftest coverage line now NAMES the interpreter that produced it, and a
bad value fails loudly with no silent fallback to `pypy3`. Verified both
ways on that branch at `--n 6 --depth 5 --walk`: 7 positions, 210 probes,
266 movegen lists, **0 mismatches under each**.

### 4.3 Inch 3 — the profile. **LANDED — as a SCHEMA, not a pinned host.**

`docs/c-profile.md` + `docs/c-profile.json` +
`harness/c_profile_probe.py`. This inch changed shape while it was being
done, and the change is the interesting part.

The memo's §3.3 proposed pinning ONE machine as the oracle, and left
"which host" as its open question 3. The tier has **two** development
hosts — an arm64 macOS laptop and an x86-64 Linux box — so pinning either
makes the other silently produce a different envelope. **The ruling
taken: pin the FACTS the corpus depends on, as a schema every host must
satisfy**, with a `#guard` per host rather than an anointed machine.

The ruling carried a stop-condition — *if ctwin depends on any fact where
the two hosts DIFFER, stop and flag* — and it was tested first.
**Measured: 13 facts, 8 depended-on, ZERO disagreements.** The condition
does not fire.

Every fact is decided by `_Static_assert` under
`clang -target <triple> -fsyntax-only`, so clang folds it for the
TARGET's ABI and one laptop certifies a host it cannot execute. The guard
rejects a bad host BY NAME: Linux AArch64 — the divergence the memo
flagged — fails on `char_signed`, with the witness attached.

Three findings from the dependence analysis, all in `docs/c-profile.md`:
`VM_VAL`'s `(int)` conversion of an out-of-range `uint32_t` is
**C23-MANDATED and was implementation-defined under C17**, so the
`-std=c23` pin is load-bearing for the move ordering rather than a
formality; endianness is measured and deliberately NOT depended on,
because `pos_seal`'s hash is never observable (a fast reject in front of
a full `memcmp`, and an unobservable bucket layout); and the corpus has
**zero signed right shifts**, so the memo's right-shift fact is not
depended on either.

`profile_id` stays a first-class envelope field. What changed is what it
identifies: not a machine, but the schema version plus the flag pin —
and that two conforming hosts produce the same envelope is now a CHECKED
property rather than a hope.

### 4.4 Inch 4 — `docs/c-envelope-schema.md`. **LANDED.**

Schema `c-0.1`, mirroring `docs/envelope-schema.md` and
`docs/sv-envelope-schema.md`. **Every vocabulary table is DERIVED from
`docs/c-construct-census.json` rather than chosen**, and a check confirms
all 45 kinds are listed with nothing extra — so "what the ingester
accepts" and "what the corpus contains" cannot silently drift apart.

Three things this envelope has that its two siblings do not, each forced
by a measurement rather than by taste: **`profile_id` is a first-class
field** (the profile is an INPUT to the AST — `_FORTIFY_SOURCE` injects
10 `__builtin_object_size` nodes that are in nobody's source, so same
source + different profile = different program, and the ingester refuses
a mismatch loudly); **spans carry BOTH spelling and expansion location**,
because 6 function-like macros produce corpus constructs and a refusal
that cannot name the macro is one a human cannot act on; and
**`externals` is a list of 27 names + prototypes, not an ingested
subtree**, because the preprocessed TU is 3335 lines around 58 functions.

The document also fixes the `Unsupported` leaf, the determinism contract,
the cache key (`(source, extractor, PROFILE)`), and §6 — the five
structural `#guard`s the ingester will be checked by, all of them facts
the census independently knows.

### 4.5 Inch 5 — `extractors/c/extract.py`.

Contract, unchanged from the other three lanes: NEVER fails on valid C;
anything outside the pinned vocabulary becomes an `Unsupported` leaf
carrying the clang node class and ≤200 characters of source text; output
deterministic (double-run byte-identical); hard errors (unreadable file,
clang diagnostic, profile mismatch) exit non-zero and say why. Cache key
`<stem>-<sha256(source)[:16]>-<sha256(extract.py)[:8]>-<profile_id>`.

Anchored, re-measured today rather than quoted: the Python extractor is
**1913** lines (the memo's 1512 has since grown), SV's is 2495; clang
does the hard work here, so the low end.

**LANDED.** All three contract paths were RUN, not admired: the corpus
extracts twice byte-identically; a missing file and a clang DIAGNOSTIC
both refuse non-zero; and a file containing `switch` produces an
`Unsupported` leaf naming `SwitchStmt` rather than failing. The extractor
also found a bug in ITSELF the way §6 predicts — its first `externals`
walk lacked the `loc.file` filter and reported 30 names where the census
said 27, the three extras being names the SYSTEM HEADERS reference from
their own macro bodies. `--source-name` was added because the corpus is
cross-repo and a path relative to this root would be a fiction.

### 4.6 Inch 6 — `LeanModels/C/Ast.lean` + `LeanModels/C/Json.lean`.

The deep-embedded C AST for the 45 kinds and the ingester that builds it
from the envelope at elaboration time, mirroring `load_program`. No
semantics: this inch produces a Lean TERM and nothing evaluates it.

Scoped by the census and not by the standard: 20 binary operators, 5
compound-assignment operators, 6 unary operators, 8 `castKind`s, the
control-flow set MINUS `switch`, 13 record types, 7 typedefs, 3 enums,
function pointers, string literals, one compound literal.

**LANDED**, and the shape changed once on contact with C's grammar. A
function DEFINITION is the only declaration containing statements and C
has no nested functions, so `Expr`, `Decl` and `Stmt` form NO cycle and
`FunctionDefn` sits on top as a structure — the same shape the Python
lane's `FunctionDefn` has, arrived at from the language rather than
borrowed. `LeanModels/C/` defines its own JSON helpers rather than
importing the Python lane's: it is a SIBLING, not a client (§2.1), and
twenty lines is not a reason to couple two tiers.

`load_c_program` defines the whole `Envelope` (not just the unit),
because `externals` is a claim the ingester must be checkable against
too, and it REFUSES a `profile_id` mismatch — the profile is an input to
the AST, so an envelope from another profile is a different program.

### 4.7 Inch 7 — one function round-tripped, with its `#guard`.

`pyfloordiv` (L160-164):

```c
static int pyfloordiv(int a, int b) {
    int q = a / b, r = a % b;
    if (r != 0 && ((r < 0) != (b < 0))) q--;
    return q;
}
```

Chosen deliberately, and the reasons are the milestone's whole thesis:
it is THREE statements (a two-object declaration, an `if`, a `return`)
exercising declaration-with-initializer, `/`, `%`, `!=`, `<`, `&&`,
`--`, `if` and `return`; it is the site the ctwin README names as **the
#1 place C clones silently diverge from Python**, which makes it the
square's first cross-language datum; and it carries **two of the eleven
armed UB classes in three statements** — the division class at `b == 0`
and at `INT_MIN / -1`, and the signed-overflow class at `q--` when `q`
is `INT_MIN` — so the first thing the tier ever says about C includes
something it must REFUSE.

**M1 IS COMPLETE.** `Examples/c/sunfish/guards.lean` ingests the 5.5 MB
envelope in ~6 s and passes **19 `#guard`s** with no interpreter in the
repository: the five structural ones the schema fixed in advance (58
function definitions, 57 of them `static`, 71 file-scope objects, 19
indirect call sites, 0 unsupported statements) plus the 27-name libc list
verbatim; six on the envelope's own claims (schema version, language,
profile id, profile flags, source path, source sha256); and seven on
`pyfloordiv` — signature, storage, span L160-164, both parameters, three
statements, the `q`/`r` binding order, the `/ % --` operator triple, and
zero unsupported statements inside it.

**They are non-vacuous, checked**: flipping 58 to 59, or appending a name
to the libc list, makes Lean report the failing expression.

### 4.8 What M1 deliberately does NOT decide

Where `Run` lives (§2.4 — measured not to gate this milestone, and
confirmed: the ingester tier does not mention it); whether `Run.exn`'s
`PyErr` payload becomes a parameter; and the endgame.

**One authorized edit was measured UNNECESSARY and not taken.** The
coordinator approved importing `LeanModels/C/` from `LeanModels.lean`
plus a `leanmodels-c-run` exe target. Measured: `Examples/c/sunfish/guards.lean`
imports `LeanModels.C` directly, and the `Examples` lib's `Examples.+`
glob therefore pulls the whole lane into `lake build` — and into CI —
with no edit to either fenced file. Taking the import anyway would couple
the C lane into every Python file's import graph, so that a C change
invalidates the Python tree; it was tried, cost a full Examples rebuild,
and was reverted. The exe is likewise deferred: `leanmodels-c-run` has
nothing to run until the interpreter exists (M4), and a build target that
does nothing is not a container, it is a stub. **Both authorizations are
banked, unspent.**

---

## 5 STILL OWED BY THE OWNER

The architecture memo left three open questions. **All three are now
answered**, and the one this charter added — the endgame — is the only
thing still open.

1. **ANSWERED — the 2026-08-07 "no sunfish deliverable" scope decision
   is amended.** That entry conditioned itself precisely: *"The C tier
   stays a generic lean-surfaces growth direction unless a classic C
   sunfish ever exists (none is planned)."* One exists, it is on sunfish
   MASTER, and the owner chartered the workstream on 2026-08-21. Recorded
   as answered by the charter itself.
2. **ANSWERED (coordinator), and HALF OF IT TURNED OUT UNNECESSARY.**
   `LeanModels/C/` and a `leanmodels-c-run` exe were both approved. The
   directory exists and is in CI — but **neither fenced file was
   touched**: `Examples/c/sunfish/guards.lean` imports `LeanModels.C`
   directly and the `Examples.+` glob does the rest (§4.8). The exe is
   banked until M4 gives it something to run. So the fence held on its
   own, and the authorization is unspent rather than used.
3. **ANSWERED — the question dissolved rather than being decided.** It
   asked which host is the pinned oracle. The answer taken (§4.3,
   `docs/c-profile.md`) is that NO host is: the tier pins the eight facts
   the corpus depends on as a schema, and both development hosts satisfy
   all eight with zero disagreements. Linux AArch64 would not — it fails
   on `char_signed` — and the guard says so by name in under a second.
   **This was M1's critical-path blocker and it is cleared**; the ruling
   is the coordinator's default and remains Thomas's to override.
4. **THE ONLY OPEN QUESTION — which endgame?** §3 presents (a), (b),
   (c) priced. M1 is complete and was endgame-NEUTRAL by construction:
   all three options need the corpus ingested, and nothing in
   `LeanModels/C/` presupposes any of them. The choice binds at **M2**,
   the semantic layer — (a) spends it on the memory model, (b) on a
   Lean-level statement of the gate, (c) on a second corpus.

One further item, not a question but a standing obligation: the ASan
channel is DESIGNED and unverified — ASan binaries do not run in this
sandbox (a trivial `main` built with `-fsanitize=address` times out). It
must be verified on the build box before any battery claims it.

---

## 6 WHAT LANDED WITH THIS CHARTER

* `harness/c_construct_census.py` — the instrument, with `--compare`.
* `docs/c-construct-census.json` — today's corpus, machine-readable,
  including the 45-kind list the memo recorded only as a count.
* `docs/c-tier-charter.md` — this document.
* `docs/backlog.md` §L35 — the record.

Inches 2-7 added, in later commits: `harness/c_profile_probe.py` +
`docs/c-profile.{md,json}`, `docs/c-envelope-schema.md`,
`extractors/c/extract.py`, `LeanModels/C/{Ast,Json,Load}.lean` +
`LeanModels/C.lean`, and `Examples/c/sunfish/{sunfish.json,guards.lean,README.md}`
— plus sunfish PR #256.

**The charter commit itself carried no Lean**, changing only
`docs/backlog.md` among existing files — but "it cannot break anything"
is an argument, not a measurement, so the triad was run then and at every
inch since. At M1's completion: `lake build` **3691 jobs** (the five new
C modules included), `docs_check` **73/73**, `diff_test` **1315 cases, 0
failed** (1202 matched, 113 whitelisted), `script_corpus` **64 scripts, 0
failed** (50 matched, 14 loud). The Python tier is unmoved at every one
of those numbers. A charter that claimed a green it had not seen would
have failed its own covenant in its last paragraph.
