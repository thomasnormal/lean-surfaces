# The C tier: architecture (DESIGN — nothing here is built)

**Status: architecture memo. No Lean exists. Its job is to make the
implementation START-ABLE** — to fix the choices that cannot be
retrofitted, and to leave everything else to the ladder. Scoping is
against the full C23 standard (ISO/IEC 9899:2024) as the owner directed:
the MODEL's type fits C23 from the first line, while the v0
IMPLEMENTATION covers exactly one corpus. Every number below was
measured on this machine by the instruments named; nothing is quoted
from memory.

**This is not the question the two parked C memos ask, and the
difference is the whole point.** `docs/c-extension-bridge-census.md`
priced C-AS-A-PYTHON-BRIDGE: model enough of C and of CPython's C API to
EXECUTE `_struct.c` under the Python tier. `docs/c-intrinsics-proposal.md`
priced the cheaper alternative (name-only bindings). Both are gated and
both stay gated; nothing here unblocks either. This memo is
**C-AS-A-FIRST-CLASS-LANGUAGE** — a third modeled language beside Python
and SystemVerilog, with its own corpus, its own oracle, and its own
differential claim, answering to the C standard rather than to CPython's
interior. The bridge memo's §5 already stated the one thing the two
share: *"UB in the C tier = loud refusal … a C tier that must DETECT UB
is strictly harder than a compiler that may assume its absence."* That
sentence is this memo's premise.

**The precondition the 2026-08-07 backlog entry named has been MET.**
`docs/backlog.md` §"A C surface" recorded the direction and attached a
scope decision: *"No sunfish deliverable attached … The C tier stays a
generic lean-surfaces growth direction unless a classic C sunfish ever
exists (none is planned)."* One now exists:
`tools/ctwin/sunfish.c` in the sunfish-packed checkout — 1310 lines,
sha256 `66c569c147c5e6224adc413d3209d983dd38b240180979c3a1ebb10ef69d14f4`
— a node-identical C TWIN of classic `sunfish.py`, whose own README
states the fidelity contract as *"same position in, same chosen move,
same node count, same score out — verified differentially, not
assumed."* It is a transcription, not a reimplementation. That is what
makes it a semantics corpus rather than a second engine, and it is why
this memo picks it as the flagship. Amending that scope decision is the
owner's call; §10 states it as an open question rather than assuming
the answer.

The same backlog entry guessed the tier would be *"Clight-like: no
`setjmp`"*. The census below overrides that guess: the corpus uses
`setjmp`/`longjmp`, and §6 resolves it rather than pretending otherwise.

---

## 1 The flagship corpus, censused

The house sequencing principle (`docs/backlog.md`, *"read this before
pricing any tail construct on its own"*) is that pricing comes before
building and a headline number is suspect until an instrument re-derives
it. So the census comes first, and every decision below cites it.

**Instrument.** `clang -std=c23 -D_FORTIFY_SOURCE=0 -Xclang
-ast-dump=json -fsyntax-only` on Apple clang 17.0.0
(arm64-apple-darwin25.6.0), walked by a scratch script that tracks
clang's STICKY `loc.file` in document order and counts only nodes whose
file is `sunfish.c` — the 776 top-level declarations include every
system-header declaration the six `#include`s drag in, and filtering by
file is the difference between censusing the corpus and censusing libc's
headers.

**The census is stated under the PINNED PROFILE, and the reason is
itself a measurement.** Under this host's default headers the same file
censuses as **48** node kinds and **2764** implicit conversions; under
`-D_FORTIFY_SOURCE=0` it censuses as **45** and **2732**. Same source,
same compiler, different program — which is §4.3's claim, demonstrated
before it is argued. Every number below is the pinned-profile one.

### 1.1 What is there

| dimension | measured |
| --- | --- |
| lines | 1310 total, 1236 non-blank; preprocessed TU 3200 lines |
| functions with bodies | **54** — 53 `static` plus `main` |
| file-scope objects | **50** (28 with initializers, 22 zero-initialized) |
| structs / typedefs / enums | 13 `RecordDecl` (7 named, 6 anonymous-tagged) / 7 typedefs / 3 anonymous enums |
| distinct AST node kinds | **45** — the entire v0 vocabulary |
| binary + compound operators | 25 distinct, 898 + 24 sites |
| unary operators | 6 distinct (`& ! ++ - * --`), 262 sites |
| implicit conversions | 2732 `ImplicitCastExpr`, **8 distinct `castKind`s** |
| calls | 290 sites; 75 distinct callees; **27 external names** over 124 sites |
| indirect calls | **19**, all through the `movecb` callback parameter `cb` |
| control flow | 230 `if`, 46 `for`, 29 `do`, 5 `while`, 7 `goto`, 3 labels, 9 `break`, 6 `continue`, 32 `?:` |
| `switch` | **0** |
| function-like macros | 7 (`YIELD`, `YIELD_PAWN`, `PACK_VM`, `VM_VAL`, `VM_MOVE`, `PROCESS`, plus 3 object-like bounds) |
| `sizeof` | 9 |
| dynamic allocation | `malloc` 2, `calloc` 1, `realloc` 2, `free` 5 |
| `setjmp` / `longjmp` | 2 / 2 |
| floats | `double` in 66 type positions, 10 float literals, 6 `IntegralToFloating` |
| shifts | 17 (`<<` 11, `>>` 6) |
| division / modulo | 14 |

### 1.2 The seven findings that move the design

1. **No type punning, at all.** The 78 `CStyleCastExpr` nodes are 40
   `NullToPointer` (the `NULL` macro) and 38 arithmetic casts; the 46
   implicit `BitCast`s are `void*`↔`T*` conversions around
   `malloc`/`calloc`/`realloc`/`memcpy`. There is **no `T*`→`U*` cast
   between incompatible object types, and no union anywhere.** The
   effective-type wall (§2.3) is therefore a boundary that never fires
   on the corpus — which is exactly the condition under which it is
   cheap to install correctly and expensive to install later.

2. **No `__int128`, no `_Atomic`, no `volatile`, no `restrict` in the
   source, no VLA, no `_Generic`, no `#if`, no `#pragma`.** The
   accumulator type is `uint64_t` (`mix64`, `hash_key`, the `PACK_VM`
   move-value packing). `MAXMOVES` is `#define 512`, so `uint64_t
   vbuf[MAXMOVES]` is a fixed-size array, not a VLA. `restrict` DOES
   appear — in the libc prototypes the headers declare (`char
   *restrict`), which is why §2.5 states the model's non-claim about it
   rather than omitting it.

3. **`malloc` is v0, not a later rung.** The directive asked the census
   to check whether the corpus is static/stack-only. It is not: all five
   allocation sites are on the search path — `map_init` (L388),
   `map_rehash` (L408/L415), `map_put` (L429/L430, two `realloc`s),
   `kslot_ensure` (L520/L523) — reached through `tpm_store`/`tpm_get`
   on every search. Worse and better: `realloc` MOVES the transposition
   table, so the corpus exercises **provenance transfer** (old object's
   pointers die, a fresh object receives the copied bytes) in its
   hottest data structure. The memory model is not speculative here; the
   first corpus needs it.

4. **`setjmp`/`longjmp` is used — and the v0 slice never takes the
   transfer.** `go_depth` sets `node_cap = 0; deadline = 0.0` (L894)
   before `setjmp(stopjmp)` (L895, with the source comment
   *"unreachable with caps off"*), and both `longjmp` sites are guarded:
   L684 by `node_cap &&`, L685 by `deadline != 0.0 &&`. Under the
   fixed-depth entry point both guards are false. §6 turns this into a
   sound rule instead of a coincidence.

5. **The float need is exactly the clock — and it is guarded.** Every
   `double` in the file is the deadline path: `deadline` (L474),
   `now_s()` (L483, one `clock_gettime`), `go_game`'s arithmetic (L942-943,
   L984-985), and `movetime` parsing (L1295). On the fixed-depth path the
   ONLY float operation evaluated is `deadline != 0.0` — an exact
   comparison of an exactly-representable value, with no rounding
   anywhere. §6 makes that a tier, not a hole.

6. **The C twin and the Python twin hit the same wall at the same node,
   and the C side is strictly easier.** `sunfish.py:322` reads
   `if self.nodes % 2048 == 0 and time.time() > self.deadline: raise Stop`
   — the left conjunct is true at node 2048, so CPython CALLS the clock,
   which is the pass-5/pass-6 frontier the trace clock exists to pass
   (`docs/memory-model.md` §the trace clock). `sunfish.c:683-685` checks
   `deadline != 0.0` FIRST and short-circuits, so the C twin never reads
   the clock on that path. **Lean-C reaches arbitrary fixed depth with an
   EMPTY clock trace where Lean-Python needs the armed pair.** That
   asymmetry is a v0 enabler and, per §5, the sharpest thing the
   cross-language edge checks.

7. **Zero temporary-lifetime sites.** `rotate` and `domove` return `Pos`
   BY VALUE, but a member is never accessed directly on a call result
   (measured: 0 `MemberExpr` whose base is a `CallExpr`). The C23
   temporary-lifetime rule for non-lvalue structures with array members
   is stated in §2 so the model's type is right, and never exercised in
   v0.

---

## 2 DECISION 1 — the memory model

**Adopt the provenance-carrying object model with byte-representable
objects and effective types: the CompCert / CH2O / Cerberus family.
Pointers are `(object, offset)` with provenance; memory is an array of
objects; each object carries a byte-level representation and a
byte-level effective type.** This is the un-retrofittable choice, and
every alternative fails on the corpus: a flat `Nat → Byte` address space
cannot express `realloc` moving the table (finding 3) without inventing
addresses, and cannot detect out-of-bounds structurally; an untyped
model cannot state the effective-type refusal at all.

The shape (a design sketch — no such file exists):

```lean
abbrev ObjId := Nat

/-- A pointer VALUE. `obj = none` is the null pointer. Provenance IS the
object identity: there is no integer address to lose it to. -/
structure Ptr where
  obj : Option ObjId
  off : Int          -- byte offset from the object's base

/-- The byte lattice. `indet` is an indeterminate byte (uninitialized
storage, padding); `ptr p k` is byte k of the representation of p, so a
pointer survives a byte-wise copy and does NOT survive being torn. -/
inductive CByte where
  | conc (b : UInt8)
  | ptr  (p : Ptr) (k : Fin 8)
  | indet

inductive ObjKind where
  | staticDur | automatic (frame : Nat) | allocated
  | stringLit | compoundLit (frame : Nat)

structure CObj where
  kind    : ObjKind
  size    : Nat
  bytes   : Array CByte
  effTy   : Array (Option CType)   -- per byte; none = "no declared type yet"
  live    : Bool
  writable : Bool                  -- false for string literals and const

abbrev Mem := Array CObj
```

### 2.1 Object lifetimes

C23 §6.2.4 gives four storage durations; the model implements them as
`ObjKind` with an explicit `live` flag, and every dereference must
establish `obj < mem.size ∧ live ∧ 0 ≤ off < size` before it reads a
byte. This is the C transcription of the Python tier's standing rule
(`docs/memory-model.md` §heap well-formedness): *"Every semantic
dereference establishes `a < heap.size` — never `getD`, never an
`Inhabited Obj` fallback, never a silent arbitrary object."*

* **Static duration**: allocated once at world init, zero-initialized
  unless a constant initializer says otherwise, `live` forever. The
  corpus has 50.
* **Automatic**: allocated on block entry with ALL bytes `indet`,
  killed (`live := false`) on block exit. A pointer to a dead automatic
  object is still a well-formed VALUE; dereferencing it REFUSES. Note
  this is why `live` is a flag and not a deletion: the standard makes
  the pointer indeterminate, and the model must be able to say so
  loudly rather than reuse the slot.
* **Allocated**: `malloc` creates an object with `indet` bytes and
  `effTy` all `none`; `calloc` with zero bytes and `effTy` all `none`;
  `free` sets `live := false`. `realloc` is the interesting one and the
  corpus needs it: it creates a FRESH object, byte-copies
  `min(old,new)` bytes INCLUDING their effective types, sets the tail
  `indet`, and kills the old object. Every pointer derived from the old
  object is thereby dead — which is the correct semantics and the
  reason provenance had to be in the pointer.
* **String literals**: one object per distinct literal, `writable :=
  false` (a write REFUSES; C23 makes it UB). Whether two identical
  literals share an object is unspecified; the model gives each
  occurrence its own object and REFUSES a pointer comparison between
  two literal objects, so the choice is never observable.
* **Compound literals**: block-scope automatic per C23 §6.5.2.5 — one
  site in the corpus (`VM_MOVE`), whose result is consumed immediately.
* **Temporary lifetime** (non-lvalue structure with an array member,
  C23 §6.2.4): stated for the type's sake, measured 0 sites (finding 7).
* **Thread duration**: not implemented; a `thread_local` declaration is
  a census refusal (rung T).

### 2.2 Byte representations, and what a read may see

An object's VALUE-level read (`load ty p`) decodes the byte run at
`p` under `ty`. Three outcomes, and the third is the point:

1. all bytes `conc` and the pattern is a value of `ty` → that value;
2. the bytes are a full, in-order `ptr q 0 .. ptr q 7` run and `ty` is a
   pointer type → `q`, provenance intact;
3. anything else — any `indet` byte in the run, a torn pointer, a
   pointer run read as an integer, a concrete run read as a pointer —
   **REFUSES, loudly and fuel-independently.**

Reading an indeterminate value is the class the standard has argued
about for two decades (DR 451 and its successors; C23 rewords it again).
**The model does not adjudicate: it refuses.** That is cheaper than
being right and strictly more honest than picking a side, and it is the
covenant verbatim — `.unsupported` is fuel-independent, and nothing is
ever silently wrong.

The corpus needs this to be per-BYTE and not per-object: `setup_fen`
declares `Pos p;` and then `memcpy(p.b, board, 120)` (L1057), leaving
`p.score`, `p.h`, `p.ep`, `p.kp` indeterminate until `pos_seal` runs. A
model that refused any read from a partly-initialized object would
refuse the corpus; a model that allowed it would invent values. The byte
lattice is what makes the middle possible.

### 2.3 Effective types as the strict-aliasing boundary

C23 §6.5 gives the effective-type rule. The model implements it
directly, per byte:

* An object with a DECLARED type has that effective type for its whole
  lifetime; `effTy` is set at allocation and never changes.
* An object with NO declared type (i.e. allocated storage) has
  `effTy = none` until written. A store of type `T` through an lvalue
  SETS the effective type of the written bytes to `T`.
* `memcpy`/`memmove` into an object with no declared type COPIES the
  source's effective types along with the bytes — this is the
  standard's own rule, not a convenience, and it is what makes
  `memcpy(hist[0].b, INITIAL, 120)` (L1020) work without a cast.
* A read of type `T` from bytes whose effective type is `U` **REFUSES**
  unless `T` is compatible with `U`, or `T` is a character type (the
  standard's own escape hatch for byte inspection), or the read is
  through the aggregate containing `U` as a member.

**Why this must be static and per-byte rather than a sanitizer check:
no sanitizer detects it.** Measured, on the pinned clang: a
`*(int*)&float_var` read produces **no diagnostic** under
`-fsanitize=undefined`, under `-fsanitize=address`, or under both. The
raise channel (§5) catches arithmetic and spatial UB; strict aliasing is
invisible to it. If the model does not carry effective types, the
project has NO instrument that would ever notice the violation — and
the corpus, which has zero violations today, would silently start
inventing behavior the day one appeared.

### 2.4 Unions and type punning

Zero sites in the corpus, so this is stated for the type and built at
rung R2. C23 §6.5.2.3 permits reading a union member other than the one
last stored, reinterpreting the object representation. The model admits
such a read exactly when §2.2's rule already admits it: the byte run
must be fully `conc` and a valid representation of the read type.
Padding bytes stay `indet` (a store to a union member does NOT define
the padding), so the punning reads that "work" are admitted and the ones
that read padding refuse — which is the honest split, decided by the
byte lattice rather than by a special case. The common-initial-sequence
rule (§6.5.2.3) is a compatibility test on `effTy`, not a new mechanism.

### 2.5 What the model deliberately does not claim

* **`restrict` is INGESTED and NEVER EXPLOITED.** The declarations reach
  the model through the libc prototypes; the model records the qualifier
  and does nothing with it. Ignoring a programmer promise is always
  sound for an interpreter (it can only admit more behavior), and it is
  recorded here as a deliberate non-claim so nobody later reads
  `restrict` in the AST and assumes the model checked it. Enforcing it
  is a rung; the provenance model is exactly the substrate that would
  make it checkable, which is a further argument for the model chosen.
* **Integer↔pointer casts REFUSE in v0.** Measured 0 sites. This is
  what lets the memo defer the PNVI-vs-PVI question (Cerberus's central
  open problem) without the deferral costing anything: with no
  round-trips, every provenance discipline agrees.
* **Pointer comparison across objects REFUSES.** The standard makes
  relational comparison of pointers into different objects undefined and
  equality comparison of a one-past-end pointer with a pointer to an
  adjacent object unspecified. The model refuses both rather than
  choosing a layout.

### 2.6 The v0 object-kind set, and the expansion rungs

The TYPE above is C23-complete. The IMPLEMENTATION at v0 is:

| kind | v0 | rung |
| --- | --- | --- |
| static duration, constant-initialized or zero | **yes** (50 objects) | — |
| automatic, fixed size | **yes** | — |
| allocated (`malloc`/`calloc`/`realloc`/`free`) | **yes** (5 sites) | — |
| string literal (non-writable) | **yes** (96 occurrences) | — |
| compound literal | **yes** (1 site) | — |
| union member / punning | no | R2 |
| bit-fields | no (0 sites) | R2 |
| flexible array member | no | R2 |
| variably-modified / VLA | no (0 sites) | R5 |
| `volatile`-qualified object | no (0 sites) | R6 |
| `_Atomic` object, thread duration | no (0 sites) | R6 |
| temporary lifetime | stated, 0 sites | R2 |

---

## 3 DECISION 2 — the semantic-latitude taxonomy

C23 divides latitude three ways (§3.4 and Annex J), and the covenant
maps onto it cleanly because the three kinds fail differently.

### 3.1 Undefined behavior → LOUD REFUSAL

The rule, unchanged from the Python tier: `.unsupported` is
fuel-independent, `.timeout` is the only exhaustion outcome, and nothing
is ever silently wrong. A definitional interpreter that must DETECT UB
does strictly more work than a compiler that may assume its absence —
and that extra work IS the product.

The classes armed at v0, each with how it is detected and whether the
corpus reaches it:

| UB class | detected by | corpus |
| --- | --- | --- |
| signed integer overflow (`+ - *`, unary `-`, `++`/`--`, compound forms) | the interpreter's own range check | 187 binary, 105 unary/compound |
| out-of-bounds array / pointer access | **structural** — `(obj, off)` with a size | 295 subscripts |
| pointer arithmetic leaving the object | structural | — |
| null / dead-object dereference | structural (`obj = none`, `live`) | 5 `free` sites |
| invalid shift (count ≥ width, negative count, negative left operand, signed left-shift overflow) | the shift arm | 17 sites |
| division / modulo by zero, and `INT_MIN / -1` | the division arm | 14 sites |
| strict aliasing / effective-type violation | **§2.3 — no sanitizer can** | 0 sites |
| indeterminate (uninitialized) read | **§2.2 byte lattice — no sanitizer available on this host** | 1 real site (L1057) |
| `realloc(p, 0)` (UB in C23; implementation-defined before) | the allocator arm | 2 `realloc` sites |
| unsequenced modification of one object (§6.5) | the sequencing census, §3.2 | 64 candidate expressions |
| library-contract UB (overlapping `memcpy`, `printf` format/arg mismatch, `strtok` state, out-of-range `atoi`) | per-function, in the libc slice | 124 external call sites |

Two of these — strict aliasing and indeterminate reads — are detectable
by NO available dynamic instrument on the pinned host (§5.2 measures
it). They are precisely the two the memory model was chosen to catch. If
the model were weaker, the project would have no answer for them at all.

### 3.2 Unspecified behavior → CANONICAL ORDER + A COMMUTATIVITY CENSUS

**Decision: fix left-to-right as the EXECUTION order, and require a
static census that the order is unobservable. Do NOT explore the space
of orders Cerberus-style.** Justification, in the terms this project is
built on:

* **Everything downstream needs a FUNCTION.** The interpreter's outcome
  type is `Run σ α` with four constructors; `fuelMono` is a
  monotonicity statement about a function; `#py_check` requires
  kernel-reducible structural recursion; the batch protocol emits
  **exactly one output line per job, in job order**. An exploring
  semantics produces a RELATION and a SET of outcomes, and every one of
  those five artifacts would have to change shape. Exploration is the
  right answer for a tool whose product is *"the set of behaviors this
  program may have"* — that is Cerberus's product, and it is a good
  one. It is the wrong answer for an interpreter whose product is *"the
  one behavior, or a refusal."*
* **A census makes the canonical order EXACT rather than arbitrary.**
  Where the census passes, the canonical order provably IS the order —
  every permitted order gives the same result — so the differential
  claim against the oracle is exact and not "exact modulo a choice we
  both happened to make." Where it fails, the program refuses and the
  telemetry names the site. Compare the alternative: executing
  left-to-right WITHOUT a census would silently agree with clang
  whenever clang happens to pick left-to-right, and the model would be
  making an unearned claim about a program whose result is not
  determined by the standard. That is exactly the failure mode the
  covenant exists to prevent.
* **CompCert solved the same problem by TRANSFORMATION and we cannot.**
  Its C→Clight pass pulls side effects out of expressions, so Clight has
  no unsequenced effects to worry about. Our envelope must be the
  program the oracle compiles — a normalizing rewrite would put a
  transformation between the model and the oracle and quietly move the
  claim. So we census.

**The census, precisely.** Within each unsequenced region (a full
expression's subexpressions between sequence points; C23 §6.5, and
§6.5.2.2 for function arguments), REFUSE unless **at most one operand
position carries an effect**, where an effect is a store, a `++`/`--`,
a call, or an allocation/IO. When more than one does, admit only if a
conservative may-alias check proves the effect sets disjoint and neither
touches static-duration state the other reads. Anything else refuses,
naming the expression.

The census is **sound but incomplete by construction** — it refuses
programs whose order genuinely does not matter but whose aliasing it
cannot see. That is the preferred failure direction, and it is the same
trade the Python tier's `moduleClockOk` census makes (*"an unanalysable
statement fails the census — it might"*).

**Measured on the corpus**: 828 full expressions in statement position,
of which **64** carry ≥2 effects. Their shapes: **32 are `x = f(…)`** —
the assignment's store is sequenced AFTER the right operand's value
computation, so there is exactly one effect POSITION and the rule admits
them by inspection. The remaining **32** need the disjointness check: 9
assignment + `++`, 9 two-call, 6 assignment + two calls, 5 two
assignments, 2 four assignments, 1 four calls. So the may-alias analysis
has to be good enough for four-call full expressions and nothing more
exotic, at 32 sites. That is a small, bounded, measurable amount of work
— the number is here so the implementation can be priced against it
rather than against a fear.

One nuance the taxonomy must keep straight: **unsequenced modification
of the same object is UB (§3.1), while the ORDER of evaluation is
unspecified (§3.2).** The census serves both — it is the same syntactic
walk — but a failure is reported as the right kind, because "your
program is undefined" and "your program's result depends on a choice we
refuse to make for you" are different messages to a user.

### 3.3 Implementation-defined behavior → A PINNED PROFILE DOCUMENT

**Decision: a versioned profile document, `docs/c-profile-<id>.md` with
a machine-readable `c-profile.json` beside it, pinned exactly the way
CPython 3.9 is pinned — and stamped into every envelope, because unlike
the CPython pin it changes the AST PAYLOAD.**

Measured on the current candidate oracle (Apple clang 17.0.0,
arm64-apple-darwin25.6.0, `-std=c23`):

| item | measured value |
| --- | --- |
| `__STDC_VERSION__` | `202311L` |
| `CHAR_BIT` | 8 |
| **plain `char` signedness** | **SIGNED** |
| `sizeof(int)` / `long` / `long long` / `void*` | 4 / 8 / 8 / 8 (LP64) |
| signed representation | two's complement (C23 §6.2.6.2 mandates it) |
| endianness | little |
| `__STDC_IEC_60559_BFP__` | **NOT DEFINED** — this toolchain does not claim Annex F |
| `__STDC_NO_VLA__` | not defined (VLAs available; the model refuses them anyway) |
| right shift of a negative value | arithmetic |
| `_FORTIFY_SOURCE` | **must be pinned to 0** — see §4.3 |

Two of those are load-bearing rather than decorative. **`char` is SIGNED
here and UNSIGNED on Linux AArch64** — same architecture family, opposite
answer — and the corpus stores the board as `char b[120]` compared
against `'R'`, `'q'`, `'.'`. Nothing in the corpus is currently
sensitive to it (every board character is ASCII below 128), but the
profile is the only thing standing between that fact and an unearned
portability claim, so a profile mismatch between the envelope and the
runner must be a **LOUD harness error, never a silent re-run**.

And **the oracle does not define `__STDC_IEC_60559_BFP__`** — it does
not claim Annex F conformance. That is a measured argument for keeping
floats out of v0 (§6) rather than an aesthetic one: a float tier built
against this oracle could not state which rounding contract it was
differential-testing against.

---

## 4 DECISION 3 — the front end

**Decision: C23 translation phases 1-6 (and all preprocessing) run
OUTSIDE Lean, in `extractors/c/extract.py`, driven by
`clang -Xclang -ast-dump=json`. Lean owns phase 7 — the semantics of the
translation unit — and nothing earlier. Phase 8 (linking) is out of tier:
v0 is single-translation-unit.**

### 4.1 Why clang's AST and not our own parser

The house rule is already normative and visible in three lanes: the
frontend is a third-party tool wherever one exists (CPython `ast`,
pyslang, OpenVAF); SPICE's hand-written line parser is the one exception
and its docstring justifies it. C has an excellent third-party frontend.
Beyond the house rule, three reasons specific to C:

1. **The front end must agree with the ORACLE's front end, or the
   differential claim compares two different programs.** Using the
   oracle compiler's own parser makes that agreement structural rather
   than asserted. This is a stronger position than the Python lane
   enjoys, where CPython's `ast` and CPython's compiler are different
   passes of one program; here they are the same program.
2. **The grammar is not the hard part; the conversions are.** C's usual
   arithmetic conversions, integer promotions, array-to-pointer decay,
   and function-to-pointer decay are where a hand parser would go wrong
   — and clang MATERIALIZES every one of them as an explicit node.
   Measured: 2732 `ImplicitCastExpr` nodes in exactly 8 `castKind`s
   (`LValueToRValue` 1635, `ArrayToPointerDecay` 335,
   `FunctionToPointerDecay` 277, `IntegralCast` 264, `NoOp` 171,
   `NullToPointer` 76, `BitCast` 46, `IntegralToFloating` 6). The
   ingester never re-derives a conversion;
   it reads one off. That is a large fraction of the semantics arriving
   pre-solved.
3. **`clang -E` alone leaves us writing a C parser.** The preprocessor
   is the easy half.

The risk, named so it is a review point: **we inherit clang's AST
vocabulary, including any place it normalizes a distinction the standard
keeps.** Mitigation is the existing convention — the ingester REFUSES on
any `kind` outside a PINNED vocabulary, emitted as an `Unsupported` leaf
with the clang node class and ≤200 characters of source text, exactly as
`docs/envelope-schema.md` and `docs/sv-envelope-schema.md` specify. The
vocabulary is written down in a new `docs/c-envelope-schema.md`, and the
census says how big it has to be to start: **45 node kinds.**

### 4.2 The envelope

Mirrors the other two lanes:

```
schema_version : "c-0.1"
language       : "c"
frontend       : {name: "clang-ast-json", version: <FAMILY>}
profile_id     : <the §3.3 profile's id>
source_file    : <repo-relative>
source_sha256  : <hex of source bytes>
translation_unit : {kind: "TranslationUnit", decls: [...]}
externals      : [ <declared-but-not-defined names the TU references> ]
lean_blocks    : []
```

`externals` exists because the preprocessed TU is 3200 lines of which
the corpus's own content is 54 functions and 50 objects: the extractor
FILTERS by `loc.file` to the main source and records the referenced
external declarations as a list of names and prototypes rather than
ingesting the headers' bodies. Measured, that list is **27 libc names**
— `abort atoi atol calloc clock_gettime fclose fflush fgets fopen
fprintf free getenv longjmp malloc memchr memcmp memcpy printf puts
realloc setjmp snprintf sprintf strchr strcmp strcpy strtok` — a small,
reviewable surface, and the same shape as the intrinsics contract's
pinned inventory.

Spans carry both the SPELLING and the EXPANSION location, because 7 of
the corpus's constructs live inside function-like macros and a refusal
that cannot name the macro is a refusal a human cannot act on.

### 4.3 The `frontend.version` lesson, applied — and it is worse here

The Python lane recorded this lesson twice, at two different landings:
an envelope's `frontend.version` stamps the EXTRACTING interpreter, so
re-extraction on another host dirties tracked envelopes with
byte-identical payloads — 3.9.25 ↔ 3.9.19 across two machines, 53 files
of churn the second time, *"the INSTRUMENT FINDING recorded at the `%`
landing, hitting for the second time."*

**Two corrections, and the second is a C-specific hazard the Python lane
never had:**

1. **Stamp the compiler FAMILY, never the point release.**
   `"apple-clang-17"`, not `"17.0.0 (clang-1700.6.4.2)"`. Reproducing
   that churn bug in a new lane, having read the entry describing it
   twice, would be inexcusable.
2. **The system headers change the PAYLOAD, not just the stamp.**
   Measured: with Apple's default headers, `memcpy`/`strcpy`/`sprintf`/
   `snprintf` are rewritten by `_FORTIFY_SOURCE` into
   `__builtin___memcpy_chk` and friends, and **10 `__builtin_object_size`
   nodes appear in the AST that are in no one's source.** With
   `-D_FORTIFY_SOURCE=0`: measured **0** of each. So the profile is not
   a stamp on the side of the envelope — it is an INPUT to the AST, and
   an envelope extracted under a different profile is a different
   program. Hence: `profile_id` is a first-class envelope field, the
   ingester REFUSES an envelope whose profile does not match the
   runner's pin, and the cache key is
   `<stem>-<sha256(source)[:16]>-<sha256(extract.py)[:8]>-<profile_id>`
   — the existing `extractor_digest()` discipline plus the profile,
   because a C envelope is a function of (source, extractor, PROFILE).

### 4.4 Determinism and the never-fail contract

Restated from the other lanes because it is a contract, not a habit: the
extractor NEVER fails on valid C; anything outside the vocabulary
becomes an `Unsupported` leaf; output is deterministic (double-run
byte-identical); hard errors (unreadable file, clang diagnostic,
profile mismatch) exit non-zero and say why.

---

## 5 DECISION 4 — the oracle, the harness, and the triangle

### 5.1 The oracle

**Pinned clang at a pinned version, `-std=c23 -O0 -g
-D_FORTIFY_SOURCE=0 -fno-strict-aliasing`**, with the profile document
of §3.3 recording what that compiler decided. `-O0` because the model is
a definitional semantics and the oracle should not be exploiting UB it
is being tested against; `-fno-strict-aliasing` pinned EXPLICITLY rather
than left to fall out of `-O0`, so the choice is a recorded decision.

State the asymmetry plainly: **the model is stricter than its oracle.**
At `-O0` clang will happily run a strict-aliasing violation and print an
answer; the model refuses. So the harness must treat "model REFUSES,
oracle answers" as a REFUSE row — telemetry, prioritization — and never
as a divergence. That is the Python lane's exit-3 convention verbatim,
and the invariant behind it survives unchanged: **3 and 4 are never
agreement.**

### 5.2 The raise channel, measured

`-fsanitize=undefined,address -fno-sanitize-recover=all` is the analogue
of CPython raising an exception: it turns UB from "a value the oracle
invented" into "a distinguished outcome the model can be compared
against." Measured on the pinned clang with `-std=c23`:

| probe | UBSan verdict |
| --- | --- |
| `INT_MAX + 1` | **DETECTED** — `signed integer overflow` |
| `1 << 40` | **DETECTED** — `shift exponent 40 is too large` |
| `-1 << 1` | **DETECTED** — `left shift of negative value` |
| `INT_MAX << 1` | **DETECTED** — `left shift of 2147483647 by 1 places cannot be represented` |
| `1 / 0` | **DETECTED** — `division by zero` |
| `a[7]` on `int a[4]` | **DETECTED** — `index 7 out of bounds` |
| `*(int*)NULL` | **DETECTED** — `load of null pointer` |
| **`*(int*)&float_var`** | **NOT DETECTED** — no diagnostic, any sanitizer combination |
| **read of an uninitialized `int`** | **NOT DETECTED** — needs MSan, unavailable on Darwin/arm64 |
| use-after-free | not UBSan's job — ASan's |

Two findings the design turns on. **First: `-fno-sanitize-recover=all`
is REQUIRED, not optional.** Measured: by default UBSan PRINTS the
diagnostic and CONTINUES, returning the wrapped value — the
`INT_MAX + 1` probe printed its diagnostic and then `-2147483648`. An
oracle that continues past UB produces a value the model refuses, and
the differential row reads as a DIVERGENCE when it should read as a
REFUSE. Recover-off turns the first UB into a distinguished exit code.
**Second: the two UB classes no sanitizer catches are exactly the two
the memory model was chosen for** (§2.3, §2.2). The raise channel and
the memory model are complementary, not redundant, and neither alone
covers the armed set.

One honest environment note, recorded rather than assumed: **ASan
binaries do not run in this sandbox** — measured, a trivial
`int main(void){return 0;}` built with `-fsanitize=address` times out.
The ASan channel is DESIGNED and must be VERIFIED on the build box; it
is battery milestone M1's gate, not a background assumption.

### 5.3 The battery

`harness/c/diff_test.py` + `harness/c/cases.json`, wired into
`tools/ci.sh` through the existing `maybe <name> <required-file> <cmd>`
helper (present ⇒ run, absent ⇒ SKIP, reported, never silently
omitted). Two `jobs.jsonl` dialects, mirroring `Main.lean`'s:

```
--c-batch         {"path":"….json","function":"f","args":[…],"fuel":N?}
--c-script-batch  {"path":"….json","argv":[…],"stdin":[…],"fuel":N?}
```

One runner process for the whole batch — the load-bearing lesson
recorded in three places (*"never spawn one runner per row"*: 615 rows
went from hours to ~11 s). Exactly one output line per job, in job
order, flushed as produced; an unexecutable job emits a
`{"status":"runner-error"}` row so the row count stays honest and the
pairing is positional and defended.

Script rows carry `"stmts": N` — the C analogue of the Python lane's
`"live"`, and for the same reason: **a run that executed nothing must
never be scored as agreement.** Exit codes carry over unchanged: 0 ok /
1 the program exited nonzero / 3 LOUD refusal / 4 fuel exhausted / 5
model-vs-oracle disagreement. And the standing prohibition carries over
too: never add an `"expect": "unsupported"` whitelist row to silence a
mismatch — whitelists document known tier gaps and nothing else.

Why v0 needs the SCRIPT dialect and not only the typed-call one: the
corpus's real surface is a UCI loop on stdin/stdout. The typed dialect
covers the scalar leaves (§8, M1); everything interesting is a whole
program.

### 5.4 THE TRIANGLE — actually a square, and the diagonal is the product

Four vertices, one program:

* **A** — compiled `sunfish.c` (pinned clang) — the C oracle
* **B** — Lean-C(`sunfish.c`) — the new tier
* **C** — CPython 3.9.19 running `sunfish.py` — the Python oracle
* **D** — Lean-Python(`sunfish.py`) — the existing tier

The Python-side vertices are not hypothetical: the corpus
`Examples/python/sunfish/sunfish.py` is **byte-identical** to the
sunfish master engine (measured, sha256
`f6c481a6a2c9f4c3686c13115adb36719693676d47b0121af03347d3a01219a1` —
engine `e670434`, re-pinned 2026-08-19, docs/backlog.md §L15), and
`sunfish.c` is a transcription of the same engine file. **The two pins
are maintained in different repositories, so the square's Python-side
identity is only as current as the OLDER of them**: whenever this corpus
is re-pinned, `sunfish.c`'s own pin has to be checked against the same
engine commit before A ≡ B ≡ C ≡ D is claimed at that commit. That check
is not part of this repository's triad.

**Edges that exist today.** A ≡ C is measured continuously by
`tools/ctwin/difftest.py`: every MTD-bi probe compared byte for byte on
`(depth, gamma, score, killer move, cumulative node count)`, plus
`gen_moves()` order and `value()` of every move at each test position
and one ply below. **With one caveat that must be stated and fixed:
difftest drives `sunfish.py` under pypy3 (via `pyref.py`), not under the
pinned CPython 3.9.19.** So the edge as measured today is
A ≡ pypy3(sunfish.py), not A ≡ C. Closing that is cheap — an interpreter
flag on `pyref.py` — and it is milestone M0 precisely because it costs
almost nothing and either holds or finds something today. C ≡ D is the
existing Python tier's differential, currently walled at the 2048-node
clock frontier with the armed trace pair carrying it past.

**Edges the C tier adds.** A ≡ B is the C tier's own differential.
**B ≡ D is the capstone: two Lean interpreters, two languages, one node
count.**

**What the square uniquely catches — three named classes, none visible
from any single edge:**

1. **A misreading shared by a model and its oracle.** If Lean-C and
   clang both compute `pyfloordiv`'s `%` the way C truncates, A ≡ B
   passes. If Lean-Python and CPython both floor, C ≡ D passes. Only
   B ≡ D puts the two RULES against each other on the same input — and
   the ctwin README names floor division as the **#1** place clones
   silently diverge, in this very corpus, with `pyfloordiv`/`pymod`
   written specifically to bridge it. The bug class is not hypothetical;
   it is the one the corpus was built to defend against.
2. **A model that is right about its oracle and wrong about the
   standard.** A ≡ B is a claim about ONE compiler on ONE platform.
   B ≡ D forces the C model's answer to coincide with a model whose
   oracle is a different implementation of a different language — a
   coincidence a platform-specific misreading cannot survive, because
   the Python side has no corresponding latitude. Concretely: `char`
   signedness, right-shift of negatives, and out-of-range integer
   conversion (§3.3) are all places where the C model could be
   faithful to Apple clang and wrong about C. Python's `//`, `%`, and
   unbounded ints have no such freedom, so B ≡ D is a check on the
   PROFILE and not only on the semantics.
3. **A refusal that hides a divergence.** The square compares the two
   tiers' FRONTIERS, not only their answers — and the census already
   predicts an asymmetry here (finding 6). The Python twin calls
   `time.time()` at node 2048; the C twin short-circuits on
   `deadline != 0.0` and never does. So Lean-C should reach arbitrary
   fixed depth on an EMPTY clock trace while Lean-Python needs the armed
   pair. **If Lean-C ever needs a clock reading on that path, the model
   is wrong about the short circuit** — and that bug is invisible from
   the C side alone, because a C-only battery would simply supply the
   reading and agree.

The square is only meaningful because `sunfish.c` is a TRANSCRIPTION
whose fidelity is a continuously-enforced gate. That is what makes
B ≡ D a comparison of two SEMANTICS rather than of two chess engines.

---

## 6 DECISION 5 — the effect walls, by kind

Each wall names its Python-tier precedent and its census result, because
a wall with no precedent is a new claim and should be visible as one.

| kind | v0 treatment | precedent | census |
| --- | --- | --- | --- |
| threads, `<threads.h>`, `_Atomic` | **OUT BY KIND** — loud | none; the bridge memo bucketed GIL/thread macros as boilerplate precisely because nothing modeled them | 0 |
| `volatile` | **OUT BY KIND** | none | 0 |
| signals, `<signal.h>` | **OUT BY KIND** | none | 0 |
| `setjmp` | **admitted, restricted** (below) | the H4 defunctionalized continuation is the nearest thing | 2 |
| `longjmp` | **LOUD** (below) | the poisoned-binding refusal: model the boundary, refuse the transfer | 2 |
| stdout / stderr | **MODELED** as world data | *"stdout is `World` data … `print` becomes a tier builtin appending to it"* | `printf` 8, `puts` 15, `fprintf` 4, `fflush` 3 |
| stdin, `fopen`/`fgets`/`fclose` | **MODELED as an INPUT TRACE** | the trace clock: *"time is an input, not an effect"* | `fgets` 2, `fopen`/`fclose` 1 each |
| other `FILE*` operations | **LOUD** | the dict method wall | 0 |
| `getenv` | **MODELED** as a marshalled input (assoc list at world init) | *"argv is a marshalled global … supplied at world initialization"* | 2 |
| `clock_gettime` | **trace input; EMPTY trace in v0** | the trace clock verbatim | 1, unreachable on the v0 path |
| floats | **EXACT-ONLY tier** (below); IEC 60559 is rung R4 | the trace clock's integer restriction and its scoped claim | 66 type positions, all on the deadline path |
| `malloc`/`calloc`/`realloc`/`free` | **IN v0** — modeled heap with lifetime tracking | the H1 heap and `Heap.WF` | 10 sites, all on the search path |
| VLA / `alloca` | **OUT BY KIND** (`alloca`: never) | — | 0 |
| `abort` | a distinguished TERMINAL outcome, not a refusal | the runner's exit-status boundary | 1 |
| varargs (`printf` family) | the format string is **its own small spec**, pinned per directive | the bridge memo said it first: *"the format-string mini-language is its own small spec"* | ~15 distinct format strings |

### 6.1 The `setjmp` split — the census's correction to the parked entry

The 2026-08-07 entry guessed *"Clight-like: no `setjmp`."* The corpus has
it, so the rule has to be right rather than absent:

* **`setjmp` is admitted** only as a direct call in one of the four
  syntactic contexts C23 §7.13.2.1 permits (the entire controlling
  expression of a selection or iteration statement; one operand of a
  relational or equality operator against an integer constant
  expression; the operand of `!`; a whole expression statement). The
  model gives it the FIRST, direct return: 0. Both corpus sites are
  legal — `if (setjmp(stopjmp))` at L895 and `if (!setjmp(stopjmp))` at
  L948.
* **`longjmp` is LOUD in v0.**

**Why the pair is sound and not a convenient fiction:** because the
transfer refuses, the model can never RETURN from `setjmp` a second
time, so the 0 return is the only reachable behavior and it is never
wrong. Any run that would take the transfer refuses AT the `longjmp`
site — it never silently continues and never invents the unwind. This is
the exact shape of the Python tier's poisoned-binding refusals: model
the boundary, refuse the transfer.

**Measured, the corpus is admitted end-to-end under it** (finding 4):
`go_depth` zeroes both caps before `setjmp`, and both `longjmp` sites
are guarded by conditions that are false.

Rung R3 arms `longjmp`, and the memory model already has what it needs:
the saved environment is an object with a lifetime (so "the function
containing the `setjmp` has returned" is a `live` check, not a new
mechanism), and C23 §7.13.2.1's rule that non-`volatile` automatic
objects modified between `setjmp` and `longjmp` have indeterminate
values is **exactly the `indet` byte** of §2.2. The rung is cheap
because §2 was designed for it.

### 6.2 Floats: the EXACT-ONLY tier, and why it is a tier and not a hole

**v0 admits `double` values, assignment, and comparison, and REFUSES
every operation whose IEEE rounding the model would have to guess.**

This is the trace clock's argument transposed. That decision said the
model has no float tier and *"a float reading would immediately meet
arithmetic whose rounding the model refuses to guess"* — so readings
became integers and the claim was scoped loudly: *"the model says
NOTHING about runs under float readings."* Here the C twin makes the
same restriction land differently, and better: the corpus's fixed-depth
path evaluates exactly ONE float operation, `deadline != 0.0`, and both
operands are exactly representable. **No rounding occurs, so no rounding
has to be modeled, and the claim is not scoped away — it is exact.**
`go_game`'s arithmetic (`start + movetime_s`, `(deadline - start) * 0.8`)
rounds, and refuses, at the rounding site.

Rung R4 is the real IEC 60559 tier. Its gate is stated up front: a
toolchain that DEFINES `__STDC_IEC_60559_BFP__` (measured: the current
candidate oracle does NOT, §3.3), or an explicitly scoped
non-Annex-F claim. Without that gate the rung would be
differential-testing against a contract neither side signed.

---

## 7 The tier ladder

### 7.1 v0 — the fixed-depth `sunfish.c` slice, end to end

**Features** (all measured in §1): the 45 AST node kinds; integer types
`char`, `signed`/`unsigned char`, `int`, `unsigned`, `long`,
`uint64_t`/`unsigned long long`, and the enum constants — **no
`__int128`**, measured; arrays including 2-D (`int[6][120]`); structs
(13) and typedefs (7); pointers, including function pointers
(`movecb` and its 19 indirect call sites); string literals; one
compound literal; `static` file-scope storage and `const`;
`if`/`for`/`while`/`do`/`goto`+labels/`break`/`continue`/`?:` —
**no `switch`**, measured 0; the 27-name libc slice; the object kinds of
§2.6; the effect walls of §6.

**UB armed**: the eleven classes of §3.1.

**Corpus**: `sunfish.c` (pinned by sha256) driven at fixed depth, plus
an `Examples/c/` lab set on the `Examples/python/*_lab` pattern — one
lab per hard rule (`alias_lab` for effective types, `indet_lab` for the
byte lattice, `seq_lab` for the sequencing census, `alloc_lab` for
`realloc` provenance, `jmp_lab` for the `setjmp` restriction).

**Not in v0, deliberately**: the entire PROOF layer. No VC walker, no
tactic layer, no theorem surface. v0 is an interpreter and a battery.
That is 11,550 of the Python lane's 23,306 Lean lines that v0 does not
write, and saying so is most of why the price in §8 is what it is.

### 7.2 The rungs

| rung | features | UB newly armed | corpus |
| --- | --- | --- | --- |
| **R1 statement completion** | `switch`/`case`/`default` incl. fallthrough and jumps into the body; the remaining declaration forms | jump into a VM scope | `switch_lab`; the first non-sunfish C file |
| **R2 layout** | unions, type punning, bit-fields, flexible array members, common initial sequence, temporary lifetime | punning through padding; trap representations; bit-field overflow | `punning_lab`; `_struct.c`-shaped byte code |
| **R3 nonlocal transfer** | `longjmp`, the full §7.13 contract | `longjmp` after return; the `volatile`/indeterminate rule | `jmp_lab` armed; the corpus's `go_game` |
| **R4 floats** | `float`/`double`/`long double`, Annex F binding, rounding modes, `FLT_EVAL_METHOD` | float exceptions; conversion out of range | gated on `__STDC_IEC_60559_BFP__`; `go_game`'s deadline arithmetic |
| **R5 variably-modified** | VLAs, variably-modified types, pointer-to-VLA | negative/zero VLA size | `vla_lab` |
| **R6 concurrency** | `volatile`, signals, `_Atomic`, `<threads.h>`, thread storage duration | data races; the C23 §5.1.2.4 memory model | deliberately LAST — this is a memory-ORDER relation, a different KIND of model from a state function, and it is the one rung that would change the interpreter's type |
| **R7 the rest of C23** | `_BitInt(N)`, `typeof`/`typeof_unqual`, `constexpr`, `auto`, attributes, `#embed`, `_Generic`, `restrict` ENFORCEMENT, multiple translation units and linkage | — | the stdlib-shaped corpora |

R6 is last for a structural reason worth stating once: every other rung
adds constructs to a semantics that stays a function from state to
state. R6 replaces that with a relation over executions. It is the only
rung that is not a widening, and treating it as one would be the same
mistake as building an exploring evaluation-order semantics (§3.2).

---

## 8 Price, and the first three battery milestones

### 8.1 Price by analogy

Measured anchors in this repo: the Python lane is **23,306 Lean lines**
across `LeanModels/Python/*` + `Main.lean`, of which the interpreter core
(`Ast` 571 + `Json` 1623 + `Runtime` 1301 + `Semantics` 6191 + `Script`
868) is **10,554** and the proof layer (`Obs` 3067 + `VCTactic` 2404 +
`ClockErase` 2654 + `VC`/`VC2`/`VCTests` 1509 + `Surface` 930 +
`LoopTactic` 487 + `Logic` 326 + `Delab` 173) is **11,550**. The SV lane
is **8,166** Lean lines. Extractors: Python 1512, SV 2495 Python lines;
`harness/diff_test.py` 442.

The C tier's v0 brackets BETWEEN the two lanes, and the reasoning is
structural rather than a guess:

| component | estimate | anchored against |
| --- | --- | --- |
| `Ast` + `Json` ingester | 2,000-3,000 Lean | Python's 2,194 for a comparable node count; C's TYPE grammar is bigger, its node vocabulary (48) is not |
| memory model + WF lemmas | 1,500-2,500 Lean | no in-repo analogue — the Python heap is `Array Obj` with 4 constructors; the honest external anchor is that CompCert's memory model is thousands of lines of Coq WITHOUT effective types |
| interpreter + libc slice | 3,000-5,000 Lean | Python's `Semantics` 6191; C's expression semantics is more mechanical but the conversion lattice is wide |
| `Main.lean` batch arms | ~150 Lean | the existing arms |
| extractor | 1,200-2,000 Python | Python 1512 / SV 2495; clang does the hard work, so the low end |
| harness | 500-800 Python | `diff_test.py` 442 |
| **v0 total** | **~7,000-11,000 Lean + ~2,000-3,000 Python** | between the SV lane (8,166) and the Python lane (23,306) — correct, because C's semantics is bigger than SV M0's and v0 builds NO proof layer |

**Build poles** (five, each independently checkable — the discipline
that keeps a lane from being one unreviewable commit):

1. Extractor + `docs/c-envelope-schema.md` + the profile document. **No
   Lean.** Green = deterministic double-run on the corpus, and the
   `Unsupported` path exercised.
2. `Ast` + ingester + `#guard` round-trip on the corpus envelope. **No
   semantics.**
3. The memory model + its WF lemmas. **No interpreter.**
4. The interpreter + the libc slice + the two batch dialects.
5. The battery.

### 8.2 The first three milestones

**M0 — close the square's existing edge under the pinned oracle. Zero
Lean.** `tools/ctwin/difftest.py` drives `sunfish.py` under pypy3 via
`pyref.py`; re-run it under CPython 3.9.19 so A ≡ C is stated against the
SAME oracle the Python tier pins. This is the cheapest possible first
result in the whole lane and it either holds or it finds something
today. It also settles, before any Lean exists, whether the square is
even square.

**M1 — the pure leaves, with the raise channel armed.** `--c-batch` over
the scalar-argument functions — `pyfloordiv`, `pymod`, `iabs`, `imax`,
`isup`, `islo`, `mix64`, `move_eq`, `parse_sq`, `set_knob` — against the
compiled oracle built with `-fsanitize=undefined -fno-sanitize-recover=all`
(and ASan verified on the build box, §5.2). This proves the arithmetic
tier, the conversion lattice, and the raise channel BEFORE any
memory-model work exists to confound them. And `pyfloordiv`/`pymod` are
the exact site the ctwin README names as the #1 silent-divergence class,
so M1 is also the square's first cross-language datum: compare them
against Lean-Python's `//` and `%` on the same inputs.

**M2 — `gen_moves` order.** One position in, the full pseudo-legal move
list out, in order. That single call exercises the function-pointer
callback (19 indirect sites), the `Pos` struct, the 120-char board, the
macros, the static tables, and the `indet` byte rule — the whole v0
memory model on one entry point. The comparison already exists:
`difftest.py` compares `gen_moves()` order at each test position and one
ply below, so the row format does not have to be invented.

The capstone after those is `bound()` node-identity — B ≡ A on
`(depth, gamma, score, move, cumulative nodes)`, then B ≡ D.

---

## 9 Prior art — what we adopt, what we deliberately simplify

**CompCert** (Leroy et al., a verified C compiler in Coq). *Adopt*: the
block-and-offset memory model — a pointer is `(block, offset)`, never an
integer — and the discipline of making the memory model a small,
separately-stated interface (`alloc`/`free`/`load`/`store`) that the
semantics is a client of rather than entangled with. §2's `Mem` is that
interface. *Simplify*: CompCert's C→Clight pass pulls side effects out
of expressions, which dissolves the evaluation-order problem by
TRANSFORMATION. We cannot: our envelope must be the program the oracle
compiles, so a normalizing rewrite would insert a transformation between
model and oracle and quietly move the claim (§3.2). And CompCert's
product is a compiler-correctness proof for programs whose UB it may
ASSUME AWAY; ours is an interpreter that must DETECT UB — the harder
direction, as the bridge memo already recorded. CompCert's model is also
untyped bytes plus permissions, with no effective types, so strict
aliasing lies outside it; we add effective types because our refusal
boundary needs them.

**CH2O** (Robbert Krebbers, a formal C11 semantics in Coq). *Adopt*: the
insight that a faithful C memory model is TYPE-STRUCTURED — objects are
shaped by their types, so padding, effective types, and the
indeterminate/poison byte are first-class rather than bolted on. This is
the closest existing thing to §2, and the `CByte` lattice is its idea.
*Simplify*: CH2O formalizes evaluation-order non-determinism faithfully,
with an interleaving small-step relation and a proof that sequence-point
violations are undefined. We take the canonical-order-plus-census route
because our interpreter must be a total function (§3.2), and we accept
the incompleteness that buys.

**Cerberus** (Sewell, Memarian et al., an executable C semantics and the
provenance study). *Adopt*: provenance as a first-class component of a
pointer VALUE — the discovery that de-facto C pointer semantics cannot
be stated without it — and the treatment of what integer↔pointer casts
do to it. *Simplify*: Cerberus EXPLORES the space of allowed behaviors;
its product is the SET, and that is the right product for a
spec-elaboration tool. Ours is the one behavior or a refusal. We also
take the weakest useful provenance rule for v0 — integer→pointer
round-trips REFUSE outright — so the PNVI-versus-PVI question does not
have to be answered before the first corpus runs. Measured: 0 such casts
in the corpus, so the deferral costs nothing today.

**KCC / the K framework C semantics** (Ellison and Roşu). *Adopt*: the
existence proof that an EXECUTABLE definitional semantics of C is
feasible at full-language scale, and — more to the point — that its
highest-value product is UNDEFINEDNESS DETECTION on real programs rather
than a proof about a compiler. That is this lane's thesis, and KCC is the
evidence it is not novel. Also adopt its discipline of a large NEGATIVE
test suite: programs that must refuse are as much of a battery as
programs that must agree, which is why the `Examples/c/*_lab` set in
§7.1 is one lab per hard RULE rather than one per feature. *Simplify*:
K's rewriting engine gives execution for free from the rules; in Lean we
pay for executability with structural recursion and fuel (the
`#py_check` kernel-reducibility covenant), so our rules must compose into
a total function rather than a rewrite relation. And KCC targets C11; we
target C23 in the model's TYPE and C23-minus-rungs in the
implementation.

**What none of them is, and what this therefore is not**: none of these
projects has a DIFFERENTIAL ORACLE as its primary instrument. CompCert
has a proof, CH2O has a proof, Cerberus has an exploration, KCC has a
test suite. This lane's distinguishing instrument is the pinned oracle
plus the battery — and, uniquely, §5.4's square, which no single-language
project can build at all.

---

## 10 Open questions for the owner

1. **Does the C tier get `LeanModels/C/` and a `leanmodels-c-run`
   executable?** That touches `lakefile.toml` and `LeanModels.lean` —
   the two files AGENTS.md explicitly fences off from lane work, and the
   two the SV lane's integration checklist still has open for the same
   reason. Either the C lane is imported from `LeanModels.lean` (so it
   is in `lake build` and therefore in CI, like the SV lane now is), or
   it is typechecked out-of-band and integrated later. This memo assumes
   the former and flags it as a deliberate, coordinator-gated edit
   rather than a side effect.
2. **Is the 2026-08-07 scope decision — "no sunfish deliverable
   attached" — amended by the existence of a classic C sunfish?** The
   entry conditioned itself on exactly that (*"unless a classic C
   sunfish ever exists (none is planned)"*), and one now does. This memo
   argues yes and gives the reason (a transcription with an enforced
   fidelity gate is a semantics corpus, not a second engine), but the
   amendment is the owner's.
3. **Which host is the pinned oracle?** The profile is per-host and the
   answer changes the profile document: this laptop's Apple clang 17
   makes `char` SIGNED and does not define `__STDC_IEC_60559_BFP__`;
   a Linux AArch64 box would flip the first. The profile must be pinned
   before the extractor is written, because it is an INPUT to the AST
   (§4.3) and not a stamp on the side of it.
