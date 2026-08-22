# SoftFloat: FOUNDING CHARTER — the family's shared IEEE 754 component

**Status: the workstream's founding document.** `docs/family-architecture.md`
§3.5 commissions this component, prices it (§3.5.5) and binds it to one
requirement — **width-parametricity, in three clauses**. This charter is its
census, its design, and its first inch.

**Census first (§5.4), and the census moved the plan twice.** Every number
below was measured today against the pin `leanprover/lean4:v4.33.0-rc1`, by
running Lean, not by reading it. Two of the findings contradict documents this
charter was told to build on, and one of them contradicts **the method this
lane started with** — see §0.

**It is NOT a language tier.** There is no `Format` frontend, no envelope, no
oracle and no corpus of its own. Its corpus is *the other tiers' needs*, which
is why §2 is a consumer census rather than a suite census, and why §5.5's
clause manifest is keyed to IEEE 754-2019 rather than to a language edition.

**Dependency posture (§3.2 item 4): this component depends on NO package.** It
imports `Init.Data.Float.Model` and nothing else. Mathlib is a repository
dependency; it is not this component's.

---

## 0 THREE FINDINGS THAT CHANGE WHAT THE COMMISSION SAID

### 0.1 `#guard` IS NOT A KERNEL ORACLE, and the commission's gating instruction cannot work

§3.5.1 instructs this lane to *"gate the reduction behaviour with `#guard`s the
way every other tier gates its primitives."* **A `#guard` cannot detect a
reduction failure.** Core's own docstring, `Init/Guard.lean`:

> Note: this uses the untrusted evaluator, so `#guard` passing is *not* a proof
> that the expression equals `true`.

and `Lean/Elab/Tactic/Guard.lean`'s `evalGuardCmd` calls `unsafe evalExpr`. The
untrusted evaluator honours `@[extern]`, so it calls the C runtime — and it
succeeds **identically** whether the declaration reduces in the kernel or is
`opaque` with no body at all.

**Measured here, twice, before the docstring was found** — which is why it is
reported as a measurement rather than as a quotation:

| proposition | `#guard` | `rfl` | `decide` |
| --- | --- | --- | --- |
| `Nat.sqrt 49 = 7` | **passes** | fails | fails |
| `pack b16 (sqrt b16 (u 49)) = pack b16 (u 7)` | **passes** | fails | fails |
| `(2.75 : Float).toInt64 = 2` | **passes** | fails | fails |

Three rows where the untrusted evaluator says yes and the kernel cannot.

**The consequence for this component, and for every tier that gates a float
row.** A reduction gate is `rfl` or `decide`, never `#guard`. What the *pair*
is good for is a **differential**: `#guard` attests the compiled C runtime,
`rfl`/`decide` attest core's logical model, and a row carrying both has checked
the two against each other — which is a genuinely useful thing this component
can offer, and it is what `LeanModels/SoftFloat/Theorems.lean`'s consumer rows
now do. It is not what the commission asked for, and it is better.

**This correction is owed to the ES lane too**, whose `docs/backlog/es.md`
2026-08-22-es-3 frames the finding as *"`#guard` is a weaker oracle than
`rfl`"*, and whose `harness/es/float_probe.lean` describes `#guard` as kernel
evaluation. The direction is right; the degree is larger than stated. Roughly
fifty float-touching `#guard` rows under `Examples/es/` are attested by the
host FPU, not by Lean.

### 0.2 CORE SHIPS THREE THEOREMS, AND SAYS IT WILL NEVER SHIP MORE

`Init/Data/Float/Model/Unpacked/Pack/Lemmas.lean` is the entire lemma
inventory — `unpackMantissa_packComponents`, `unpackExponent_packComponents`,
`valid_pack` — and the file's own header says:

> These are only the lemmas required to write down the operations on
> `Float.Model` and `Float32.Model`. There will not be any additional lemmas;
> see the docstring of `UnpackedFloat` for more details.

That docstring goes further, and it is the strongest possible corroboration of
§3.5's premise — **core has already commissioned this component, in its own
words**:

> This type exists solely for the purpose of supporting `Float.Model` and
> `Float32.Model`. It is not a goal of this development to serve as the basis
> for a general-purpose floating-point library or to have any direct lemmas
> written about it at all. Rather, users interested in a library about
> floating-point numbers should develop such a library **completely
> separately**, and users interested in proving properties of their programs
> involving `Float` should prove that the operations defined here are
> **equivalent** to the operations defined in the separate library and then
> **transfer** lemmas from the library to the `Float` and `Float32` types.

**This names a THIRD deliverable the commission does not have: the
equivalence-and-transfer layer.** §3.5.1's two layers are *executable bit ops*
and *the spec algebra*. Core's instruction adds *the bridge from our library
back to `Float`/`Float32`*, which is where the packed boundary's
non-parametricity (§3.5.1 clause 3) has to be paid — once per width, because
`Float.Model` and `Float32.Model` are per-width duplicates. It is scheduled as
layer 3 in §3.

The practical consequence for planning is blunter: **no proof in this component
gets help from core.** Every arithmetic lemma is from scratch, over someone
else's algorithm, with a three-lemma standing library.

### 0.3 THE NaN RESIDUE HAS NOTHING TO RANGE OVER

§3.5.4 routes NaN payload and sign to **∀-resolution** — *"the payload is a
parameter, quantified at theorem level"* — and names WebAssembly the exemplar
because its specification enumerates the admissible NaN result patterns.

**Core's `UnpackedFloat` cannot express a NaN payload or a NaN sign.** The
constructor takes no arguments (`Unpacked/Basic.lean`: *"There is no payload
attached to a NaN in this format"*), `Format.Valid` *requires* every NaN bit
pattern to be the canonical one, and `Float.ofBits` canonicalizes its input.
So the ∀-parameter §3.5.4 describes has no domain inside the type §3.5.1 clause
(3) says to build on.

The two instructions are individually correct and jointly unsatisfiable. This
is a **named decision**, §7 item 1 — not something to absorb quietly, which is
exactly what clause (3)'s *"flag it, do not absorb it"* forbids.

---

## 1 THE CORE CENSUS — measured at the pin

`Init/Data/Float/` is **27 files, 2 918 lines**. Reproduced by `wc -l`;
independently reproduced by the consumer census.

**State the numbers were taken in (§5.4a):** toolchain
`leanprover/lean4:v4.33.0-rc1`; probes `harness/softfloat/probe_{reduces,walls,widths}.lean`
run through `tools/check.sh` (case `scratch`, rule 3's exemption with the
warm-clone amendment checked); the axiom prints in §1.4 come from files that
elaborated with **zero errors**, and the wall probe — which is expected to
error — carries **no** axiom print, per §0.1 II(a).

### 1.1 The parametric layer — op by op

`parametric?` = takes `spec : Format` as an argument, or does not need one.
`kernel?` = `rfl` **and** `decide` close a small instance. `extern?` = whether
the *packed* wrapper for this op is `opaque`.

| core declaration | parametric? | kernel? | packed wrapper `opaque`? |
| --- | --- | --- | --- |
| `Format` (`mantissaBitsWithoutImplicit`, `exponentBits`, `numBits`, `exponentBias`, `minExponent`, `targetExponent`) | **yes** — the parameter record | **yes** | — |
| `Format.Valid` | **yes** — indexed by the format | **yes** | — |
| `UnpackedFloat` (4 constructors) | **yes** — format not baked in | **yes** | — |
| `add` / `sub` / `mul` / `div` | **yes** — `spec` is an argument | **yes** | no (`@[extern] def`, has a Lean body) |
| `sqrt` | **yes** | **NO — see §1.2** | no |
| `compare` / `le` / `lt` / `beq` | **yes** (format-free) | **yes** | no |
| `neg` / `abs` | **yes** (format-free) | **yes** | no |
| `isFinite` / `isInf` / `isNaN` | **yes** (format-free) | **yes** | no |
| `round` / `roundWithAccuracy` / `normalize` / `Accuracy` / `ExtendedMantissa` | **yes** | **yes** | — |
| `pack` / `unpack` / `packedNaN` / `packedZero` / `packedInfinity` | **yes** | **yes** | — |
| `ofInt` / `ofNat` / `ofUInt8…64` / `ofUSize` / `ofInt8…64` / `ofISize` | **yes** | **yes** | **signed: YES** (`Int64.toFloat` &c. are `opaque`) |
| `toInt` / `roundToInt` / `toUInt8…64` / `toUSize` / `toInt8…64` / `toISize` | **yes** (format-free) | **yes** | **signed: YES** (`Float.toInt64` &c. are `opaque`) |
| `ofScientific` (decimal PARSE) | **yes** | **yes** | no |
| **decimal PRINT** | — | — | **`Float.toString` is `opaque`; there is no model at all** |
| **`fma`** | — | — | **ABSENT — zero declarations under `Init/Data/Float/`** |
| **rounding modes other than roundTiesToEven** | — | — | **ABSENT** |
| **exception flags (IEEE §7)** | — | — | **ABSENT** — `Operations/Status.lean` is three predicates, not flags |
| **NaN payload / NaN sign** | — | — | **INEXPRESSIBLE** — §0.3 |
| `Float.Model` / `Float32.Model` | **NO** — zero parameters | yes | — |
| `ceil` / `floor` / `round` / `frExp` / `scaleB` / `pow` / transcendentals | — | — | **`opaque`** |

**§3.5.1 clause (3)'s six-row alignment table is CORRECT on all six rows**,
re-verified. The table above extends it from six rows to the whole surface.

**The asymmetry that produced the ES tier's wall is worth naming on its own:**
core's **unsigned** float↔int conversions are `@[extern] def`s with Lean bodies
and reduce; core's **signed** ones, in both directions, are `opaque`
(`Init/Data/SInt/Float.lean`). Nothing about the ES call site looks like it is
choosing between them.

### 1.2 `sqrt` IS THE ONE ARITHMETIC OP THAT DOES NOT REDUCE, and the cause is not floats

`+ − × ÷` all close by `rfl` and by `decide`. `sqrt` closes by neither. The
cause is one level down: `Nat.sqrt` is defined by **well-founded recursion**
(`Init/Data/Nat/Sqrt/Basic.lean`, `Nat.sqrt.iter` with `termination_by guess`),
and well-founded definitions do not unfold in the kernel. Isolated:
`Nat.sqrt 49 = 7` fails `rfl` and fails `decide`.

**This is the mergeSort trap that `docs/completeness.md` §6 predicted** — the
prediction was right about the *family* of the obstacle and wrong about its
*scope*. It costs floats one operation, not the tier. And it lands squarely on
the SV divider flagship, whose RTL module is `divSqrtRecFN` — division **and**
square root in one module. Named as §7 item 3.

### 1.3 THE WIDTH SCALE — binary16 through binary256, with the price

`Format` carries only `0 < mantissaBitsWithoutImplicit` and
`0 < exponentBits`, so every IEEE format is an instance and so are formats IEEE
does not name. Measured, by `rfl` on `pack (div fmt 12 4) = pack fmt 3`:

| format | `mantissa`/`exponent` bits | `rfl` | `maxRecDepth` needed |
| --- | --- | --- | --- |
| a 3-bit toy (`tiny`) | 1 / 1 | yes | default (512) |
| **binary16** — IEEE §3.6, core does not ship it | 10 / 5 | yes | default |
| **binary32** — core ships it | 23 / 8 | yes | default |
| **binary64** — core ships it | 52 / 11 | yes | default |
| **binary128** — IEEE §3.6, core does not ship it | 112 / 15 | yes | **1 000** |
| binary256 — beyond IEEE's named formats | 236 / 19 | yes | **2 000** |

The cost is **linear in the significand width**, and the mechanism is visible
in the source: `ExtendedMantissa`'s `>>>` is `Nat.repeat shiftRightOne`, so a
shift of *n* is *n* kernel steps. binary128 and binary256 are not blocked —
they need a `maxRecDepth` line, and that is the whole price.

**This is the crossover table's SoftFloat row**
(`docs/lean-structures-census.md`), and it agrees with the census's shape:
rung 1 covers all widths at 6-18 lines; rung 2 works but is priced per width.

### 1.4 RUNG 1 IS MEASURABLY CHEAPER THAN RUNG 2, IN TRUST AS WELL AS COVERAGE

`docs/family-architecture.md` §0.1 II(a) argues rung 1 is preferred for
*informativeness*. In this component it is also **strictly cheaper in axioms**,
which the ladder does not claim and which is worth recording:

| statement | scope | proof | axioms |
| --- | --- | --- | --- |
| `∀ fmt, add fmt NaN x = NaN` | **every format** | `rfl` | `[propext]` |
| `∀ fmt, add fmt (+0) (−0) = +0` | **every format** | `rfl` | `[propext]` |
| `∀ fmt s₁ s₂ m e, div fmt (finite …) (zero s₂) = infinity (s₁/s₂)` | **every format** | `rfl` | **none at all** |
| `pack b16 (add b16 1 2) = pack b16 3` | binary16 only | `rfl` | `[propext, Quot.sound]` |

The parametric statement covers infinitely many formats and asks the kernel to
believe *less*. Rung 1 is not a preference here; it is the cheaper option on
both axes.

### 1.5 EVERY LAYER-1 FUNCTION IS TOTAL AND NON-RECURSIVE — the termination finding

Recorded because the founding checklist asks for the fuel/termination decision
*before* the code. Across the whole parametric layer there is **no fuel
parameter, no `partial`, and exactly one well-founded definition** — `Nat.sqrt`,
reached from `sqrtCore`. Everything else is a composition of total `Int`/`Nat`
operations: `Nat.log2`, shifts, division, `Nat.repeat` over a computed count.

**That is the structural reason the component is kernel-computable at all**, and
it is why layer 2 inherits the property (§3.4).

---

## 2 THE CONSUMER CENSUS — op × tier × needed-when

Measured by reading every tier's charter, design doc, backlog and Lean.
Legend: **BLOCKING** = a live refusal in landed code · **live (L1)** = already
used and satisfied by core layer 1 · **inch N** = scheduled at a named rung ·
**—** = the tier's own documents do not ask.

| capability | ES | SV | C | Wasm | Python | Go | Ada |
| --- | --- | --- | --- | --- | --- | --- | --- |
| add / sub / mul | live (L1) | R1-exit | R4, oracle-gated | M2+ (101× `f64.add`) | — | — | deferred |
| **div** | live (L1) | **FLAGSHIP, R1-exit** | R4 | M2+ (51× `f64.div`) | grammar row, refused today | — | deferred |
| **sqrt** | — | **R1-exit, same RTL module** | R4 | M2+ (19× `f32.sqrt`) | — | — | deferred |
| fma | — | — | plan step 4 | absent from the suite vocab | — | — | — |
| six comparisons | live (L1) | R1-exit | design says v0; **model refuses** | M2+ | — | — | deferred |
| int → float | live (L1) | R1-exit | R4; refused today, 13 corpus sites | M2+ | — | — | deferred |
| **float → int truncation** | **BLOCKING** | R1-exit | R4 | M2+ | — | — | deferred |
| format ↔ format | not needed (one number type) | via `recFN` recoding | R4 | **M2+, and core's is `opaque`** | — | — | — |
| decimal parse | partial, refuses outside the integer fragment | — | plan step 3 | 16 250× `f32.const` | — | — | — |
| **decimal print (shortest round-trip)** | **BLOCKING** | — | **plan step 3 — 21% of c-testsuite's format specs** | pattern-compared | grammar row | — | — |
| NaN payload / sign | not needed (one NaN) | — | — | **THE EXEMPLAR — and core cannot express it (§0.3)** | — | — | — |
| exception flags | — | — | Annex F territory, no profile slot exists | — | — | — | — |
| rounding-mode selection | — | — | routed to the profile; **no such slot exists** | — | — | — | — |

### 2.1 ES is blocking on ONE thing, and this lane UNBLOCKED it — run, not admired

`docs/backlog/es.md` 2026-08-22-es-3 says the exact-integer arm of
`numberToString` (ECMA-262 §6.1.6.1.20) is not `rfl`-provable because it goes
through `Float.toInt64`, and that

> the obstruction is an extern primitive with **no kernel-reducible substitute
> short of the bit-level model**

The bit-level model is in core, is kernel-reducible, and is one structure
projection away. `Float.toInt64` is `opaque` — core's own docstring says *"This
function does not reduce in the kernel"* — but `Float.Model.toInt64` is a plain
`def` over `UnpackedFloat.toInt64`, and `Float.toModel` is a projection.

**Replicated and RUN** (`harness/softfloat/probe_es_unblock.lean`, core imports only, the ES
function copied verbatim from `LeanModels/Es/Convert.lean`):

| row | `#guard` | `rfl` | `decide` |
| --- | --- | --- | --- |
| `numberToString 42.0 = some "42"` — **as landed** | passes | **fails** | **fails** |
| `numberToStringViaModel 42.0 = some "42"` | passes | **passes** | **passes** |
| the same at `7.0`, `-7.0`, `1000.0` | passes | **passes** | — |
| `NaN` / `±Infinity` / `±0` arms | passes | **passes** | — |
| the `%` site (`Convert.lean:303`) | passes | — | **passes** |
| `numberToStringViaModel 2.5 = none` (still refused) | passes | **passes** | — |

The change is two expressions: `n.toInt64` → `n.toModel.toInt64`, and
`t.toFloat` → `Float.ofModel (Float.Model.ofInt64 t)`. Axiom print from a
zero-error elaboration: `[propext, Classical.choice, Quot.sound]`.

**That moves the whole exact-integer arm from `#guard` strength — which §0.1
shows is the C runtime, not Lean — to kernel strength.** It is the ES lane's
edit to make; this lane owes them the measurement, not the commit.

**What stays blocked for ES:** `Number::toString` for non-integers, i.e.
correctly-rounded shortest-round-trip decimal printing. `Float.toString` is
`opaque` and core has no decimal printer in the model. That is plan step 3 and
it is this component's largest single item.

### 2.2 The SV flagship needs div AND sqrt, and the doc's `real` row is uncorroborated

The flagship is Berkeley HardFloat's **`divSqrtRecFN`** — one RTL module
computing both. Two obstacles the SV lane already recorded and neither is
this component's: the **`recFN` recoding** at the module boundary (the theorem
must compose through it, and *"a sloppy statement would prove the wrong thing"*),
and that HardFloat is **Verilog, not SystemVerilog**. The circuit side is
`LeanModels/Sv/` and specifically the parametric `sv-0.2` layer — §3.5.2's
warning that `LeanModels/Circuit/` is the analog lane is confirmed, and the
trap is real: `docs/circuit-spec-surface.md` has a section headed *"Exact
divider"* about a **resistive voltage divider**.

**Correction to §3.5.3:** its SV row reads *"`real`, and the divider
flagship"*. **No SV document asks for `real`**, and `LeanModels/Sv/` contains
zero `Float`, zero `real`, zero `shortreal`. The SV need is the divider.

### 2.3 C: the oracle half is genuinely gated; the model half is what this unblocks

`__STDC_IEC_60559_BFP__` is **null on both profiled hosts** — neither claims
Annex F — so the R4 rung's gate stands, and it is the *oracle's* gate. What
this component unblocks is the model half.

**And the size of that slice depends on which unit you count, so both are
given.** The C tier's census (`docs/c-semantics-design.md` §6) records float
conversions as **21% of c-testsuite's format specs and 10% of Fujitsu's** — but
its own table counts TESTS, and there the float slice is **2 of 61**
printf-family tests for c-testsuite and **19 of 261** for Fujitsu. Both are
true and they price plan step 3 very differently. **The test-level number is
the actionable one for this component**: correctly-rounded decimal printing
unblocks 21 tests across the two corpora, not a fifth of them.

**A model/doc divergence found while censusing, and it is a blocker not a
footnote.** `docs/c-semantics-design.md` §1.3 says *"v0 admits `double` values,
assignment and comparison"* and that ctwin's one float operation
(`deadline != 0.0`) *"is exact rather than scoped away"*. The model does not do
this: `LeanModels/C/C23/Expr.lean` refuses **every** float literal and every
`IntegralToFloating`, pinned by `Examples/c/sunfish/expr.lean`. The described
v0 is not the landed v0. Flagged to the C lane, §7 item 5.

### 2.4 Three rows of §3.5.3 are architecture-lane inferences, not tier statements

Recorded so the commission's consumer table is not read as measured demand:

* **Go** — *"same component, no new work"*. `docs/go-charter.md` contains
  **zero** occurrences of `float`; so do the Go backlog and all three Go census
  JSONs. `LeanModels/Go/` does not exist.
* **SV `real`** — §2.2.
* **Ada** — `docs/ada-semantics-design.md` defers floats citing *"the charter's
  R4 gate"*. **`docs/ada-charter.md` has no R4 and no `float`**; R4 is the *C*
  charter's rung. Ada has inherited a C gate by mis-citation, and **Annex G is
  mentioned nowhere in the repository** — case-sensitively; a case-insensitive
  search hits `annex gap` in `docs/backlog.md`, which is §5.4a's name-collision
  trap and not a citation.

### 2.5 The "stale in three places" claim is stale in ONE place

§3.5.5 names `docs/completeness.md` §6, `docs/c-semantics-design.md` §1.3 and
`docs/c23-goal.md` §5.3. Verified:

* **`docs/completeness.md` §6 — STILL STALE.** It defers floats on a
  **Lean-side** premise (*"Lean's `Float` is not kernel-reducible… the same
  family as the mergeSort trap"*), and that premise is false at the pin. It is
  the Python campaign's file; flagged, not edited (§7 item 6).
* The two C documents defer on `__STDC_IEC_60559_BFP__` alone. They are
  **oracle-side only** and have no Lean premise to correct.

§3.5's own later sentence — *"correct only about their oracle-side halves"* —
is the accurate one; its opening framing is not.

---

## 3 LAYER 2 — THE DESIGN

### 3.1 Three layers, not two

| layer | what | who builds it | status |
| --- | --- | --- | --- |
| **1 — executable bit ops** | `Format`, `UnpackedFloat`, `round`, the operations | **core Lean**, free at the pin | censused, §1 |
| **2 — the SPEC ALGEBRA** | the exact-rational model, `round`, `op_correct` over a general `Format` | **this component** | inch 1 landed, §4 |
| **3 — EQUIVALENCE AND TRANSFER** | our library ↔ `Float.Model`/`Float32.Model`, so lemmas reach `Float` | **this component** | §0.2; scheduled |

Layer 3 is core's own instruction (§0.2) and the commission does not have it.
It is also where the packed boundary's non-parametricity gets paid, **once per
width**, because `Float.Model` and `Float32.Model` are per-width duplicates.

### 3.2 The obligation shape

```
-- (illustrative — the obligation shape, not a tree declaration)
op_correct (fmt : Format) (mode : RoundingMode) :
    op fmt x y  =  roundQ fmt mode (exact_op (valQ x) (valQ y))
```

Downstream proofs target **round-of-exact** and never our bit algorithm. An SV
divider proof says *"these output bits are the correctly-rounded quotient"*, not
*"these output bits equal what `UnpackedFloat.div` computes"* — the second is a
tautology about an implementation.

### 3.3 `Q` — the exact value, and why ℝ never appears

Every finite float's value is **dyadic**: `± m · 2^e`. Sums, differences and
products of dyadics are dyadic; quotients are **rational**; and `√` is decided
by comparing squares rather than by extracting a root. So the whole algebra
lives in `Int`, and the number system is a rational:

```lean
-- LeanModels/SoftFloat/Basic.lean (excerpt)
structure Q where
  num : Int
  den : Nat
  den_pos : 0 < den
```

Deliberately **not normalized** — comparison is cross-multiplication, which
keeps every operation in `Int` and never calls `gcd`. `Q.div` returns
`Option Q`, because a zero divisor has no exact quotient: IEEE §7.3 routes that
through the special-value table and the `divideByZero` exception. A sentinel
there would be the silent degrade the family forbids; the `Option` is the same
discipline `valQ` uses for NaN and the infinities, which IEEE §3.2 says do not
denote a real number.

### 3.4 FUEL AND TERMINATION — decided, and the answer is none

**No fuel parameter, no well-founded recursion, no `partial`.** Every layer-2
function is a composition of total `Int`/`Nat` operations. Rounding a rational
to a format is `Nat.log2`, a shift and a division — it does not *search*, so
there is nothing for fuel to bound.

This is a decision with a consequence, not a convenience: it is what makes
layer 2 **kernel-reducible**, which is what lets the instance corollaries close
by `decide` (§0.1 II(a) rung 2). A layer-2 written with a search would have
forfeited rung 2 for the entire component.

The one place the property could be lost is `√`, and §1.2 shows core already
lost it there. **Layer 2's `√` obligation is stated by comparing squares** —
`y = round(√q)` iff the neighbours' squares bracket `q` — which stays in `Int`
and stays reducible. That is not a workaround; it is IEEE's own characterization.

### 3.5 Rounding modes — all five from the first commit

IEEE 754-2019 §4.3 names five rounding-direction attributes. **Core implements
one** (`Accuracy.roundToNearestEven`). Layer 2 carries all five
(`RoundingMode`), for the same reason the format is a parameter: *a spec that
names one mode has hard-coded the default exactly the way a spec that names one
width hard-codes binary64.* Where core cannot serve a mode, the component
**flags it** — §3.5.1 clause (3)'s "flag, do not absorb" — rather than defining
the mode away.

### 3.6 Exceptions — a payload, never silent

IEEE §7's five exceptions (`invalid`, `divideByZero`, `overflow`, `underflow`,
`inexact`) are carried as a **verdict-class payload** (§5.2), not raised. A tier
that does not model flags must be able to ignore them without the model
pretending they did not occur. **No tier in the family has asked for flags
yet** — recorded, so that this is understood as design headroom rather than
demand.

### 3.7 NaN — the decision this lane cannot take alone

§0.3. Two options, both real, and Thomas's call:

* **(a) Extend the type.** Layer 2 defines its own `UnpackedFloat'` carrying a
  NaN sign and payload, and layer 3's transfer collapses it to core's canonical
  NaN. Serves Wasm's NaN result *patterns* — **3 325 `nan:canonical` and
  3 409 `nan:arithmetic` at wg-3.0** (`docs/wasm-charter.md` §2.4; the counts
  are per suite version and are **0** at wg-1.0, which used two dedicated
  assertion forms instead) — and the **103** float→int `reinterpret` sites
  (`i32.reinterpret_f32` 52 + `i64.reinterpret_f64` 51, from
  `docs/wasm-suite-census.json`'s `core_flat_keyword_vocab`; 133 counting both
  directions) that need bit-exact round-trip. Costs a second representation.
* **(b) Scope the claim.** Layer 2 states everything over core's payload-free
  NaN, and Wasm's NaN-pattern rows are **REFUSED by name** rather than served.
  Cheap and honest, and it means the family's stated NaN exemplar is a gap.

**(a) is this lane's recommendation**, because the family's own doctrine (§0.1
I) says the definition is never weakened for convenience, and (b) narrows the
definition to what the dependency happens to express.

---

## 4 INCH 1 — WHAT LANDED

`LeanModels/SoftFloat/{Basic,Theorems}.lean`, **12 theorems, zero `sorry`, zero
`native_decide`, zero `bv_decide`**, no package dependency.

**The split is the founding-checklist law** (`docs/statement-cookbook.md` §6):
`Basic.lean` is the spec half and mentions no interpreter — it recompiles
unchanged under a definition swap. `Theorems.lean` is the only file that names
core's operations.

**The deliverable theorem, and it is the ES row:**

```lean
-- LeanModels/SoftFloat/Theorems.lean (excerpt)
theorem toInt_eq_truncate {lo hi : Int} {x : UnpackedFloat} {q : Q}
    (h : valQ x = some q) : UnpackedFloat.toInt lo hi x = q.truncate := by
```

Core's float→int conversion **is** truncation-toward-zero of the exact value
(IEEE §5.8 `convertToIntegerTowardZero`), for every float that has an exact
value. NaN and the infinities are excluded **by the hypothesis**, not by a side
condition — which is what makes it the specification's statement rather than the
algorithm's. It mentions **no `Format` at all**, because truncation does not
depend on one: §3.5.1 clause (2) is satisfied *a fortiori*, not narrowly.

Its working lemma is the one genuine piece of arithmetic:
`em_shift_mantissa`, that `ExtendedMantissa`'s `>>>` is division by a power of
two, by induction on the shift count — the fact §1.3's width scale is about.

**The IEEE special-value rows, each over a general `Format`** (§6.2, §6.3, §7.2,
§7.3, §5.11): NaN propagation through `add`; `(+0) + (−0) = +0`; zero-sign
preservation; `(+∞) + (−∞) = NaN`; `0/0 = NaN`; `x/0 = ±∞`; NaN unordered;
`+0 = −0`; `√` of a negative is NaN. These are the rows ES already pinned three
ways, now stated once for every format instead of once for binary64.

**Axiom prints — from a zero-error elaboration** (§0.1 II(a)):

```
em_shift_mantissa          [propext]
roundToInt_eq_truncate     [propext, Quot.sound]
toInt_eq_truncate          [propext, Quot.sound]
add_nan_left               [propext]
add_zero_opposite_signs    [propext]
add_zero_same_sign         [propext]
add_inf_opposite           [propext]
div_zero_zero              does not depend on any axioms
div_by_zero                does not depend on any axioms
compare_nan                [propext]
compare_zeros              [propext]
sqrt_neg                   does not depend on any axioms
```

**Instantiated on real consumer rows, run and not admired:** the ES truncation
rows at `2.75` and `-2.75` through `.toModel`, carrying **both** oracles; the
SV divider's `1/8` row at binary32 and binary16, `decide`-closed at binary16;
and the instance corollaries of `add_nan_left` at binary16 / binary32 /
binary64 / binary128 — three of which core does not ship as formats.

### 4.1 What inch 1 did NOT do, stated as obligations

* **`op_correct` for `+ − × ÷`** — the round-of-exact bridge. Inch 2. It needs
  the `roundQ` interpreter and a real proof about core's `normalize` /
  `roundWithAccuracy`, with **no help from core** (§0.2).
* **`roundQ` itself** — the computable correctly-rounded rounding of a `Q` to a
  `Format` under a `RoundingMode`, and its declarative characterization
  `IsCorrectlyRounded`, proved equivalent. The spec/interpreter split one level
  down.
* **Layer 3** — equivalence and transfer to `Float`/`Float32`.
* Decimal printing (plan step 3), `fma` (step 4), transcendentals (step 5).

---

## 5 COVERAGE BY CLAUSE

The manifest is keyed to **IEEE 754-2019**, not to a language edition, and it is
this component's §5.5 artifact. Claimed today:

| clause | title | status | declarations |
| --- | --- | --- | --- |
| §3.3 | Sets of floating-point data | stated | `Format`, `Q`, `valQ` |
| §3.6 | Extended and extendable precisions | stated | `binary16`/`binary128` as instances |
| §4.3 | Rounding-direction attributes | **stated (spec), refused (impl)** | `RoundingMode`; core serves 1 of 5 |
| §5.8 | Details of conversions to integer | **stated + proved** | `toInt_eq_truncate` |
| §5.11 | Details of comparison predicates | stated | `compare_nan`, `compare_zeros` |
| §6.2 | Operations with NaNs | **partial** | `add_nan_left`; payload INEXPRESSIBLE (§0.3) |
| §6.3 | The sign bit | stated | `add_zero_opposite_signs`, `add_zero_same_sign` |
| §7.2 | Invalid operation | stated | `add_inf_opposite`, `div_zero_zero`, `sqrt_neg` |
| §7.3 | Division by zero | stated | `div_by_zero`, `Q.div : Option Q` |
| §7.4-7.6 | Overflow / underflow / inexact | **refused — no consumer** | `Exception` type only |
| §5.4.1 | Arithmetic operations | **OWED** | inch 2 |
| §5.12 | Conversions to/from decimal | **OWED** | plan step 3 |

Cite-and-paraphrase throughout; no IEEE text is vendored.

---

## 6 THE LANE'S OWN RULES

1. **Width-parametric or it does not land.** Every theorem over a general
   `Format`, or over none. Width-specific results only as instance corollaries
   or `decide`-closed base cases.
2. **Never over `Float`/`Float32`.** The moment a statement mentions them it has
   silently hard-coded binary64 (§3.5.1 clause 3).
3. **A reduction gate is `rfl` or `decide`, never `#guard`** (§0.1).
4. **Both oracles on a consumer row**, because together they are a differential
   between core's model and the host FPU.
5. **Flag, never absorb.** Where core forces a fixed width, one mode, or a
   payload-free NaN, record the declaration and the widths it cannot serve.
6. **ℝ never appears** below the transcendentals.
7. **Axiom prints only from zero-error elaborations.**

---

## 7 WHAT THOMAS HAS TO ANSWER

1. **NaN payloads (§0.3, §3.7).** Extend the type, or scope the claim and refuse
   Wasm's NaN rows by name? This lane recommends extending.
2. **Layer 3's priority (§0.2).** Core says build separately and transfer. Does
   the transfer layer come before `op_correct` for `+ − × ÷`, or after?
3. **`sqrt` (§1.2).** Core's `sqrt` is not kernel-reducible because `Nat.sqrt`
   is well-founded. Layer 2 can state `√` by comparing squares and stay
   reducible — but the SV flagship's module is `divSqrtRecFN` and needs both.
   Is a reducible `√` in scope for this component, or does the SV proof compose
   through core's irreducible one?
4. **Exceptions and rounding modes (§3.5, §3.6).** No tier has asked. Build the
   headroom now, or wait for a consumer?
5. **The C model/doc divergence (§2.3)** — the C lane's to fix; flagged here.
6. **`docs/completeness.md` §6 (§2.5)** — the Python campaign's file; the
   Lean-side premise is false at the pin.

---

## 8 WHAT LANDED WITH THIS CHARTER

* This document, and `docs/backlog/softfloat.md`.
* `LeanModels/SoftFloat/{Basic,Theorems}.lean` + `LeanModels/SoftFloat.lean` —
  12 theorems, zero `sorry`, no package dependency.
* The core census (§1), run against the pin at four widths plus two beyond IEEE.
* The consumer census (§2), across seven tiers.
* **The ES unblock, measured** (§2.1) — the ES lane's edit to make.
* Three corrections to the commission (§0) and five to other documents (§2.2,
  §2.3, §2.4 ×3, §2.5).
