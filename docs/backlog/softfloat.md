# The SoftFloat lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the SoftFloat lane.** Ids are `YYYY-MM-DD-softfloat-<n>`.

SoftFloat is **shared component #2** (`docs/family-architecture.md` §3.5), not
a language tier: no frontend, no envelope, no oracle, no corpus of its own. Its
charter is `docs/softfloat-charter.md`.

---

## 2026-08-22-softfloat-1 — M1: the two censuses, the layer-2 design, and inch 1

`docs/softfloat-charter.md` + `LeanModels/SoftFloat/{Basic,Theorems}.lean` +
`LeanModels/SoftFloat.lean` — **12 theorems, zero `sorry`, zero `native_decide`,
zero `bv_decide`, no package dependency.** State: pin
`leanprover/lean4:v4.33.0-rc1`; every quoted axiom line from a zero-error
elaboration; probes under `harness/softfloat/probe_*.lean`, run through `tools/check.sh` (case `scratch`).

### THE COMMISSION'S OWN GATING INSTRUCTION CANNOT WORK — `#guard` is not a kernel oracle

§3.5.1 says to *"gate the reduction behaviour with `#guard`s"*. `#guard` runs
`unsafe evalExpr` — core says so in `Init/Guard.lean` (*"this uses the untrusted
evaluator, so `#guard` passing is not a proof"*) — so it honours `@[extern]`,
calls the C runtime, and **passes identically whether a declaration reduces or
is `opaque` with no body**.

Measured here **before** the docstring was found, which is why it is a
measurement and not a quotation. Three propositions where `#guard` says yes and
the kernel cannot: `Nat.sqrt 49 = 7`; `pack b16 (sqrt b16 49) = pack b16 7`;
`(2.75 : Float).toInt64 = 2`. All three fail `rfl` **and** `decide`.

**The rule, and it is now the lane's:** a reduction gate is `rfl` or `decide`.
What the pair is good for is a **differential** — `#guard` attests the compiled
C runtime, `rfl`/`decide` attest core's logical model — and a row carrying both
has checked the two against each other. Every consumer row in
`Theorems.lean` carries both.

**Owed to the ES lane:** `docs/backlog/es.md` 2026-08-22-es-3 frames this as
*"`#guard` is a weaker oracle than `rfl`"* and `harness/es/float_probe.lean`
describes `#guard` as kernel evaluation. Direction right, degree understated:
~50 float-touching `#guard` rows under `Examples/es/` are attested by the host
FPU, not by Lean.

### THE ES BLOCKER IS UNBLOCKED, AND THE UNBLOCK WAS RUN

`docs/backlog/es.md` 2026-08-22-es-3 says the exact-integer arm of
`numberToString` has *"no kernel-reducible substitute short of the bit-level
model"*. **The bit-level model is in core, is kernel-reducible, and is one
structure projection away.** `Float.toInt64` is `opaque` — core's docstring says
*"This function does not reduce in the kernel"* — but `Float.Model.toInt64` is a
plain `def` over `UnpackedFloat.toInt64`, and `Float.toModel` is a projection.

Replicated verbatim from `LeanModels/Es/Convert.lean` into a core-only scratch
file and run both ways:

| row | `#guard` | `rfl` | `decide` |
| --- | --- | --- | --- |
| `numberToString 42.0 = some "42"` (the body landed **at the time**) | passes | **fails** | **fails** |
| `numberToStringViaModel 42.0 = some "42"` | passes | **passes** | **passes** |
| `7.0`, `-7.0`, `1000.0` | passes | **passes** | — |
| NaN / ±Infinity / ±0 arms | passes | **passes** | — |
| the `%` site (then `Convert.lean:303`; now `:315-324` and **withdrawn**) | passes | — | **passes** |
| `2.5 ⇒ none` (still refused) | passes | **passes** | — |

Two expressions change: `n.toInt64` → `n.toModel.toInt64`, `t.toFloat` →
`Float.ofModel (Float.Model.ofInt64 t)`. **It is the ES lane's edit to make;
this lane owes them the measurement, not the commit.**

> **SINCE LANDED (annotation, not a rewrite).** The ES lane committed the
> routing in `9dab312`, about six minutes after this entry was written, so
> `Convert.lean:224-238` is now the routed body and the row above describes
> history. The measurement stands as taken; only its tense was wrong. The
> probes carried the same staleness in a worse form — see
> `2026-08-23-softfloat-11`.

Still blocked for ES:
non-integer `Number::toString`, i.e. shortest-round-trip decimal printing —
`Float.toString` is `opaque` and core has no decimal printer at all. That is
plan step 3.

### CORE SHIPS THREE THEOREMS AND SAYS IT WILL NEVER SHIP MORE — and it commissions us in its own words

`Unpacked/Pack/Lemmas.lean` is the whole lemma inventory (three packing
lemmas). Its header: *"There will not be any additional lemmas."* And
`UnpackedFloat`'s docstring instructs downstream users to build a library
**completely separately** and then prove core's operations **equivalent** to it
and **transfer** lemmas back to `Float`/`Float32`.

**That is a THIRD layer the commission does not have** — equivalence and
transfer — and it is where the packed boundary's non-parametricity gets paid,
once per width. Practical consequence: no proof in this component gets help
from core.

### THE NaN RESIDUE HAS NOTHING TO RANGE OVER

§3.5.4 routes NaN payload to ∀-resolution; §3.5.1 clause (3) says build over
`UnpackedFloat`. **`UnpackedFloat.notANumber` takes no arguments**
(*"There is no payload attached to a NaN in this format"*), `Format.Valid`
requires the canonical NaN, and `Float.ofBits` canonicalizes. The two
instructions are individually correct and jointly unsatisfiable. Wasm — the
doc's own exemplar — needs **3 325 `nan:canonical` / 3 409 `nan:arithmetic`
result patterns at wg-3.0** (`docs/wasm-charter.md` §2.4; **0** at wg-1.0, which
spelled the same nondeterminism as two dedicated assertion forms — so the number
carries its suite version) and **103** float→int bit-exact `reinterpret` sites
(`docs/wasm-suite-census.json`). **Named decision, charter §7 item 1;
this lane recommends extending the type.**

### `sqrt` IS THE ONE ARITHMETIC OP THAT DOES NOT REDUCE, AND FLOATS ARE NOT THE CAUSE

`+ − × ÷` all close by `rfl` and `decide`. `sqrt` closes by neither, because
`Nat.sqrt` is **well-founded** (`Nat.sqrt.iter`, `termination_by guess`).
Isolated: `Nat.sqrt 49 = 7` fails both. `docs/completeness.md` §6's mergeSort-trap
prediction was right about the *family* and wrong about the *scope* — it costs
one operation, not the tier. It lands on the SV flagship, whose RTL module is
`divSqrtRecFN` (division **and** square root).

### THE WIDTH SCALE IS REAL TO binary256, AND THE PRICE IS `maxRecDepth`

`rfl` on `pack (div fmt 12 4) = pack fmt 3`: `tiny`(1/1), binary16, binary32,
binary64 at the default 512; **binary128 at 1 000; binary256 at 2 000**. Cost is
linear in the significand width — `ExtendedMantissa`'s `>>>` is
`Nat.repeat shiftRightOne`, so a shift of *n* is *n* kernel steps. Nothing is
blocked; three of the six widths are formats core does not ship.

### RUNG 1 IS CHEAPER THAN RUNG 2 IN AXIOMS, WHICH THE LADDER DOES NOT CLAIM

| statement | scope | axioms |
| --- | --- | --- |
| `∀ fmt, add fmt NaN x = NaN` | every format | `[propext]` |
| `∀ fmt s₁ s₂ m e, div fmt (finite …) (zero s₂) = infinity (s₁/s₂)` | every format | **none at all** |
| `pack b16 (add b16 1 2) = pack b16 3` | binary16 only | `[propext, Quot.sound]` |

The parametric statement covers infinitely many formats **and** asks the kernel
to believe less. §0.1 II(a) argues rung 1 on informativeness; in this component
it wins on trust too.

### INCH 1's DELIVERABLE

```lean
-- LeanModels/SoftFloat/Theorems.lean (excerpt)
theorem toInt_eq_truncate {lo hi : Int} {x : UnpackedFloat} {q : Q}
    (h : valQ x = some q) : UnpackedFloat.toInt lo hi x = q.truncate := by
```

Core's float→int conversion **is** truncation-toward-zero of the exact value
(IEEE §5.8). NaN and the infinities are excluded **by the hypothesis**, not by a
side condition — the specification's statement, not the algorithm's. It mentions
no `Format`, because truncation does not depend on one: clause (2) satisfied *a
fortiori*. Plus nine IEEE special-value rows (§6.2, §6.3, §7.2, §7.3, §5.11),
each **over a general `Format`**, and instance corollaries at four widths.

**Fuel/termination, decided before the code:** none. Every layer-2 function is a
composition of total `Int`/`Nat` operations; rounding a rational to a format
does not search. That is what keeps the component kernel-reducible, which is
what lets rung 2 close the base cases at all.

### FIVE CORRECTIONS TO OTHER DOCUMENTS, FLAGGED NOT EDITED

* **§3.5.3's SV row** names `real`. No SV document asks for it; `LeanModels/Sv/`
  has zero `Float`/`real`/`shortreal`. The need is the divider.
* **§3.5.3's Go row** (*"same component, no new work"*). `docs/go-charter.md`
  has **zero** occurrences of `float`; nor do the Go backlog or its three census
  JSONs. `LeanModels/Go/` does not exist.
* **`docs/ada-semantics-design.md`** defers floats citing *"the charter's R4
  gate"*. `docs/ada-charter.md` has no R4 and no `float` — R4 is the **C**
  charter's rung. Annex G appears nowhere in the repository (case-sensitively;
  the case-insensitive search hits `annex gap` in `docs/backlog.md` — §5.4a's
  name-collision trap).
* **`docs/c-semantics-design.md` §1.3** says v0 admits `double` values,
  assignment and comparison. `LeanModels/C/C23/Expr.lean` refuses **every**
  float literal and every `IntegralToFloating`. Model and doc diverge; that is a
  blocker for the C lane, not a footnote.
* **§3.5.5's "stale in three places"** is stale in **one**:
  `docs/completeness.md` §6 still defers floats on the false Lean-side premise.
  The two C documents are oracle-side only and have nothing to correct.

### NEXT — ORDERED AS RULED

1. **Layer 3, the TRANSFER layer, FIRST.** Core commissioned it in its own
   words, and its price is now measured rather than feared:
   `harness/softfloat/probe_transfer.lean` (zero errors) shows every packed
   operation is **definitionally** `pack ∘ (the parametric op at its format) ∘
   unpack`, so a parametric theorem transfers in **one line — and the same line
   at both widths**, reaching `Float` itself with one more. **So layer 3 is a
   TACTIC, not a body of lemmas**: the per-width cost is a mechanical `show`
   that names the format, and it should be generated. That is the difference
   between paying §3.5.1 clause (3)'s price once and paying it on every theorem
   forever. Boundary: it cannot reach the `opaque` declarations at all —
   consumers route through `.toModel` (which is the ES unblock as a general
   rule).
2. **`roundQ` + `IsCorrectlyRounded`** — the computable correctly-rounded
   rounding of a `Q` to a `Format` under a `RoundingMode`, with its declarative
   characterization proved equivalent. The spec/interpreter split one level down.
3. **`op_correct` for `+ − × ÷`** — the round-of-exact bridge, from scratch,
   with no help from core.
4. **The flag layer** — `inexact` is read off the same `Accuracy` datum (2)
   consumes; the other four off the special-value rows already proved.
5. **Decimal printing** (plan step 3) — the largest single item, and what
   unblocks ES's `Number::toString` and, on the C side, **21 printf-family tests**
   (2 of 61 c-testsuite + 19 of 261 sampled Fujitsu). The C tier's headline
   "21% of format specs / 10% of Fujitsu's" counts SPECS; its own table counts
   TESTS. Both are in `docs/c-semantics-design.md` §6; they price this step
   very differently and the test-level number is the actionable one.

### THE BUILD STATE OF THIS LANDING (§5.4a, A14) — SAY WHAT THE GREEN COVERS

**What was RUN, and it covers every Lean claim in the charter.** All five
probes and a faithful simulation of the two-module split were elaborated
through `tools/check.sh`, case `scratch` — §7.1 rule 3's exemption, with the
warm-clone amendment CHECKED by the script rather than assumed, under
`nice -n 19` and needing no lock. Zero errors on `probe_reduces`,
`probe_widths`, `probe_es_unblock_axioms` and the split simulation; exactly
nine expected errors on `probe_walls`, which is the wall map and is pinned as
a gate. Every axiom line quoted in the charter comes from one of the
zero-error files.

**What is OWED: the full `lake build`.** `tools/triad.sh --lane softfloat
--classify` reads this landing as **spine** (it touches `LeanModels.lean`),
so the triad is a full-tree build — and A14 makes those quiet-machine-only.
At landing time the machine was **load 3.6 but 6.1 GB of swap in use**, and
the FIFO queue was **nine lanes deep** with another lane's tenure past
thirty-five minutes. The ticket is enqueued and the wrapper is detached; it
runs when the queue reaches it.

**Therefore, precisely: the green this landing carries is that every module
and probe elaborates against the pinned toolchain. It is NOT yet a claim that
the whole default target set still builds with `import LeanModels.SoftFloat`
added to `LeanModels.lean`.** That integration risk is small — these two
modules import `Init.Data.Float.Model` and nothing else, so there is no name
they can collide with outside their own namespace — but small is not zero and
it is not measured yet. **The full triad stays owed** and is discharged by the
queued tenure.

### THE `Core/` TRIGGER, NAMED SO IT IS NOT A JUDGEMENT CALL

SoftFloat lives at `LeanModels/SoftFloat/`, **not** `LeanModels/Core/`, and that
is §3.8's own rule rather than a preference: a thing moves into `Core` when a
**second consumer** exists, and SoftFloat has **zero** in-tree consumers today
(ES is blocked, SV is dormant). **The trigger is the second tier that imports
`LeanModels.SoftFloat`.** ES importing it for the truncation family would be the
first; SV's divider the likely second.

### A CONVENTION CHOICE, NAMED RATHER THAN MADE SILENTLY

The five doc corrections above were filed **into their owners' backlog files**
on the coordinator's routing (`docs/backlog/{c,sv,go,ada,python-completeness}.md`,
plus one to `es.md`). Those files each say *"appended only by the <lane> lane"*,
and a survey found **no precedent** for a cross-lane append anywhere in
`docs/backlog/`.

So the entries are shaped to honour what that rule protects — id collisions and
a lane losing control of its own record — while still reaching the owner:
each is headed **INBOUND FROM THE SOFTFLOAT LANE**, carries an id in the
**SoftFloat** namespace so nothing is minted in the owner's sequence, and says
in its own first lines that the owner should renumber it or close it.

**If §9.5 means the stricter thing, this is the wrong shape and these six
entries are the ones to fix.** Naming it here is cheaper than discovering it in
an audit.

### TWO PROCESS FINDINGS FROM FILING THEM, both recorded because they cost something

**1. THE CROSS-LANE APPEND RE-INTRODUCED THE EXACT RACE §9.5 RETIRED.** Per-lane
backlog files exist because *"at ~66 landings a day every lane appends to the
same tail"*. Appending to six other lanes' files put this lane back in six tails
at once, and it collided immediately: rebasing onto a master that had moved 24
commits produced a conflict in `docs/backlog/es.md` — the ES lane had appended
while this lane was writing. **The per-lane rule is not bureaucratic; it is the
merge strategy**, and a cross-lane filing convention has to carry the cost the
rule was avoiding. `docs/backlog/INDEX.md` conflicted too, but that one is free:
it is GENERATED, so the resolution is `tools/backlog-index.sh`, never a hand
merge (§5.5).

**2. THE ROUTING BEAT THE FILE, AND THE FILE ARRIVED 90% REDUNDANT.** By the
time this lane's `es.md` entry landed, the ES lane had already published
`2026-08-22-es-4` accepting **both** findings — re-measured independently on
their own expression, retracting their own three-times-repeated phrase, and
**sharpening the second past what was reported** by separating *detecting* a
non-integer (now provable) from *rendering* one (still blocked). The agent-to-
agent routing carried the finding faster than the durable file did.

So the entry was cut down to the one thing their landing does not carry — **the
clamp**: core's `toInt` clamps, ECMA-262's `ToInt32`/`ToUint32` reduce modulo
2³², and the projection that unblocked `toString` is wrong for `ToInt32` in the
quiet way, passing every in-range test. **The lesson for cross-lane filing:
check what the owner has already landed before filing, and file the residue,
not the report.**

**2a. THE CLAMP WARNING WAS NOT PREVENTIVE — IT FOUND A LIVE BUG.** The residue
this lane filed to ES (core's `toInt` clamps; ECMA-262's `ToInt32`/`ToUint32`
reduce modulo 2³²) was written as a warning about a conversion that tier **has
not built yet**. The ES lane audited **both** `toInt64` sites rather than the
reported one, and found the second was already wrong: `applyBinary`'s `%` was

    | "%" => return .num (a - b * (a / b).toInt64.toFloat)

and `Float.toInt64` clamps, so a large quotient **silently produced a wrong
remainder that every in-range test would have passed** (`2026-08-23-es-1`).
`%` is now REFUSED pending the exact-value route. Their audit also confirmed
the good half: `numberToString`'s site is guarded by `n.abs < 1e15`, far inside
`Int64`, so the clamp cannot fire there — *"the distinction the warning draws is
exactly the distinction the guard makes"*.

**So the lesson from finding 2 inverts.** There the routing beat the file and
the report arrived redundant; here the same reduced entry — *the residue, not
the report* — was the part that carried a defect nobody had looked for. **Filing
the residue is not a courtesy to the owner, it is where the value was.** The
`es.md` INBOUND entry has since been dropped entirely: fully absorbed, acted on,
and its conflict on rebase was the third collision of the same tail race.

**3. A SLOPPY LIVENESS CHECK, caught by looking twice.** This lane's pre-rebase
"is a build running in my clone" probe was a `pgrep | while read | grep -c`
pipeline that returned **2** when the true answer was **0** — the one live
`lake` was another lane's, in another clone. It failed toward caution, which is
the safe direction, but §7.1 rule 5's warning is that a broken liveness check
*"does not fall back to caution, it falls forward into reclaiming a lock
somebody is holding"*. The fix is the one the rule already states: print the
processes and read them, rather than counting them.

---

## 2026-08-23-softfloat-8 — LAYER 3 LANDED, and it is a CLASS, not a tactic

`LeanModels/SoftFloat/Transfer.lean`. **The priced first item, and the price
came in lower than the estimate because the estimate was the wrong shape.**

### THE ESTIMATE WAS "A TACTIC". THE ANSWER IS A CLASS, AND IT IS STRICTLY BETTER

`2026-08-22-softfloat-1` measured that every packed operation is definitionally
`pack ∘ (the parametric op at its format) ∘ unpack`, so a transfer costs one
mechanical `show` per (theorem, width), and concluded: **generate it** — a macro
emitting the packed corollary per width.

A bake-off (`harness/softfloat/probe_transfer_class.lean`) put that against a
`Packed α` class over the wrapper type. **The class wins outright**, and the
difference is not ergonomic, it is what the theorem SAYS:

| | macro / simp set | `Packed` class |
| --- | --- | --- |
| statements per IEEE row | **2** (one per width) | **1** |
| new widths (`binary16`, `binary128` wrappers) | 1 more per row, forever | **an instance; inherits everything** |
| what the reader sees | two theorems that must be kept in step | one theorem |

**This is §3.5.1 clause (1)'s own move applied one level up.** The clause says
`binary32`/`binary64` are instances of a general `Format`, never separate
definitions. The class says the same of the **wrappers**. Clause (3) observes
that core's parametricity **stops** at the packed boundary — it does, and this
file is the finding that **ours does not have to stop there too.**

Landed: `packed_add_nan`, `packed_add_zeros`, `packed_add_inf_opposite`,
`packed_div_zero_zero`, `packed_div_by_zero`, `packed_sqrt_neg`,
`packed_compare_nan`, `packed_toInt64_eq_clamped_truncate` — **eight rows, one
statement each, both widths**. Axioms `[propext]` throughout, or
`[propext, Quot.sound]` where `toInt_eq_truncate` is used.

### THE ACID TEST, because a class is easily a BARRIER instead of a VIEW

If the class's `pack`/`unpack` stop being definitionally the real ones, `rfl`
stops closing at the instances and the abstraction buys nothing. Measured:
`packed_stays_definitional` and `packed32_stays_definitional` both close by
**`rfl`** through the class. It is a view.

### AND THE BAKE-OFF REPRODUCED §0.1 II(a)'s LYING AXIOM PRINT, LIVE

The class's first version omitted `[Add α]`, so `HAdd α α ?m` could not be
synthesized and the class fields failed to elaborate. `#print axioms
packed_add_nan` then printed **`does not depend on any axioms`** — the cleanest
line the command can emit — about a theorem whose **statement had never
elaborated**. Twelve errors in the file, and the axiom line read like a
triumph. The doctrine's most dangerous failure mode, reproduced in this lane
rather than quoted from the family document.

### THE ES DELIVERY: THE CLAMP IS NOW IN A CONCLUSION, NOT A COMMENT

`packed_toInt64_eq_clamped_truncate` states the packed conversion as
`Int64.ofIntClamp q.truncate` — **the clamp is in the statement**, deliberately.

The ES lane's `%` bug (`2026-08-23-es-1`) happened because the clamp was
invisible at the call site. A warning in prose prevented the next one; a
theorem whose conclusion names `Int64.ofIntClamp` prevents it **in the goal
state**, where a modular conversion (ECMA-262 §7.1.6 `ToInt32`, mod 2³²) cannot
silently unify with it. `toInt_eq_truncate` remains stated over the **exact
value** and is the handle for the modular route — which is now the ES lane's
`OWED` item, and it has the theorem it needs.

### NEXT, unchanged in order

`roundQ` + `IsCorrectlyRounded` and the mode layer (§3.5), then `op_correct`
for `+ − × ÷`, then the flag layer, then decimal printing.

---

## 2026-08-23-softfloat-9 — THE CONSUMER-SITE CENSUS: zero unrouted crossings remain, and the instrument corrected itself twice

`harness/softfloat_consumer_census.py` → `docs/softfloat-consumer-census.json`.
The §5.4 instrument contract: `--compare` mode, every refusal path RUN (12
self-test rows, no Lean needed), double-run byte-identical, and the toolchain
**pin stamped**, because *which declarations are opaque is a fact about the pin*
and therefore an INPUT to the result.

### THE OPAQUE SET IS DERIVED, NEVER HARDCODED

Whether `Float.toInt64` reduces is a property of the toolchain, not of this
lane's memory. The instrument parses the toolchain's own float sources and
classifies each declaration `opaque` / `def` / `extern-def`. Measured at
`leanprover/lean4:v4.33.0-rc1`: **42 opaque, 31 reducible.** A toolchain bump
moves the census by itself instead of silently invalidating a hardcoded list.

### THE ANSWER: ZERO UNROUTED CROSSINGS

**0 qualified crossings; 13 dot-notation candidates, and every one resolves to
a non-crossing:**

| site | resolves to |
| --- | --- |
| `LeanModels/Es/Convert.lean:236` `.toInt64` | **already routed** — it reads `n.toModel.toInt64`, this lane's unblock, applied |
| `LeanModels/Es/Convert.lean:238`, `:252` `.toString` | `ToString.toString` on an **`Int64`/`BigInt`**, not `Float.toString` |
| 10 sites in `LeanModels/SoftFloat/{Theorems,Transfer}.lean` | this component's own deliberate `.toModel` routing |

So **the transfer layer has no unrouted consumer waiting on it.** ES's residual
need is not a crossing at all: non-integer `Number::toString` is a **REFUSE with
a named cause** (`Convert.lean:249` — *"needs correctly-rounded decimal
conversion (SoftFloat step 3)"*), and `%` is refused after the clamp bug. The
tier is honest about the gap rather than crossing the boundary quietly, which
is the outcome the transfer layer was supposed to produce.

**Consequence for the plan: decimal printing (step 3) is now the ONLY thing any
tier is blocked on.** The mode layer, `roundQ` and `op_correct` are headroom,
not unblocking.

### THE INSTRUMENT CORRECTED ITSELF TWICE, and both errors flattered

This is §5.4a pointed at the instrument rather than at the tree, and the census
is only trustworthy on its third pass.

| pass | matcher | result | why it was wrong |
| --- | --- | --- | --- |
| 1 | bare member name | "26 crossings, **319** prose hits" | `round`, `exp`, `log`, `pow`, `toString` are ENGLISH WORDS and other types' members |
| 2 | qualified + dot-notation | "0 qualified, **170** candidates" | the analog lane's `.exp`/`.log` are **Mathlib's `Real.exp`/`Real.log`**, not floats at all |
| 3 | + sound narrowing | "0 qualified, **13** candidates" | a file with no `Float` token in code cannot contain a Float crossing |

**Both errors ran in the flattering direction — a bigger consumer list, which
is a bigger mandate for this lane.** Pass 1 over-reported by ~24×. The fix that
mattered was not a cleverer regex but a **sound narrowing**: dropping files that
never name `Float` cannot drop a Float call site, so it costs no recall.

**And the residue is stated rather than hidden:** a regex cannot resolve a
receiver's type, so `dotted`/`anonymous` rows are reported as **CANDIDATES** and
are never merged into the qualified count. The final resolution of all 13 was
done by reading them, and it is recorded above rather than asserted by the tool.

**The law this pays into**, and it is the master-branch commit `f48f9db`'s own
title: *count the pattern position, never the identifier.*

---

## 2026-08-23-softfloat-10 — STEP 3 SCOPED: the consumer census found a SECOND consumer, and the algorithm choice follows from the SPEC's own wording

`harness/softfloat/probe_decimal.lean` (zero errors; both theorems `rfl` with
**no axioms at all**). Design only — no tree module yet.

### THE CONSUMER CENSUS, and the answer to "is there a second?" is YES

Asked to confirm ES's `Number::toString` REFUSE row is the only named consumer.
**It is the only PRINTING consumer. There is a second, in the inverse
direction.**

| # | site | direction | served today? |
| --- | --- | --- | --- |
| 1 | `LeanModels/Es/Convert.lean:251` — `Number::toString` REFUSE, naming *"correctly-rounded decimal conversion (SoftFloat step 3)"* | float → decimal (**print**) | **NO — core ships no printer at all**; `Float.toString` is `opaque` |
| 2 | `LeanModels/Es/Convert.lean:168` — `StringToNumber` REFUSE, *"outside the decimal-integer fragment (the StringNumericLiteral grammar is a rung)"* | decimal → float (**parse**) | **PARTLY** — core's `UnpackedFloat.ofScientific` is width-parametric and kernel-reducible (censused reducible) |
| — | `LeanModels/Es/Eval.lean:72` — BigInt literal outside the decimal fragment | decimal → **BigInt** | not ours: no float involved |
| — | `Examples/es/convert/guards.lean:82` | the gate row for #1 | — |

**No other tier names a decimal need.** So step 3 is two half-inches, not one,
and they are asymmetric: **printing is greenfield, parsing already has a core
primitive to state a theorem about.** Parsing is therefore the cheaper one and
should probably go first — `ofScientific_correct` is an `op_correct` in the
existing shape, whereas printing needs a new algorithm.

### THE ALGORITHM: DRAGON4-STYLE EXACT, and the reason is the SPEC's wording

**Not Ryū, not Grisu.** Those are *speed* designs: they use precomputed power
tables and fixed-point approximations, with a slow fallback for the cases the
approximation cannot decide. Their correctness arguments are **error bounds on
an approximation** — "this fast path agrees with the exact answer whenever the
bound holds". We would then owe ES two theorems: the fast path matches the
exact algorithm, and the exact algorithm matches the spec. **ES only wants the
second one.**

ECMA-262 §6.1.6.1.20 does not describe an algorithm at all. It says: let `n`,
`k`, `s` be integers such that `k ≥ 1`, `10^(k-1) ≤ s < 10^k`,
`s × 10^(n-k)` is the Number value, **and `k` is as small as possible**. That
is an **existential over integers with a minimality side condition** — which is
*literally what an exact big-integer search computes*. So the exact algorithm's
correctness theorem **is the spec clause**, with no approximation layer to
excuse.

The family's own reasons stack on top:

* **ℝ never appears** (charter §3.5.1). Exact big-integer arithmetic keeps the
  whole thing in `Nat`/`Int`; Ryū's tables would be a large data blob whose own
  correctness is a separate obligation.
* **Kernel-reducible** (§3.4), so instance rows close by `decide`.
* **Width-parametric**: the interval is computed from `(mantissa, exponent)` and
  `fmt.targetExponent`, so binary16/32/64/128 are instances, as everywhere else.

### THE CORRECTNESS STATEMENT ES NEEDS, in the family's output-determined form

```
-- (illustrative — the obligation shape, not a tree declaration)
toDecimal_shortest (fmt : Format) (x : UnpackedFloat) (d : Decimal) :
    toDecimal fmt x = some d →
      roundTrips fmt x d ∧ ∀ d', d'.digits < d.digits → ¬ roundTrips fmt x d'
```

*What it emits round-trips, and nothing shorter does.* The second conjunct is
ECMA-262's *"k is as small as possible"*, and it is the half a fast algorithm
cannot give you without its own error analysis. The answer is bound in the
RESULT, never taken as an input (`docs/statement-cookbook.md` §7).

**This is the statement that kills the `"1.000000"` bug by construction** — the
one the ES lane names at `Convert.lean:207` as the reason they refuse rather
than delegate to the host: *"handing back the host's `Float.toString` would emit
`1.000000` where the spec says `1` — a silent wrong answer."* A theorem with
the minimality conjunct cannot be satisfied by a printer that pads.

### TERMINATION: FUEL, AND IT IS THE FIRST TIME THIS COMPONENT NEEDS IT

Layer 2's fuel answer was **none** — nothing searched. Shortest-round-trip
printing **searches**: it tries digit counts until one round-trips. So it needs
well-founded recursion or fuel, and **well-founded recursion is exactly what
cost this component `sqrt`** (§1.2: `Nat.sqrt`'s `termination_by` is why `sqrt`
closes under neither `rfl` nor `decide`). Measured in the probe: the fuelled
loop closes by **`rfl` and by `decide`**, with **no axioms**, and fuel
exhaustion answers `none` — loud, never a wrong digit count.

### ONE THING FLAGGED BEFORE THE CODE EXISTS

`/` on `Int` is a **convention choice**: `Int.ediv`, `Int.tdiv` and `Int.fdiv`
disagree on negatives, and the nearest-decimal step divides. The probe's sample
is positive, where all three agree. **The implementation must pin the convention
and say which** — a printer that picks one silently is the same shape of defect
as an unstated rounding mode.

---

## 2026-08-23-softfloat-11 — THE PROBES WENT STALE IN SIX MINUTES, and correcting the text is not the fix

Audit row, `docs/quality-audit-2026-08-23.md` "## softfloat", **HIGH**. Verified
against the current tree before acting, not taken on the note's word.

### THE DEFECT: THE PROBE PRESENTED THE LANDED VERSION AS THE UNPROVEN ALTERNATIVE

`harness/softfloat/probe_es_unblock.lean` transcribed ES's `numberToString` and
labelled the transcription *"`LeanModels/Es/Convert.lean:219-226` as landed"*.
That was true when written. **The ES lane committed the routing (`9dab312`)
about six minutes later**, so the landed body became the routed one — and the
probe went on calling the PRE-unblock body "as landed", with its two
expected-FAIL rows sitting under the heading *"The landed version"*.

**Anyone running the probe would have concluded the unblock was unlanded** — the
exact opposite of what this lane had just measured, in a file whose whole
purpose was to demonstrate it. The same staleness sat in
`probe_es_unblock_axioms.lean`, and a second row cited `Convert.lean:303` for
the `%` site, which had moved to `:315-324` **and been withdrawn**.

### FIXED, AND THE HALVES ARE NOW NAMED FOR WHAT THEY ARE

`numberStringPreUnblock` (history, the subject of the failure rows) and
`numberStringLanded` (mirrors `Convert.lean:224-238`). Sections retitled so the
landed half is the routed one; the `%` row re-cited to `:315-324` and retitled
*"the shape the WITHDRAWN `%` arm would need"*, with an explicit line saying it
does **not** claim the arm is landed. The probes are now a **regression gate on
the landed shape** rather than a proposal about it. Charter §2.1's table and its
*"the ES lane's edit to make"* line are corrected the same way.

The dated entry `2026-08-22-softfloat-1` is **annotated, not rewritten**: the
measurement was correct as taken and only its tense was wrong, and a backlog
entry is a record of a moment.

### THE STRUCTURAL FIX, because correcting prose does not stop the next one

> **A transcription of another lane's file is A COPY WITH A TIMESTAMP, and it
> rots the moment they commit.**

Six minutes is the measured half-life here, which is short enough that "be
careful" is not a control. So the copy now carries a **tripwire**:
`harness/softfloat_consumer_census.py --check-transcriptions` asserts that every
text this lane's probes assume about another lane's file is *still in that
file* — the routed `n.toModel.toInt64`, the `Float.ofModel (…ofInt64 t)`
rebuild, and the `%` arm's refusal string. It is in the gate set, so the next
time ES moves that code the probe goes **red instead of quietly lying**.

Its own failure path is exercised in the self-test (13 rows now): a fixture
whose cited text is absent must make the tripwire FIRE, because a check that
has never failed is a design and not a control.

### WHY THIS ONE WAS INVISIBLE TO EVERY GATE THIS LANE HAD

Worth naming, because the gate set looked complete. `probe_es_unblock.lean` is
**expected to error** (two rows), and its sibling is expected to be clean — both
were, throughout. `docs_check` gates marked blocks in `.md`, and this was a
comment in a `.lean`. The census gated *call sites*, not *citations*. **Every
gate was green while the file said the opposite of the truth**, because none of
them was pointed at the claim that had rotted. That is the §5.4a lesson in its
sharpest form: the failure was silent AND flattering, and it took an outside
audit to see it.
