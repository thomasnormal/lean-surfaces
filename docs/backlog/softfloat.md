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

---

## 2026-08-23-softfloat-12 — THE DECIMAL INCH'S CENSUS: 2 sites in tree, and the suite figure is a BOUND

`harness/softfloat_consumer_census.py --decimal-demand`. Census-first, before
any decimal code.

### IN-TREE, EXACT — two refusal sites, one per direction

| site | direction | spec | served by core? |
| --- | --- | --- | --- |
| `LeanModels/Es/Convert.lean:251` | **print** | ECMA-262 §6.1.6.1.20 `Number::toString` | **no** — `Float.toString` is `opaque`; core ships no printer |
| `LeanModels/Es/Convert.lean:168` | **parse** | ECMA-262 §7.1.4.1 `StringNumericLiteral` | **partly** — `UnpackedFloat.ofScientific` is width-parametric and kernel-reducible |

**Reproduced by two independent methods**, which is this repository's standard
for adopting a number: the consumer-site census (call-site scan) and a refusal
grep found the same two sites. `LeanModels/Es/Eval.lean:72` is a BigInt literal
row and involves no float; `Spec.lean:290` is prose.

**The asymmetry is the schedule.** Printing is greenfield; parsing already has a
core primitive to state an `op_correct` about. **Parse is the cheaper half and
should go first.**

### OUT-OF-TREE — a BOUND, labelled as one, and NOT CI-wired

`built-ins/Number` 340 + `built-ins/parseFloat` 54 = **at most 394 of 23 109
built-ins files (1.7%)**. It is an **upper** bound and the mode says so in its
own output: those directories also hold `Number.isInteger`,
`MAX_SAFE_INTEGER` and friends, which need no conversion at all.

**The exact figure is not computable here.** test262 is out of tree — the ES
lane's census pins it at sha `3655e746` and the corpus is not on disk — and
`docs/es262-census.json` carries only aggregate esid counts (`esid_rows` is an
`int`, not a per-clause map), so it cannot be refined from the committed data
either. Per §5.4, a mode whose corpus is out-of-tree is **not wired into CI**: a
gate that is a permanent SKIP is a check pretending.

**1.7% is deliberately a smaller claim than it could have been.** The C tier's
analogous headline is "21% of format specs"; this lane has now twice published a
consumer number that shrank under scrutiny (319 → 170 → 13), both times in the
flattering direction, so the bound is stated as a bound.

### THE INSTRUMENT FAILED LOUDLY FIRST, AND THAT WAS THE DESIGN WORKING

The mode's first run reported **0 in-tree sites** — because it reused
`strip_lean`, which blanks string literals on purpose for the call-site scan,
and **a refusal MESSAGE lives inside a string literal by construction.** It
printed `FAIL … either it was fixed (good) or the marker drifted (bad)` and
exited non-zero rather than reporting `0` as a finding. That is §5.4's *"an
empty census is an instrument fault, never a finding"* firing on its author.

Fixed by matching the RAW source for this mode, with a proximity requirement —
a hit must sit within three lines of a `refuseConstruct` — because the message
and its call are split across lines in the real file, so same-line matching
would have found nothing either.

### WHAT THE INCH MUST COVER, from the census

1. **Parse first** (`ofScientific_correct`): core's primitive already exists, so
   this is an `op_correct` in the shape already built and it retires
   `Convert.lean:168`.
2. **Print second** (the Dragon4-style exact algorithm of
   `2026-08-23-softfloat-10`): greenfield, fuel-shaped, and it retires
   `Convert.lean:251` — the only site in the tree that no other lane can fix.

---

## 2026-08-23-softfloat-13 — PARSE INCH, STATEMENT-FIRST: `ofScientific`'s branches are NOT shape-uniform

`harness/softfloat/probe_ofscientific.lean` (zero errors). Exploratory probe
run **before** writing the theorem, to fix its statement. Two findings, and the
first one changes the subject of the theorem.

### THE THEOREM CANNOT BE ABOUT `ofScientific`'s UNPACKED RESULT

`UnpackedFloat.ofScientific` has three branches: zero, two SAFETY CUTOFFS, and
the computing path. **They do not return the same shape.**

| branch | binary16 example | result |
| --- | --- | --- |
| cutoff, `e > 2 ^ exponentBits` | `1e33` | `.infinity .positive` — **directly**, computing nothing |
| computing path, `e = 2 ^ exponentBits` | `1e32` | **`.finite`** — measured `.isInf = false`, `.isFinite = true` |
| the same, after `pack` | `1e32` | `packedInfinity` |

The reason is structural: `roundWithAccuracy` returns only `.zero` or
`.finite`, **never `.infinity`** — overflow to infinity happens one layer up, in
`pack`. Core states it in `UnpackedFloat`'s own docstring: *"an unpacked float
in canonical form for a given format may not actually be representable in that
format … the `pack` function will overflow the float to infinity."*

> **So `op_correct` for the parse half must be stated AFTER `pack`, or must
> carry a representability hypothesis.** A single statement about the unpacked
> result would be comparing `.infinity` on one branch against an
> unrepresentable `.finite` on another, and it would be false without either
> having been wrong about the arithmetic.

This is precisely why the inch was probed statement-first. The bug it prevents
is not an arithmetic error; it is a theorem that is false for a reason having
nothing to do with what it was meant to say.

### THE KERNEL COST IS VALUE-DEPENDENT, NOT ONLY WIDTH-DEPENDENT

§1.3 measured the width axis (binary16 → binary256, cost linear in the
significand, priced in `maxRecDepth`). The parse probe found the other axis:

* `ofScientific binary64 1 (-1)` — `0.1` — closes by `rfl` at `maxRecDepth 4000`;
* `ofScientific binary64 3 (-1)` — `0.3` — does **not** close at **16000**.

Same width, same operation, same denominator; only the numerator differs. And
`1e32` at binary16 does not close at 16000 either, while `1e33` closes
instantly — because the latter takes the cutoff and computes nothing.

> **An instance row that closes for one literal may not close for its
> neighbour.** So the parse theorem must be **parametric**, and the
> `decide`-closed base cases must be **chosen and measured**, never assumed
> from a nearby row that happened to work. That is the §0.1 II(a) ladder with a
> sharper edge than the width axis gave it.

### WHAT DID CLOSE, and it is the fragment ES parses

Zero at every width and both cutoffs by `rfl`; exactness for `m * 10 ^ e` with
`e ≥ 0` at **binary16, binary32, binary64 and binary128**; and the dyadic
negative exponents (`5e-1 = 1/2`, `125e-3 = 1/8`) that are exact in binary.
`ofsci_zero` — `∀ spec e, ofScientific spec 0 e = .zero .positive`, over a
general `Format` — closes by `rfl`.

### NEXT, and the statement is now fixed

`ofScientific_correct` stated over `pack spec (ofScientific spec m e)`, against
the correctly-rounded value of the exact rational `m * 10 ^ e`. It needs
`roundQ`, which is the same prerequisite the arithmetic `op_correct` family
needs — so the parse half and `roundQ` are one inch, not two.

---

## 2026-08-24-softfloat-14 — THE DECLARATIVE ROUNDING SPEC, and it is the half that stops `op_correct` being a tautology

`LeanModels/SoftFloat/Round.lean`. Zero errors, zero warnings, `check.sh`
verdict **TRUSTWORTHY**; `nearest_of_exact` `[propext]`, `directed_of_exact`
**no axioms at all**.

### WHY DECLARATIVE FIRST, AND NOT THE COMPUTABLE `roundQ`

The obvious next step was a computable `roundQ` so `op_correct` could be stated
as `op fmt x y = roundQ fmt (exact …)`. **That would have been close to
circular**, and charter §3.5.2 says why in advance: a proof must target
round-of-exact and never our bit algorithm, because *"these output bits equal
what `UnpackedFloat.div` computes"* is a tautology about an implementation.
Any correct computable `roundQ` will structurally resemble core's rounding —
they are both the same finite integer computation — so proving core against it
proves little.

**The escape is the split one level down**: predicates that mention **no
algorithm at all**, core's or ours, and say only what §4.3 says. That is what
landed:

* `ReprQ fmt q` — IEEE §3.3: the finite values a format holds, `± m · 2 ^ e`
  with the significand inside `2 ^ mantissaBits` and the exponent at or above
  `minExponent`.
* `IsNearest fmt q y tieOk` — §4.3.1: `y` is representable, **nothing
  representable is strictly closer**, and when something is exactly as close the
  tie rule decides. The tie rule is a **parameter**, which is what distinguishes
  roundTiesToEven from roundTiesToAway instead of hard-coding one.
* `IsDirected fmt q y side` — §4.3.2: representable, on the required side, and
  **nothing representable strictly between**. One shape covers toward-zero,
  toward-positive and toward-negative by instantiating `side`.

`op_correct` will be stated against these. The computable `roundQ` is then
proved to *satisfy* them, and its resemblance to core stops mattering — which
is the whole point of the spec/interpreter split, applied to rounding itself.

### ONE OMISSION STATED RATHER THAN HIDDEN

`ReprQ` carries **no upper bound on the exponent**, so it describes the
format's finite values as though the exponent range were unbounded above.
That is deliberate: overflow is IEEE **§7.4**, a separate clause with a
**mode-dependent** answer (the directed modes give the largest finite magnitude
in one direction and ±∞ in the other — charter §3.5). Folding it in here would
silently redefine "nearest representable" as "nearest representable or ±∞",
which is a different theorem. Named now so §7.4 is designed rather than
discovered.

### NO PACKAGE DEPENDENCY, HELD

The nonnegativity step in `nearest_of_exact` would be one `ring` call. This
component depends on **no package**, so the cancellation is done by hand
(`Int.neg_mul`, `Int.add_right_neg`, `Int.mul_nonneg`). The posture costs three
lines here and is worth keeping: it is what lets this component be a dependency
of tiers that claim core-only.

### §9.0 — WHERE THE `op_correct` FAMILY ACTUALLY STANDS

**1 of 12 proved.** The denominator is the charter's own plan (§3.5.5),
enumerated so the fraction is auditable rather than flattering:

| step | ops | proved |
| --- | --- | --- |
| 1 | `+` `−` `×` `÷` `√` | **0 of 5** |
| 1 | the six comparison predicates (one statement) | 0 of 1 |
| 2 | int→float, **float→int**, format→format | **1 of 3** — `toInt_eq_truncate` |
| 3 | decimal parse, decimal print | 0 of 2 |
| 4 | `fma` | 0 of 1 |

The other **21** landed theorems are real but are **not** `op_correct`: 2
working lemmas, 9 parametric IEEE special-value rows (§6.2, §6.3, §7.2, §7.3,
§5.11), 7 packed transfers of those, 2 acid tests, and 1 packed transfer of the
one `op_correct`. Counting those toward the family would be exactly the
flattering direction this lane has already had to correct twice.

### THE DECIMAL BLOCKER'S STATE

**Both sites live and gated**, re-verified by `--decimal-demand` in every triad
since it was added:

* `Es/Convert.lean:251` — **print**, §6.1.6.1.20. Core ships no printer at all.
  **The only item in the tree no other lane can fix.**
* `Es/Convert.lean:168` — **parse**, §7.1.4.1. Core's `ofScientific` exists and
  is reducible, so this is an `op_correct`, not an algorithm.

Both are blocked on the same prerequisite, and **the parse half and `roundQ`
are one inch** (2026-08-23-softfloat-13). The declarative half of that
prerequisite is now landed; the computable `roundQ` and the equivalence are
what remain before `ofScientific_correct` can be stated at all.

---

## 2026-08-24-softfloat-15 — `roundQ` LANDS AS AN ALGORITHM WITH EVIDENCE, and says so

`LeanModels/SoftFloat/RoundAlg.lean`. Zero errors, zero warnings, verdict
**TRUSTWORTHY**. `zero_repr` and `roundQ_isNearest_zero` `[propext]`;
`roundQ_zero` **no axioms**.

### THE FIRST ARITHMETIC TARGET IS `×`, AND CORE'S CODE DECIDES IT

Not a judgement call. `mul`'s finite branch is **one line** —
`roundWithAccuracy spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) .exact` — the exact
product's significand and exponent handed straight to rounding with `.exact`
accuracy. `add`'s is **five steps**: two `decreaseExponent` calls to align
exponents, a **signed** sum that can be negative or zero, then `normalize`,
which case-splits three ways on the sign and calls `round`, which calls
`roundWithAccuracy` anyway.

> **`mul`'s obligation is a strict sub-problem of `add`'s.** Whatever proves
> `mul` is needed for `add` too; the converse is false. So `×` first.

### WHAT LANDED, AND WHAT IT IS NOT

`roundQ` is computable, **mode-parametric over all five §4.3 attributes**,
returns a `Q` so that `IsNearest fmt q (roundQ fmt mode q)` is directly
statable, and terminates without fuel or well-founded recursion —
`Nat.log2`, a shift, a division, two bounded corrections.

**It is an ALGORITHM WITH EVIDENCE, not a specification, and the file says so
in its own header.** The satisfaction theorems are what would make it one, and
two remain:

* `roundQ_repr` — the output is representable (the corrections exist to make
  this true);
* `roundQ_nearest` — nothing the format holds is strictly closer. This is the
  real content and needs the interleaving argument about representable values
  at differing exponents — the heart of a Flocq-style development.

**They are stated as TEXT, not as `sorry`ed declarations.** A `sorry` would put
`sorryAx` into this file's axiom prints and make every neighbouring theorem's
receipt unreadable (§0.1 II(a)). This lane has already caught two axiom prints
that lied; it will not manufacture a third.

### EVIDENCE IN PLACE OF THE MISSING PROOF, LABELLED AS EVIDENCE

`roundQ` was written independently of core's rounding. At a **3-bit
significand**, where every rounding decision is forced and hand-checkable, the
two are checked to agree on the rounding-sensitive integers **9, 11, 13, 5, 7**
— including the ties — all by `decide`, in the kernel. And the modes are shown
to genuinely differ (9 → ties-to-even **8**, toward-zero **8**, toward-positive
**10**), so the mode parameter is not decoration.

**This is corroboration, not proof**, and it is what justifies carrying `roundQ`
before the satisfaction theorems land.

### §9.0 — UNCHANGED, DELIBERATELY

**`op_correct`: 1 of 12.** Nothing here moves it. `roundQ` is not an
`op_correct`; `roundQ_isNearest_zero` is satisfaction on a single point, not an
operation. The 21 excluded theorems stay excluded, and these three join them —
**24 landed theorems, 1 of which is an `op_correct`.** A numerator that moved
because a supporting file landed would be exactly the flattering direction this
lane has corrected twice already.

**The decimal blocker is unchanged**: `Es/Convert.lean:251` (print) and `:168`
(parse), both live, both gated by `--decimal-demand` in this triad.

---

## 2026-08-24-softfloat-16 — THE DRIFT GUARD FIRED ON ITS OWN AUTHOR, and the fix is a better instrument

Triad8 went **RED** — `[03:02:17] LOCK ACQUIRED` → `BUILD GREEN` →
`[03:03:13] TRIAD DONE (build exit 0, gates RED)`. The failing gate was this
lane's own `--compare`: *"DRIFT against the committed census."* A red triad is
an aborted triad; nothing landed.

### THE DRIFT WAS TWO ROWS, AND NOT THE ONES EXPECTED

The standing hypothesis was that `Basic.lean`'s new `Q.Eq/Le/abs/dist` had
moved consumer sites. **It had not.** Measured, the whole diff is:

```
> dotted  .log2  LeanModels/SoftFloat/RoundAlg.lean:30
> dotted  .log2  LeanModels/SoftFloat/RoundAlg.lean:30
```

13 → 15 candidates. Line 30 is `ilog2Q`:
`(Nat.log2 q.num.natAbs : Int) - (Nat.log2 q.den : Int)` — two `Nat.log2` on
one line. **`Float.log2` is opaque**, so `log2` is in the instrument's member
set, and a properly-qualified `Nat.log2` matched it.

### IT IS THE NAME-COLLISION CLASS AGAIN, IN ITS THIRD DISGUISE

`2026-08-23-softfloat-9` recorded two passes of this: bare English words
(`round`, `exp`, `log`) and Mathlib's `Real.exp`/`Real.log` in the analog lane.
The **sound narrowing** (a file must contain the `Float` token) killed both —
and does **not** kill this one, because `RoundAlg.lean` genuinely contains
`Float` (it opens `Float.Model`). The narrowing's precondition was satisfied
and the candidate was still spurious.

### THE FIX IS A RULE, NOT A REGENERATION

> **An UPPERCASE receiver is a NAMESPACE, not a value.** One that is not a
> float owner is a **definite non-crossing**: `Nat.log2` cannot be
> `Float.log2`. A lowercase receiver is a value whose type a regex cannot
> resolve, and stays a candidate.

Lean's own naming convention is what makes this sound, and the excluded rows
are **listed under `excluded`, not dropped**, so the exclusion is auditable.

**The rule validates itself against work already done by hand.** 15 candidates
→ **8 candidates + 7 excluded**, and the seven are exactly the rows this lane
had previously resolved *manually* in `2026-08-23-softfloat-12`: the two
`ToString.toString` on `Int64`/`BigInt`, the two `Nat.log2`, and
`Float.Model.toInt64` / `Float32.Model.toInt64` / `Packed.toInt64` — the
**reducible** model and this component's own class, none of them opaque
crossings. **The instrument now derives the answer that previously needed a
human read.**

Three self-test rows added (13 → 16), including the exact defect that turned
triad8 red: `Nat.log2` must be excluded, must **not** be a dotted candidate,
and a lowercase receiver must still be one.

### A DRIFT GUARD FIRING ON ITS AUTHOR IS THE GUARD WORKING

Recorded as such. The gate was added in `2026-08-23-softfloat-12` to catch the
census going stale against the tree; the first thing it caught was **this
lane's own edit**, one ticket later. It cost a tenure and bought a better
instrument, which is the trade the gate exists to make.

## 2026-08-24-softfloat-17 — THE TIE RULE IS NOT STATABLE WITHOUT CANONICALITY

`LeanModels/SoftFloat/Round.lean` §2a. Landed at the pre-verified splice point,
between the predicate and its first use.

### "∃ AN EVEN SIGNIFICAND" IS VACUOUS

A `Q` has no canonical significand: the same value has many `(m, e)` pairs and
they differ in the **parity** of `m`. Doubling `m` and decrementing `e` turns
any significand even. Measured — `Q.dyadic 5 0`, `Q.dyadic 10 (-1)` and
`Q.dyadic 20 (-2)` are one value with significands **5 (odd), 10, 20**.

So the obvious instantiation of `IsNearest`'s `tieOk` parameter is **true of
every value, odd ones included**, and a tie clause that is always true silently
permits the wrong answer on every tie.

**`IsNearest`'s tie field was under-specified as shipped: not wrong, but
instantiable wrongly.** The parameter's SHAPE was right; the file simply
carried no canonicality notion to instantiate it with, and the nearest thing to
hand was the vacuous one.

### THE FIX, AND IT IS THE FORMAT'S OWN NORMALIZATION

`IsCanonical fmt m e` — the significand fits, and either the leading bit is set
(normal) or the exponent sits at `minExponent` (subnormal). That is exactly
what core's `targetExponent` computes, and it is a fact about the **format**,
not about the rational. `TieEven` is then stated over it, where each value has
exactly one parity.

Verified: `IsCanonical m3 5 0` **true**; `IsCanonical m3 10 (-1)` and
`IsCanonical m3 20 (-2)` **false** — the even-significand representations of an
odd value are ruled out, which is precisely what the vacuous reading failed to
do. `even_repr_of_odd_is_not_canonical` closes by `decide` with **no axioms**.

### THE FAILURE MODE, NAMED

> **A weaker predicate: easier to satisfy, and it looks fine.**

This is §5.3's family living inside a **spec parameter** rather than a proof.
The parameter's shape was right, the obvious instantiation vacuous, and only a
witness computation caught it — no type error, no failing proof, no red gate
would ever have fired.

### §9.0 — STILL 1/12

`op_correct` unchanged. `IsCanonical`, `TieEven` and the witness are spec
machinery, not operations. **26 landed theorems, 1 of which is an
`op_correct`.**

---

## 2026-08-24-softfloat-18 — THE GUARD FIRED A SECOND TIME, ON MASTER'S EDIT, AND THE RESOLUTION IS CLEAN

After the green at `tree 031c854498c5`, rebasing onto master (25 commits) drifted
the census again — **7 rows, none of them this lane's**, all in
`LeanModels/Es/Ordinary.lean`, a file master gained in those commits.

| rows | site | resolution |
| --- | --- | --- |
| 1 | `:232` `.toInt64` | **the ROUTED form** — `Float.ofModel (Float.Model.ofInt64 n.toModel.toInt64)`. This lane's unblock, applied. Not a crossing. |
| 6 | `:284 :292 :313 :315 :316 :333` `.toFloat` | `Nat.toFloat` on array indices/lengths from `arrayIndex?`. **Not a crossing.** |

**The `.toFloat` resolution was measured, not assumed**, because it is the
actionable claim: `Int8/16/32/64.toFloat`, `ISize.toFloat` and `Float32.toFloat`
ARE opaque, so six `.toFloat` sites in new ES code was a live hazard until the
receiver type was settled. `Nat.toFloat` is an **`abbrev` over `Float.ofNat`**
(`Init/Data/OfScientific.lean:81`), and it **reduces** — `rfl` and `decide` both
close `(3 : Nat).toFloat = 3.0`. So the ES lane's new file crosses nothing.

**This is the census gate doing the job it was built for**, and this time on
another lane's landing rather than its own: it noticed seven new float sites in
a file this lane had never read, within one rebase of their appearing.

### AND A PROCESS DEFECT OF THIS LANE'S OWN, RECORDED

The re-push composed its verification and its push with `;` instead of `&&`:

```
python3 …--compare; fi; git push …        # WRONG: push runs regardless
```

So `--compare` printed **DRIFT** and the push went through anyway, putting a
branch with a stale census in front of the coordinator. Caught immediately and
corrected, but the shape is worth keeping: **a check whose failure does not
stop the next step is not a gate, it is a comment.** The triad wrapper gets
this right — it stops on a red gate — and this lane's own shell did not.
Every verify-then-push chain here is now `&&`.

### §9.0 — STILL 1/12

Unchanged. Nothing in this entry is a theorem.

---

## 2026-08-24-softfloat-19 — `mul_correct` REDUCED TO ONE OBLIGATION, and `roundQ` is not on its path

`LeanModels/SoftFloat/Mul.lean`. `mul_correct_of` and
`mul_eq_roundWithAccuracy` both depend on **no axioms at all**, from a
zero-error elaboration. Statement written first, as directed, and it named
what it needs.

### THE REDUCTION, AND ITS PROOF IS ONE TERM

Stated against `IsNearest` / `TieEven` — never against `roundQ` — so no
implementation appears on either side of the conclusion. The residual
obligation is carried as a **hypothesis**, `RoundWithAccuracyIsNearest`, which
means it is **type-checked rather than described**, and this file carries no
`sorryAx` to poison its neighbours' receipts (§0.1 II(a)).

The proof is a single term application:

```
H fmt (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) qr (Nat.mul_pos h₁ h₂) hr
```

No tactics, no case analysis, no arithmetic beyond `Nat.mul_pos`.

> **Multiplication's entire content beyond the rounding lemma is NOTHING.**

That is the "`mul` is a strict sub-problem of `add`" claim from
`2026-08-24-softfloat-15` **confirmed by measurement** rather than re-asserted:
the sub-problem is empty.

### THE SEQUENCING ASSUMPTION IS REFUTED — `roundQ` IS A PARALLEL ARTIFACT

The standing suspicion was that `mul_correct`'s proof would force `roundQ_repr`
first, making the `Nat.log2` ±1 arithmetic the real inch. **It does not.**

The obligation the statement names is about **core's `roundWithAccuracy`**, not
about this component's `roundQ`. `roundQ` would be needed only to state
`mul = roundQ (exact …)` — which is exactly the circular form §3.5.2 warns
against and which this lane refused to write. So:

* `roundQ_repr` / `roundQ_nearest` are **not** prerequisites for any
  `op_correct`;
* the real next inch is `RoundWithAccuracyIsNearest` — the same mathematical
  content (nearest-ness of a rounding), but about **core's** function;
* `roundQ` remains valuable as an independently-written cross-check (it agrees
  with core by `decide` at a 3-bit significand) and as the eventual
  satisfying implementation, but it is **off the critical path**.

The distinction is not pedantic: it redirects the next inch from proving things
about our own algorithm to proving them about the one the tiers actually run.

### THE §7.4 OMISSION PAID OFF

`mul_correct_of` needs **no overflow hypothesis**. That is `ReprQ`'s
deliberately-missing UPPER exponent bound (`2026-08-24-softfloat-14`) doing its
job: an overflowed result is still `ReprQ`, so the theorem holds
unconditionally on finite inputs. Had overflow been folded into
representability, this statement would have needed a side condition it has no
business carrying — overflow is §7.4, a separate clause with a mode-dependent
answer.

### SV'S ANSWER LANDS: FOUR INFERRED ROWS RETIRE

The SV lane confirms they do **not** want `real`; the true need is the divider
— this component's spec layer over `Rat`, against HardFloat's `divSqrtRecFN`.
So §2.0's SV column narrows to `div` + `sqrt` (one RTL module) plus the `recFN`
recoding, and **four cells that were this lane's own inference from "R1-exit"
are retired**: add/sub/mul, the six comparisons, int→float, float→int
truncation.

The estimate shrinks, which is the right direction: **a consumer table built
from inference over-prices the component**, and SV was four rows of it. The
decimal rows already read `—` for SV and are unchanged.

### §9.0 — STILL 1/12, AND `mul_correct_of` DOES NOT MOVE IT

`mul_correct_of` is **conditional**: it proves multiplication correct *given* an
unproved obligation. A conditional theorem is not a proved `op_correct`, and
counting it would be exactly the flattering direction this lane has corrected
three times. The numerator moves when `RoundWithAccuracyIsNearest` is
discharged — at which point `mul_correct` becomes unconditional in one line,
and `div`, `sqrt` and `add` all draw on the same lemma.

**28 landed theorems, 1 of which is an unconditional `op_correct`.**

---

## 2026-08-24-softfloat-20 — THE BRIDGE LEMMAS: what core's round and sticky bits MEAN

`LeanModels/SoftFloat/Theorems.lean`. `em_shift_round` `[propext]`;
`em_shift_sticky` `[propext, Classical.choice, Quot.sound]`. Verdict
**TRUSTWORTHY**, zero errors, zero `sorry`.

### THE FIRST REAL STEP INTO `RoundWithAccuracyIsNearest`

`Mul.lean` reduced multiplication to one obligation about core's
`roundWithAccuracy`. That obligation bottoms out in a translation problem:
**core decides every rounding from two bits**, round and sticky, and nothing so
far said what those bits mean in exact arithmetic.

Now something does. After shifting `⟨m, false, false⟩` right by `n+1`:

| bit | value |
| --- | --- |
| mantissa | `m / 2^(n+1)` (already had it — `em_shift_mantissa`) |
| **round** | bit `n` of `m`, i.e. `(m / 2^n) % 2 ≠ 0` |
| **sticky** | whether anything below survives, i.e. `m % 2^n ≠ 0` |

Together they determine `m % 2^(n+1)` against `2^n` — **exactly the comparison
every IEEE §4.3 rounding mode needs**, and exactly what `roundQ`'s `applyRM`
consumes. The bit-level and the exact-rational views of rounding are now the
same view.

### TWO ASYMMETRIES WORTH RECORDING

* **`em_shift_round` needs NO induction.** One unfold plus `em_shift_mantissa`
  — because the round bit after `n+1` shifts is just the low bit of the
  mantissa after `n`. The recursion was already paid.
* **`em_shift_sticky` is a genuine recursion** — `sticky(n+1) = round(n) ∨
  sticky(n)` — and turns on `Nat.mod_pow_succ`
  (`x % b^(k+1) = x % b^k + b^k * ((x / b^k) % b)`), which core ships.

### THE ARITHMETIC OBSTACLE, AND IT IS A GENERAL ONE

`omega` could not close the sticky step, and the reason generalizes past this
lemma: `2^n * ((m / 2^n) % 2)` is **nonlinear**, and `omega` is a linear
decision procedure. **Casing the bit first** — it is `0` or `1` by
`Nat.mod_two_eq_zero_or_one` — turns the product into `0` or `2^n` and the
goal becomes linear.

> **When `omega` fails on bit arithmetic, look for a product of a power and a
> bit, and case the bit.** The nonlinearity is usually one variable wide.

### AND A METHOD NOTE: STOP GUESSING DEFINITIONAL FORMS

Three attempts were lost to hand-written `show` patterns guessing how core's
`>>>` unfolds. The fix was to run `simp only [...]` with `trace_state` and
**read the actual goal**, which showed `(E0 m).mantissa` sitting unreduced —
the reason a perfectly good hypothesis `hb` would not apply. Two minutes of
looking beat three rounds of guessing.

### §9.0 — STILL 1/12

These are lemmas toward the obligation, not the obligation. `mul_correct_of`
stays conditional. **30 landed theorems, 1 an unconditional `op_correct`.**

### WHAT REMAINS IN `RoundWithAccuracyIsNearest`

With the bits now meaning something, the residue is in hand. What is left:
`roundToNearestEven` picks the nearer of the two neighbours (a case analysis on
the `Accuracy`, now that `Accuracy` is pinned to `m % 2^(n+1)` vs `2^n`); the
second `shiftToTargetExponent` absorbs a rounding carry-out; and the result is
nearest among **all** representables, which is the interleaving argument.

---

## 2026-08-24-softfloat-21 — THE NEARER-NEIGHBOUR CASE ANALYSIS: core's rounding IS round-half-to-even

`LeanModels/SoftFloat/Theorems.lean`. `em_shift_eq` and
`roundedMantissa_eq_roundHalfEven`, both `[propext, Classical.choice,
Quot.sound]`, verdict **TRUSTWORTHY**, zero `sorry`.

### THE STATEMENT

```
(⟨m, false, false⟩ >>> (n+1)).roundedMantissa
  = if 2 * (m % 2^(n+1)) < 2^(n+1) then m / 2^(n+1)
    else if 2^(n+1) < 2 * (m % 2^(n+1)) then m / 2^(n+1) + 1
    else m / 2^(n+1) + (m / 2^(n+1)) % 2
```

Both sides are **exact integer arithmetic against the residue**. Core's
rounding is no longer a bit procedure this component reasons *around*; it is
round-half-to-even, and the four branches are the four IEEE §4.3.1 cases:
exact, strictly below half, **exactly half → tie to even**, strictly above.

The step it unlocks is the one it was for: `Accuracy` was pinned to the residue
by the bridge lemmas, and the case analysis was then closed rather than
open-ended — four branches, each decided.

### FOUR OBSTACLES, AND EACH IS A GENERAL LESSON

The proof took five iterations. Every failure was mechanical, and all four
causes recur:

1. **A `match` will not reduce while its scrutinee is symbolic.** Core's
   `accuracy` matches on `⟨_, roundBit, stickyBit⟩`; leaving
   `stickyBit := m % 2^n != 0` un-literalised stalled two branches with no
   error message pointing at the cause. **Both bits must be literal `true`/
   `false` first** — by `rw [hb]` where a hypothesis is an equation, and by
   `rw [show (… != 0) = true from by simp [hs]]` where it is a negation.
2. **A hypothesis stated over `2^(n+1)` never fires against a goal rewritten
   to `2 * 2^n`.** `hres` had to be *restated* over the same power the goal
   carries. Rewriting the goal and not the hypothesis is a silent no-op.
3. **`omega` cannot resolve an `if`.** The last branch failed with a
   perfectly linear goal still wrapped in a conditional; `rw [if_neg (by
   omega), if_pos (by omega)]` discharged the conditions and the rest was
   `rfl`.
4. **`omega` is linear** — already recorded for `2^n * bit`, and it bit again.

### THE METHOD NOTE FROM THE LAST ENTRY PAID FOR ITSELF, TWICE

`2026-08-24-softfloat-20` recorded *"stop guessing definitional forms; run
`trace_state` and read the goal."* Two of the four obstacles above were found
that way in one step each, after guesses had failed repeatedly. The third
guess-driven attempt made the proof **worse** — an invented `show
… = decide (1 = …)` rewrite turned 2 failing cases into 8. Reading beat
guessing every time it was tried.

### §9.0 — STILL 1/12

Lemmas toward `RoundWithAccuracyIsNearest`, not the obligation.
**32 landed theorems, 1 an unconditional `op_correct`.**

### WHAT REMAINS, in dependency order

Carry-out absorption (the second `shiftToTargetExponent`, for when rounding up
overflows the significand), then nearest-among-**all**-representables — the
interleaving argument, which is the genuinely hard one and the last piece.

---

## 2026-08-24-softfloat-22 — THE RED WAS MY VERIFICATION METHOD, NOT A RENAME

Triad on `d98177b` went **RED** in five seconds — build failed, `GATES NOT RUN`.
`Unknown identifier Accuracy.roundToNearestEven` in
`LeanModels/SoftFloat/Theorems.lean`. Aborted triad, no landing.

### IT WAS NOT A RENAME, AND NOT A STRANDED CONSUMER

The standing hypothesis was a rename with an unswept consumer — the clash-check
family in reverse. **Measured: nothing was renamed.** Core's
`Accuracy.roundToNearestEven` is intact, and the failing references are in the
block this lane had just *added*, not in older code.

The actual cause is **scope**:

* `Theorems.lean:18` opens `Float.Model.UnpackedFloat (Sign ExtendedMantissa)`
  — **no `Accuracy`**;
* the probe the proof was developed in opened `(ExtendedMantissa Accuracy)`.

So the proof compiled in the probe and could not compile in its destination.

### AND THE VERIFICATION THAT SHOULD HAVE CAUGHT IT WAS UNSOUND

Every landing in this lane has been checked by concatenating `Basic.lean` and
the target file into one scratch file. **That sim merges `open` scopes that
modules keep separate**, and it did so here in a specific, findable way:

> `Basic.lean:180` carries `open Float.Model.UnpackedFloat (Sign ExtendedMantissa
> Accuracy)`. The concatenation dropped `Basic`'s `end`, so that open stayed
> live over the appended `Theorems` content — supplying the very name the real
> module lacks.

`open` is section-scoped and does not cross a module boundary. The sim erased
the boundary, so it was testing a file that does not exist.

### THE FIX, BOTH HALVES

**The code:** add `Accuracy` to `Theorems.lean`'s open list. One line.

**The method:** the sim now keeps `Basic.lean`'s `end` and appends the target
**from its own `namespace` line**, so the target's opens are the only ones in
scope — which is what the real module sees.

**Both directions RUN, because a check that has never failed is a design and
not a control:**

| sim | with the fix | without the fix |
| --- | --- | --- |
| old (merged scopes) | 0 errors | **0 errors — MISSED IT** |
| new (faithful) | 0 errors | **8 errors, `Unknown identifier Accuracy.roundToNearestEven`** |

The faithful sim reproduces the triad's red exactly. The old one is why a
`TRUSTWORTHY` verdict preceded a red build.

### WHY THE TRIAD CAUGHT IT AND NOTHING ELSE DID

Worth naming: `docs_check`, the census gates and all ten probes were green —
every one of them, before and after. **None of them compiles `LeanModels/**` as
modules**; only `lake build` does. The probes are core-only by design (that is
what makes them lock-free), and the sim was standing in for the module build
and doing it wrongly. **The triad was the only instrument pointed at the real
artifact**, which is exactly why a red triad is worth its tenure.

### `--iterate` REFUSED, CORRECTLY

The natural fix-verification was `check.sh --iterate` on the real module — the
new mode built for this. It **refused**: memory pressure 65.0% against a 50%
line. That is the courtesy protocol working, and it is why the faithful sim was
built instead of waiting.

### §9.0 — STILL 1/12

Unchanged; the theorems are the same ones, now in a file that compiles.
**32 landed theorems, 1 an unconditional `op_correct`.**
