# The analog lane's backlog (Circuit + Spice)

Per-lane file per `docs/family-architecture.md` §9.5. **Appended only by the
analog lane.** Ids are `YYYY-MM-DD-analog-<n>`. Entries newest-last.

**This lane is a SECOND ARCHITECTURE, deliberately.** `docs/family-architecture.md`
§6.1 item 3 places continuous state outside the `Run σ` model and records that
`LeanModels/Circuit/` and `LeanModels/Spice/` "use no `Run` at all, modelling by
interval enclosure and contract". The two lanes are **not unified** and are not
to be unified. The design contracts are `docs/circuit-assurance-architecture.md`
(semantic root) and `docs/circuit-spec-surface.md` (the implementation ledger).

**Dependency posture: MATHLIB, declared.** §3.2 makes "core only, no packages" a
per-tier claim. This tier is the counter-example and says so: 22 of the 26
Mathlib-importing files in the repository are its own (Circuit 11, Spice 11), and
it needs `Mathlib.Data.Real.Basic`, `Analysis.Calculus.Deriv` and friends because
`Circuit/Enclosure.lean` quantifies over `ℝ` directly. Verified 2026-08-24.

---

### SPEC COVERAGE — the completion metric (standing; updated every landing)

Reproduce it, do not quote it:

    python3 harness/spice/assurance_census.py

**The denominator counts what could have DISAGREED** (§9.0(a)). For this tier
that is not "theorems proved" but "premise sets shown to be inhabited", because
every obligation in `AssuranceCase` is universally quantified over `allowed`.

| landing | sha | grounded assurance cases | circuits fully grounded | circuits with any case |
| --- | --- | ---: | ---: | ---: |
| pre-lane baseline | `ed9f1f5` | 0 / 24 | 0 / 21 | 9 / 21 |
| `2026-08-24-analog-1` | `491b944` | **8 / 24** | **4 / 21** | 9 / 21 |
| `2026-08-24-analog-2` | `c34834e` | 8 / 24 | 4 / 21 | 9 / 21 |
| `2026-08-24-analog-3` | `5119cf6` | 8 / 24 | 4 / 21 | 9 / 21 |
| `2026-08-24-analog-4` | `494b850` | 8 / 24 | 4 / 21 | 9 / 21 |
| `2026-08-24-analog-5` | `2cf53de` | 8 / 24 | 4 / 21 | 9 / 21 |
| `2026-08-24-analog-6` | `130dd20` | 8 / 24 | 4 / 21 | 9 / 21 |
| `2026-08-24-analog-7` | `3e8c41e` | 8 / 24 | 4 / 21 | 9 / 21 |
| `2026-08-25-analog-8` | `1d1f55e` | 8 / 24 | 4 / 21 | 9 / 21 |
| `2026-08-25-analog-9` | `341e247` | 8 / 24 | 4 / 21 | 9 / 21 |
| `2026-08-26-analog-10` | *(next commit)* | 8 / 24 | 4 / 21 | **20/20 primary, 9/20 bundling** |

**THE PRIMARY NUMBER — NON-VACUOUS BEHAVIOR GUARANTEES: 20 / 20.**

Every circuit in the corpus that carries Lean has a proved behavior guarantee
whose premise set is shown inhabited. The denominator is **20, not 21**:
`gnd_alias` is a parser regression fixture with **no `.lean` file at all**, so
it is out by construction rather than by omission.

**THE BUNDLING NUMBER — `AssuranceCase` cases: 9 / 20 (secondary).** This is
what the ledger quoted as `9 / 21` from its founding until `2026-08-26-analog-10`,
and it was never a coverage number: it counts how many circuits use the typed
`AssuranceCase` BUNDLE, not how many are guaranteed. Quoting it as the tier's
standing figure understated the tier by more than a factor of two.

> **`9/21` measured BUNDLING and was read as COVERAGE. A denominator inherits
> the meaning of whatever the numerator happens to count, and nothing in the
> figure itself says which was meant.**

Both numbers are reproduced, not quoted, by the same command
(`python3 harness/spice/assurance_census.py`), which now enumerates **five**
non-vacuity idioms because counting one of them is exactly how `9/21` happened.

**F2 exp/log certificates discharged: 7 / 7 — THE FAMILY IS CLOSED.**

**AND THE DENOMINATOR WAS WRONG UNTIL THIS LANDING.** Every previous entry
reported `N / 12`. Re-censusing with a bracket-aware extractor found **7**, not
12: the original figure counted library-internal occurrences of
`hdeadline`/`hsmall` and six *plain bounds* (`0 ≤ deadline`,
`deadline ≤ horizon`, `1/1e9 ≤ horizon`) that are trivial side conditions, not
transcendental certificates. A first regex attempt at the recount **also
under-counted**, silently missing `loaded_rc` because its hypothesis nests
parentheses two deep.

> **A denominator computed by a heuristic is a heuristic. This one was quoted
> in four consecutive landings before anything checked it, and §9.0's warning
> that a denominator is "quoted without its definition" was written about
> exactly this.**

The seven, and the corollary that discharges each — six corollaries for seven
obligations, because `performance_realizable` carries two:

| parent theorem | hypothesis | discharged by |
| --- | --- | --- |
| `loaded_rc_settles` | `hdeadline` | `loaded_rc_settled_at_horizon` |
| `loaded_inverter_settles_within` | `hdeadline` | `loaded_inverter_settled_at_microsecond` |
| `dram_1t1c_write_zero_settles` | `hdeadline` | `dram_1t1c_write_zero_settled_at_2ns` |
| `dram_sense_amp_small_signal_realizable` | `hsmall` | `..._realizable_at_1ns` |
| `dram_sense_amp_small_signal_behavior` | `hsmall` | `..._behavior_at_1ns` |
| `dram_sense_amp_small_signal_performance_realizable` | `hdeadline` + `hsmall` | `..._performance_at_1ns` |

**F2 IS A FAMILY, NOT THE TIER** (§9.0's waypoint law). F4 still has 88 sites,
F3 eight, F5 two, F6 one, and F1 is unclosable by construction. Closing F2
closes the family that was the tier's stated real-analysis frontier; it does
not close the tier.

**The certificate kit is now directionally COMPLETE** — decay above, decay
below, growth below, growth above — which is what analog-6 found missing.

**DECLARED DIVERGENCES: 0** — and the qualifier is part of the number.

**F1 RIDES THIS TABLE AND IS NOT OPTIONAL**: `model validity: MISSING`,
architecturally unclosable, admitted 12×. The numbers above are model-level
throughout; none of them is evidence that a fabricated device matches its model.

The register ruled F1 an **EPISTEMIC BOUNDARY, not a debt** (§5.0a admits no
permanent row; the discriminator is whether the closing condition can be NAMED,
and for F1 no experiment the domain admits can establish model validity). So it
is not filed as a divergence, and the standing line carries this instead:

> **A permanent admission is part of what the number MEANS; a debt is something
> the number WAITS ON.**

The underdetermined-node observation (below) was likewise ruled a named
non-case — *spec-admits-both* — because a row there would assert the model is
wrong where the spec declines to choose. Zero divergence rows, correctly.

`491b944` is a **scoped** green (`tier` class): it covers the modules built and
everything they import, not the modules that import them and not any untouched
tier. Triad `[01:41:35] LOCK ACQUIRED after 4164s` → `[02:26:24] BUILD GREEN` →
`[02:26:59] TRIAD DONE (build exit 0, gates green)` → `[02:27:00] LOCK RELEASED
(mine)`. Citable as an increment base with `--since 491b944`.

**TWO DENOMINATORS, and the gap is the point.** The table above counts
`AssuranceCase` declarations, which only 9 of the 21 circuits use. The other 12
carry proved behavior specs in the lane's older house style — a universal
theorem paired by hand with a `..._realizable` twin — and those are not worse,
they are unbundled. Against the corpus rather than the bundle:

* **19 / 21 circuits have a proved behavior spec**, and since
  `2026-08-24-analog-2` **all 19 of them are non-vacuous** — `and_gate` was the
  last contract with no companion observation and now has one for all four input
  vectors. `gnd_alias` is a parser regression fixture with no Lean file at all,
  and is out of the denominator by construction rather than by omission.
* **19 / 21 circuits are reachable from an ngspice path** in `harness/spice/`.
  The two with no oracle path are `dram_array_2x2` and `dram_bitcell`.

**THE BOUND RUNS THE OTHER WAY FROM GO'S.** §9.0's syntactic guard warns that a
syntactic coverage measure is an UPPER bound. This instrument's is a **LOWER**
bound: it recognises one canonical spelling (`GroundedUnder`), so a case grounded
by some other lemma reads as ungrounded. `dram_bank_256x32` is exactly that —
`dram_bank_256x32_nominal_profile` inhabits its allowed-world set for every
world. `NO-GROUNDING-WITNESS` therefore means *this instrument cannot see a
witness*, *never* *this case is vacuous*, and the instrument says so in its own
output. Retiring a flag is done by writing the canonical witness, which is also
what makes the fact mechanically checkable.

---

## 2026-08-24-analog-1 — CENSUS-FIRST: non-vacuity is a chain of two links, and the tier closed only the inner one

**The finding.** `AssuranceCase` (`LeanModels/Circuit/Assurance.lean`) bundles
`safe`, `realizable` and `withinDomain`. `RealizableUnder` is there so that a
safety theorem cannot rest on an empty BEHAVIOR set — `docs/circuit-assurance-architecture.md`
says so in as many words: *"A safety theorem over an empty behavior set is not a
complete correctness result."* But all three fields read
`∀ world, allowed world → …`, and `RealizableUnder` is itself guarded by
`allowed world`. So an `allowed` predicate that **no world satisfies** discharges
all three obligations simultaneously, and `#assurance_report` prints the same
lines it prints for a real result.

> **Non-vacuity is a chain of two links — an inhabited WORLD set, then an
> inhabited BEHAVIOR set. A guard on the inner link cannot see the outer one,
> because the guard is itself inside it.**

The failure is invisible in the flattering direction, which is why it survived
27,675 lines and a purpose-built non-vacuity instrument: nothing about an empty
`allowed` looks like an error, and `typed_divider/spec.lean` even labels its
realizability theorem *"an explicit non-vacuity result"*.

**The inch.** Three declarations in `Assurance.lean`, no new imports:

* `GroundedUnder allowed : Prop` — `∃ world, allowed world`, the outer link;
* `ExhibitsUnder behavior allowed specification domain` — the existential form,
  which is FALSE when `allowed` is empty and is therefore the statement that
  could have disagreed;
* `AssuranceCase.exhibits` — one lemma converting **any** of the tier's 24
  assurance cases from three universal obligations into the existential form,
  given the one fact none of them carried.

Applied to the four circuits whose allowed-world sets are singletons or `True`:
`typed_divider`, `rlc_discharge`, `loaded_rc`, `ac_lowpass`. 0 / 24 → 8 / 24
(each circuit carries the case twice, in `proof.lean` and in `spec.lean`).

**Why these four and not the others** — the census authorises the order (§9.0b).
Their allowed-sets are `world = <named world>` or `fun _ => True`, so the witness
is `rfl` or `trivial`. The remaining families are priced below.

---

### THE OBLIGATION CENSUS — families, because the flat list misleads

**There are no sorries, so the obligation surface is somewhere else.** Census of
all 564 theorem signatures plus every Prop-valued structure field and every
prose concession across `LeanModels/Circuit/`, `LeanModels/Spice/` and
`Examples/spice/`, grouped by the MISSING LEMMA rather than by the site:

| id | family | sites | the single missing thing |
| --- | --- | ---: | --- |
| **F2** | **transcendental numeric certificate (`exp`/`log` deadline)** | **12** | **`RatInterval.exp_contains` — a rational two-sided enclosure for `Real.exp`** |
| ~~F4~~ | ~~channel-length modulation~~ — **COLLAPSED, `2026-08-25-analog-9`** | ~~88~~ **0** | **none — a declared boundary, enforced once and gated** |
| F3 | unbalanced latch determinacy / convergence / restore | 8 | Grönwall/ODE uniqueness lifted from the scalar case to the 2-D pair field |
| F1 | physical-envelope coverage (model ↔ fabricated device) | 19 | **none — not closable in Lean** |
| F7 | dead framework surface (carriers with zero suppliers) | 9 | nothing; the stated architecture is wider than the discharged one |
| F5 | small-signal AC for nonlinear devices | 2 | an `ApproxLinearizationAt` with a Taylor remainder bound |
| ~~F6~~ | ~~interval-arithmetic width~~ — **CLOSED, `2026-08-26-analog-10`** | ~~1~~ **0** | `sub`, `neg`, sign-mixed `mul` landed |
| F8 | elaboration-time dimension checking | 2 | engineering, not mathematics |

**F2 IS THE FIRST REAL-ANALYSIS INCH, and the census is what says so.** Every
settling example — `loaded_inverter`, `dram_1t1c`, `loaded_rc`, `dram_sense_amp`
— has a fully proved exponential or logarithmic envelope underneath it, with IVT
existence, Picard–Lindelöf realizability, Grönwall determinacy and barrier
domain-closure all landed. Each then stops one inference short, taking the
numeric bound as a hypothesis (`hdeadline`, `hsmall`) that reaches the top
UNINSTANTIATED. F2 is the last inch on all of them at once.

**And it is already done once, by hand, which is what makes it tractable rather
than hopeful.** `Spice/DramBankCoreSpec.lean:30-36` proves `Real.exp (-(16/3)) ≤
1/4` in seven lines from `Real.add_one_le_exp`, and `:118-167` uses it to
actually discharge a `hdeadline`. The work is to generalise that into
`Circuit/Enclosure.lean` beside `RatInterval.add` / `mulNonnegative` /
`dividerOutputInterval`, and to teach `circuit_enclose` — which today applies
exactly ONE theorem — to reach it. Mathlib supplies `Real.add_one_le_exp`,
`Real.exp_neg`, `Real.exp_le_exp`, `Real.one_sub_le_exp_neg`,
`Real.log_le_sub_one_of_pos`.

**F4 is the largest by site count and must not therefore be read as the
priority.** All 88 sites instantiate `lambda := 0`; the only λ-general theorem is
the trivial cutoff case at `Mos1.lean:113`. `lambda` IS parsed from the netlist
(`Mos1.lean:29`), so the idealisation is real rather than cosmetic, and
`DiffPair.lean:34-35` names it as what breaks the CMRR theorem. But each site is
individually cheap and none blocks a top-level claim; it is 88 re-proofs, not one
lemma. **Site count ranks effort, not value.**

**F1 IS ARCHITECTURALLY UNCLOSABLE, and the tree says so twelve times.** Every
one of the 12 `#assurance_report` invocations prints
`model validity: MISSING (model-level theorem only; no physical coverage
evidence)`, because `AcceptedValidity` is constructed in exactly two places
(`Spice/DiffPair.lean:1179`, `Spice/CommonSource.lean:822`) and BOTH take
`haccepted : claim.statement` as a parameter that is never applied. That is not a
defect to fix — no Lean proof turns a PDK measurement into a kernel theorem — and
the machine-emitted admission on every example is the honest boundary of the
whole enterprise. **Keep it visible whenever this tier is described.**

> **THE MANDATED QUOTING FORM (coordinator ruling, 2026-08-24).** Every
> description of this tier — the §9.0 standing report included — carries F1 as:
> **`model validity: MISSING`, architecturally unclosable, admitted 12×.**
> A coverage number for this tier that omits it is quoting the numerator
> without the boundary the whole tier sits inside.

---

### THE OPEN QUEUE, censused and priced

**A1 — LANDED, `2026-08-24-analog-2`.** *(Original entry kept below; the queue
is a record, not a to-do list.)* **A1 — `and_gate` has no realizability twin,
and its sibling proves the exact missing lemma.** `cmos_and_mos1_correct : Mos1BinaryGateContract …` is purely
universal over `Mos1ComponentSatisfies ∧ Mos1WithinSupply ∧ Mos1DrivesTwo`, and
nothing in the tree proves that premise set is satisfiable for this deck.
`half_adder` proves precisely that shape — `half_adder_mos1_observation_exists`,
by exhibiting `halfAdderMos1Witness left right` and discharging the three
conjuncts by `simp <;> norm_num` over all four input pairs — and the half-adder
deck instantiates the same `and2` subcircuit. **This is the one concrete vacuity
gap in the corpus and it has a worked template.** Next inch.

**A2 — ground the two PVT-envelope cases.** `RobustDividerAllowed` is three
interval memberships over a `DCRunWorld` record; `LoadedInverterExampleAllowed`
is `LoadedInverterCornerRun`, a corner box that the deck's projected nominal sits
inside. Both need a constructed witness world rather than `rfl`, and neither is
hard — `robust_divider` needs `deterministicWorld` with `sourceVoltage := 5` and
resistances `1000`/`2000`, then `norm_num`. +4 cases.

**A3 — `dram_*` grounding in the canonical spelling.** `DramBankCoreReadAllowed
profile _world := DramBankCoreNominalProfile profile` is already inhabited by
`dram_bank_256x32_nominal_profile` / `dram_bank_2x2_core_nominal_profile`; the
work is to state it as `GroundedUnder` so the instrument can see it. +8 cases,
and it is the cheapest of the three.

**A4 — `dram_1t1c_assurance` passes `Dram1T1CValidityDomain` as BOTH the
specification and the domain**, proved by the same term twice
(`⟨dram_1t1c_domain, dram_1t1c_realizable, dram_1t1c_domain⟩`). Its `safe`
obligation is therefore its `withinDomain` obligation restated, and the case
carries one claim wearing two hats. The real content is in
`dram_1t1c_write_one_assurance`. Flagged `SPEC-EQ-DOMAIN` by the census; decide
whether to give the hold phase a genuine behavior specification or to retire the
case in favour of the write-one one.

**A5 — `typed_divider`'s domain is `fun _ _ _ => True`.** The `withinDomain`
obligation carries zero information. Flagged `TRIVIAL-DOMAIN`. Not a defect —
DC on exact rationals has no validity domain to leave — but the report should
say so rather than printing "domain closure" as though it measured something.

**A6 — `#assurance_report` should print grounding**, in the idiom it already
uses for `model validity`: that field prints
`MISSING (model-level theorem only; no physical coverage evidence)` when absent,
which is the right shape. Grounding deserves the same line rather than silence.
Metaprogramming in `Circuit/Surface.lean`; costs a tenure to iterate.

**A7 — two circuits have no ngspice path**: `dram_array_2x2` and `dram_bitcell`.
Not a proof gap (no simulator result is ever a theorem premise) but a validation
gap, and cheap to close — `harness/spice/` already has eight transient runners.

**A8 — `dram_bitcell`'s `nominalRead` is not tied to its deck.** The behavior
theorems use `storageCapacitance := 30, bitlineCapacitance := 300`; the deck
carries `3e-14`/`3e-13`. Only the RATIO agrees and **no theorem links the two**.
`dram_bitcell_topology` exists but no behavior theorem consumes it, and
`spec.lean` has no `load_circuit` at all. This is the one place in the corpus
where a proved theorem is about a model the source does not pin.

**A9 — the imported-contract residue.** `EquationManifest` names these honestly
rather than hiding them, which is the system working; they are still
assumptions: `"ideal sense discriminator"` and `"ideal restore endpoint"`
(`dram_bitcell`), and the legacy two-inverter sense endpoint contract (both DRAM
banks). Each is a derivation not yet done.

**A10 — the F2 lemma itself** (see the family census above): widen
`Circuit/Enclosure.lean` with `RatInterval.exp_contains` and teach
`circuit_enclose` to reach it, then discharge the four top-level `hdeadline` /
`hsmall` hypotheses. **This is the tier's real-analysis frontier and the highest-
value item in this queue** — higher than A1, which is merely the cheapest.

*(Correction to a first reading, recorded because the prose invites it:
`DramDifferentialSenseUnbalanced.lean:1899` is NOT an open obligation. Its
sentence "admit a uniform positive regeneration-rate certificate over every
rail-valid unresolved common-mode state" describes a certificate that is PROVED
immediately below it at `:1901-1924`, via `IsCompact.exists_forall_le'`. A grep
for concessive phrasing finds proved theorems as readily as open ones; the
census had to read each hit.)*

---

### FOR THE COORDINATOR — findings outside this lane's authority

**C1 — the "Spice 11, Circuit 11, Verilog-A 1" line in §3.2 is a MATHLIB IMPORT
count, not a sorry count.** Verified exactly: 26 files import Mathlib, 11 + 11 +
1 under `LeanModels/` plus 3 under `Examples/`. **There are ZERO `sorry`s in
either analog lane** — and zero `axiom`s, zero `native_decide`, zero `opaque`.
The only occurrence of the token is the guard in `Circuit/Surface.lean:575` that
REJECTS any declaration whose `collectAxioms` contains `sorryAx`. A dispatch
brief that reads §3.2's sentence as a sorry census will send a lane hunting for
eleven things that are not there.

**C2 — `set_option autoImplicit false` is in 1 of 163 `LeanModels/` files** (only
`LeanModels/Sv/Step.lean`) **and 0 of 188 `Examples/` files.** The campaign
states it as a required loudness guard; the tree does not carry it, in any tier,
including Python. `Circuit/Assurance.lean` depends on auto-bound implicits today
— `AssuranceCase`'s `World Boundary Internal` are auto-bound, and
`Circuit/Surface.lean` hard-codes the resulting arity (`arguments.size == 10`)
and position (`arguments[4]!`). Flipping the option is therefore a real change
with a metaprogramming blast radius, not a one-line hygiene fix. **This lane did
not flip it unilaterally**; the new declarations are written with fully explicit
binders so they survive a future flip. Surfacing rather than deciding.

**C3 — the ngspice oracle is CLI-reachable and needs no MCP server.**
`/opt/homebrew/bin/ngspice` is ngspice-46, and `harness/spice/` holds thirteen
scripts that drive it directly; `tools/ci.sh` gates them behind
`command -v ngspice` with an explicit SKIP row per step rather than a silent
omission. No lane needs the `spice-sim` MCP server to reach the oracle.

**C4 — this tier implemented §5.3's vacuity ruling in Lean before the family
minted it as prose.** `AssuranceCase` structurally refuses to let safety be
assembled from unrelated theorem names, `SourceBinding`'s two equalities stop a
case naming one circuit while proving facts about another, and `#assurance_report`
rejects a case attached to a different elaborated circuit. Last substantive
commits here were July 25–29; §5.3 and §9.0(a) are August. The dormant lane was
ahead of the register, and the register should cite it.

---

## 2026-08-24-analog-2 — A1: the last contract without a witness, and a symmetry lemma declined

**The gap.** `cmos_and_mos1_correct` is a `Mos1BinaryGateContract`: universally
quantified over every state satisfying the component equations, the supply
envelope and the input drivers. Nothing in the tree showed such a state exists
for this deck, so the theorem was the same shape as the assurance cases
`2026-08-24-analog-1` grounded — true of a deck no state satisfies. `and_gate`
was the last one in the corpus.

**The fix, from the sibling's template.** `half_adder` already proves exactly
this shape (`half_adder_mos1_observation_exists`, exhibiting
`halfAdderMos1Witness` and discharging the conjuncts over all four input pairs),
and the half-adder's `and2` subcircuit **is** this deck — `and_gate.cir` is that
subcircuit flattened. So:

* `LeanModels/Spice/Mos1.lean` gains `Mos1BinaryGateObservation`, the two-input
  analogue of `Mos1HalfAdderObservation`;
* `Examples/spice/and_gate/proof.lean` gains `andGateLevel` /
  `andGateMos1Witness` / `and_gate_mos1_observation_exists`, proved for all four
  vectors;
* `spec.lean` exposes it with `#print axioms`.

The witness rails are the deck's own: `nand = ¬(a∧b)`, `out = a∧b`, and
`nseries = a ∧ ¬b` — the series node between the two pull-down NMOS devices,
matching `xcarry.nseries` in the half-adder. The deck's committed ngspice
comments agree (`00: out≈0, nand=5`; `11: out=5, nand≈0`), which is validation,
never a premise.

**A SYMMETRY LEMMA DECLINED, and this is the reusable part.** The obvious
companion was `Mos1BinaryGateContract.observation_sound`, mirroring
`Mos1HalfAdderContract.observation_sound`. It was written, then removed. The
half-adder's version refines an observation into `HalfAdderBehavior`, a separate
implementation-independent predicate; the binary-gate version's conclusion would
be `output = operation left right`, which is **definitionally trivial** once
`output` is instantiated to `operation left right`.

> **A lemma that cannot fail is not a lemma, and "the sibling has one" is not a
> consumer. Symmetry is a reason to LOOK for a lemma, never a reason to KEEP
> one.**

This is F7 (dead framework surface, 9 sites) caught at the moment of creation
rather than found in a later census — the cheapest place to catch it, and the
only place where declining costs nothing. A comment stands where the lemma would
have been, saying why it is absent, so the next reader does not re-add it.

**autoImplicit retrofit rode this touch** (ruling 1(b)): `Spice/Mos1.lean`,
`and_gate/proof.lean` and `and_gate/spec.lean` now carry
`set_option autoImplicit false`. All three verified monomorphic first — no
`Type`/`Sort` binders, no generic or Greek type variables across 44 + 8 + 3
declarations — and the option is **file-local**, so the 11 files importing
`Mos1.lean` are unaffected. That is the difference from `Circuit/Assurance.lean`,
where the flip is a semantic change because `Circuit/Surface.lean` hard-codes
`AssuranceCase`'s arity at 10 and its circuit at index 4.

**Standing number unmoved: still 8/24 grounded assurance cases.** `and_gate`
carries no `AssuranceCase`, so this landing does not touch that table — it moves
the *corpus* denominator instead: all 19 circuits with a proved behavior spec are
now non-vacuous. **A landing that improves the tier without moving the headline
number must say so rather than letting the flat table imply nothing happened**
(§G22's `+0` discipline).

**Next: A10/F2** — `RatInterval.exp_contains`, with
`Spice/DramBankCoreSpec.lean:30-36` as the specification of done.

### Triad — RED first, and a comment is not syntactically inert

`[04:36:54] LOCK ACQUIRED after 3616s as 'analog 67609'` →
`[04:38:00] BUILD DID NOT COMPLETE (exit 1)` → `GATES NOT RUN (build red —
aborted triad)` → `[04:38:01] LOCK RELEASED (mine)`. One module, one error:

    LeanModels/Spice/Mos1.lean:804:77: unexpected token '/--'; expected 'lemma'

**The declined-lemma comment was itself the defect.** The note left "where the
lemma would have been" was written as a doc comment, and a doc comment is
GRAMMAR: it must attach to a declaration. It is therefore exactly the wrong
form for marking a declaration's ABSENCE — **it occupies the slot it is trying
to say is empty.** One hour of queue, 66 seconds of build, gates never reached.

> **A comment is not syntactically inert. A doc-comment token is grammar, not
> prose, and the declined-lemma convention needs a comment FORM that cannot
> occupy a declaration slot.**

**AND THE FIX HAD THE SAME BUG ONE LEVEL DOWN, caught before the queue.** The
plain-block rewrite *quoted the delimiters it was describing* — and Lean block
comments **NEST**, so an opener written as an example, even inside backticks,
raises the depth and never lowers it: the comment swallows the rest of the
file. A depth count over the file found it at nesting depth 2. A second draft
then dropped the closing delimiter entirely — the very failure the note
warns about — and the same count found that too.

> **A comment that describes comment syntax cannot QUOTE it. Name the
> delimiters; never spell them.**

**So the fix lives in a gate**, `harness/lean_comment_forms.py`: orphan doc
comments and unbalanced block comments, over every `.lean` file in the tree
(385 today, 0 defects). Both refusal paths were RUN, not admired — injected
into throwaway files, each fires with exit 1.

**And the gate has a false-positive control, because the first draft had one.**
Go and SystemVerilog both have a `--` operator and both name it inside error
strings (`"++/-- on a non-integer"`), which reads to a naive scanner as a
doc-comment opener; the first draft reported `LeanModels/Go/Stmt.lean:821` and
`LeanModels/Sv/Param.lean:787` as defective when **both were clean**. The
scanners now skip string literals, and the control case is in the test set.
**The two tiers most likely to trip this check are the two whose languages
contain the token** — a gate whose false positives land on other lanes is worse
than no gate, because it spends someone else's attention.

**Proposal for the coordinator, not taken unilaterally:** wire
`lean_comment_forms` into `tools/ci.sh` near `docs_check`. It is pure Python,
shells out to nothing, needs no tenure, and runs the whole tree in under a
second. This lane runs it via `--gates` in the meantime.

**RED #3 — THE SAME FAMILY, AND THE GATE COULD NOT SEE IT.**
`[05:21:31] LOCK ACQUIRED after 2174s` → `[05:23:34] BUILD DID NOT COMPLETE
(exit 1)` → `GATES NOT RUN`. One error:

    Examples/spice/and_gate/proof.lean:122:16: unexpected token 'set_option'; expected 'lemma'

Not the `autoImplicit` retrofit — **all three guard placements were correct**
and were re-verified against the top-of-file rule. The defect was a doc comment
followed by `set_option maxHeartbeats … in`. A doc comment opens
`declModifiers`; `set_option … in` is a command **combinator**, not a
declaration, so the docstring never finds what it attaches to.

> **The correct order is `set_option … in` FIRST, then the docstring, then the
> declaration** — which seven sites on master already do, including
> `Spice/DramDifferentialSense.lean:1134` in this tier. The fix was to copy a
> shape the tree had already proved, instead of inventing one.

**AND THE OBVIOUS GENERALISATION IS UNSOUND — the tree refused it.** The family
is "a token in a declaration slot", so the natural fix is to WHITELIST the
declaration starters and flag everything else. That draft accused **60+
known-green sites**, because docstrings legally attach to things that are not
declarations: **structure fields** (`val : Int`), **inductive constructors**
(`| nil : I`), and **`#guard_msgs in` expected-output blocks**.

> **A whitelist of "what a docstring may precede" is a claim about Lean's
> grammar; a blacklist of "what it may never precede" is a claim about a few
> commands. Only the second is checkable without a parser.**

So the gate blacklists `set_option`, `open`, `namespace`, `section`, `end`,
`import`, `variable`, `universe`, another comment, and end-of-file. Sound
against all 385 green files (0 defects), and the regression set now pins all
three shipped reds plus five legal shapes that must stay silent — the string
literal, the documented field, the documented constructor, `#guard_msgs`, and
the proven-safe `set_option`-then-docstring order. Every case RUN, not admired.

**Parse validation without a tenure.** Lean cannot be run outside the lock and
these files are not dependency-free, so the placements were checked three other
ways: comment-nesting depth 0 in all touched files; the gate clean tree-wide;
and a **precedent check** — every doc-comment follower in the three touched
files matched one of the 169 distinct followers that already appear after doc
comments in green `origin/master` code.

---

## 2026-08-24-analog-3 — A10/F2: the transcendental certificate becomes a decision procedure, and F2 splits in two

**The kit** (`LeanModels/Circuit/Enclosure.lean`, six lemmas, no new imports):

| lemma | direction |
| --- | --- |
| `exp_neg_le_inv_one_add` | one step, `exp (-a) ≤ 1/(1+a)` |
| `exp_neg_le_inv_pow` | `n`-fold upper, `exp (-a) ≤ (1/(1+a/n))^n` |
| `one_sub_div_pow_le_exp_neg` | `n`-fold lower, `(1-a/n)^n ≤ exp (-a)` |
| `one_add_div_pow_le_exp` | `n`-fold lower on the positive side |
| `exp_neg_le_of_pow_le` | **decay certificate** |
| `log_le_of_le_pow` | **deadline certificate** |

All from `Real.add_one_le_exp` and `Real.one_sub_le_exp_neg` through
`Real.exp_nat_mul`. **The split depth is what makes it a procedure rather than
a lemma**: the one-step bound gives `exp (-16/3) ≤ 3/19`, nowhere near tight
enough for a real deadline, and raising `n` tightens it without bound —
`exp (-16/3) ≤ 1/100` needs `n = 20` and is then decided by `norm_num`. No
floating point anywhere in the path; both endpoints are exact rationals.

**Specification of done, met.** `dramBankCore_exp_write_zero_bound` was seven
bespoke lines; it is now one call at split depth 1.

**A SITE DISCHARGED, which is the part that counts.** `loaded_rc_settles`
carried `hdeadline : Real.log ((10/3)/ε)/1500 ≤ time` to the top of the deck
**assumed**. `loaded_rc_settled_at_horizon` now proves, at the deck's own 10 ms
horizon and a 10 mV tolerance, that the output is within tolerance — the
deadline certified at split depth 4, axioms `[propext, Classical.choice,
Quot.sound]`.

### F2 SPLITS IN TWO, and only one half was the exp certificate

The remaining sites are **no longer blocked on transcendental arithmetic**.
`loaded_inverter` and `dram_1t1c` state their deadline as
`initialError * exp (-rate * deadline) ≤ tolerance`, which is exactly
kit-shaped — but their worlds are **PVT CORNER ENVELOPES**
(`LoadedInverterCornerRun`), not single worlds, so `rate` is not a constant.
Discharging them needs a **worst-case bound over the corner box** first: the
minimum decay rate over the envelope. That is an optimisation problem over a
product of intervals, and it is a different piece of work.

> **A family named by its missing LEMMA can still be blocked on something that
> is not a lemma. F2's twelve sites were counted by the certificate they lack;
> two thirds of them are gated on a QUANTIFIER over a parameter box that the
> certificate never touches.**

So the honest F2 number is **1 of 12 top-level numeric hypotheses discharged**,
plus one bespoke constant retired — and the queue below is re-priced, because
the next inch is a corner-minimisation lemma, not more real analysis.

**A11 (new) — worst-case decay over a PVT box.** For `LoadedInverterCornerRun`
and its DRAM analogues, prove `rate world ≥ rateMin` for every allowed world,
with `rateMin` rational. Then the F2 certificate applies unchanged and
`loaded_inverter`, `dram_1t1c` and `dram_sense_amp` fall together — 8 of the
remaining 11 sites. This is the real unlock, and it is monotonicity over a
box, not analysis.

**autoImplicit retrofit (ruling 1(b)) rode `Circuit/Enclosure.lean` only.**
`Spice/DramBankCoreSpec.lean` was also touched but is **NOT** a free retrofit:
`rows` and `columns` are auto-bound throughout it and never declared, so the
flip there needs explicit binders added first. Recorded rather than forced —
the retrofit rides a touch only when it is inert, and this one is not.

**Iteration is open, and it changed the work.** This landing was built in a
scratch loop at roughly 8 seconds per probe, against the previous regime of one
attempt per hour-long queue. Every lemma name in the kit was WRONG on first
writing (`inv_le_inv_of_le`, `pow_le_pow_left` — both renamed in this Mathlib)
and each was found by probing `#check` rather than by spending a tenure. **The
one-shot regime did not just cost time; it selected for guessing.**

---

## 2026-08-24-analog-4 — A11: corner minimisation lands, and my own repricing was wrong

**The lemma.** `loadedInverterCornerRun_decayRate_lower`: over the entire PVT
corner box, `3e7 ≤ loadedInverterDecayRate world`. The binding corner is the
PMOS branch (`nBeta = 2 * pBeta`) at `1156000000/33 ≈ 3.5e7`; `3e7` keeps a 17%
margin and stays a round rational. With `initialError ≤ 11/2` and the F2 decay
certificate at split depth 10 (`exp (-30) ≤ 1/550`), the product is exactly
`11/2 × 1/550 = 1/100`, and `loaded_inverter_settled_at_microsecond` now proves
10 mV settling in one microsecond **for every allowed corner** — axioms
`[propext, Classical.choice, Quot.sound]`.

**THE PROBE SAID DON'T USE THE VOCABULARY IT WAS SENT TO FIND.** The instruction
was to probe Mathlib's monotone-on-a-box vocabulary first. It answered in the
negative, and that was worth more than a hit:

* `IsCompact.exists_isMinOn` gives a minimiser that **exists and cannot be
  evaluated** — against a concrete deadline that is no use at all;
* `MonotoneOn` / `AntitoneOn` would need the rate decomposed coordinate by
  coordinate, four monotonicity lemmas to say what one quotient bound says.

The rate is a single quotient, so bounding numerator below and denominator
above is **one `div_le_div₀`**, and the whole lemma compiled on the first
attempt.

> **A probe that returns "this vocabulary does not apply" has done its job.
> The measurement that probing pays does not require the probe to find
> something.**

### AND THE REPRICING IN `analog-3` WAS WRONG — I generalised from one deck

`analog-3` priced A11 as unlocking **8 of the remaining 11 sites**, on the
strength of `loaded_inverter` being a PVT corner box. Censusing the other two
decks while landing this one shows they are **not corner boxes at all**:

| deck | sites | world | blocked on |
| --- | ---: | --- | --- |
| `loaded_inverter` | 3 | PVT corner box | A11 — **1 discharged here** |
| `dram_1t1c` | 5 | `fabricated = dram1T1CNominal.instance` — **pinned** | concrete-constant arithmetic |
| `dram_sense_amp` | 4 | `dramSenseAmpLayout.fabricated = …` — **pinned** | concrete-constant arithmetic |

So corner minimisation unlocks **3 sites, not 8**, and the other 9 were never
corner-blocked — they are *easier* than priced, needing only the rate's concrete
value and the F2 kit already landed.

> **I priced eleven sites from the shape of one, one landing after invoking
> census-first to authorise the order. A repricing is a measurement and owes a
> census exactly like the first pricing did.**

The error was in the flattering direction for the *lemma* (it looked like it
unlocked more) and the pessimistic direction for the *tier* (nine sites looked
blocked on work they never needed). Both halves are wrong, which is what
extrapolation from one instance produces.

**Next: A12 — the pinned-nominal nine.** No new mathematics; instantiate the
decay rate at each deck's nominal constants and apply `exp_neg_le_of_pow_le`.
`dram_1t1c` first, being the larger.

**Note on the axiom pins.** The first draft of the `spec.lean` mirror named
`LoadedInverterExampleAllowed` unqualified, which does not resolve there; the
build went red **and** `#print axioms` reported `sorryAx` alongside the errors.
Not a silent degrade — the tenure would have caught it either way — but it is
the second signal, and it is why every new theorem here carries a pin.

**Iteration note.** `LeanModels/Spice/LoadedInverter.lean` takes **192 s** to
re-elaborate; the scratch loop against its built olean takes 8. Developing the
lemma standalone first and inserting it once is worth roughly one order of
magnitude on a file this size.

---

## 2026-08-24-analog-5 — A12: the pinned-nominal pattern, and "pinned" was only half true

**The site.** `dram_1t1c_write_zero_settles` carried its deadline as a
hypothesis. `dram_1t1c_write_zero_settled_at_2ns` now proves that at the
nominal instance and a 5 V supply, **two nanoseconds settle the storage node to
within 10 mV** — certified at split depth 8, axioms `[propext,
Classical.choice, Quot.sound]`.

**The constant closes a loop.** `dram_1t1c_nominal_decayRate` evaluates the
rate at `16000000000/3` per second, so **rate × 1 ns = 16/3 exactly** — the very
constant `DramBankCoreSpec.lean` proved by hand in seven bespoke lines before
the F2 kit existed. Two nanoseconds gives `32/3`, and `5 · (3/7)^8 =
32805/5764801`, comfortably under `1/100`.

### "PINNED-NOMINAL" WAS HALF RIGHT, AND THE HALF I MISSED IS THE LOAD-BEARING ONE

`analog-4` classified these decks as pinned-nominal, against `loaded_inverter`'s
corner box. `Dram1T1CExampleAllowed` does pin the **fabricated instance**
(`world.fabricated = dram1T1CNominal.instance`) — but its other conjunct is only
`Dram1T1CAdmissible`, which constrains the **environment** by
`threshold < supply` and nothing more.

> **The supply is free above 1 V, so the decay rate has NO uniform lower bound
> over the allowed set: as `supply → threshold⁺` the rate goes to zero.**

So the deadline cannot be discharged for *every* allowed world, and the
corollary carries `hsupply : world.environment.supply = 5` as an explicit
hypothesis. That is honest and it is weaker than `loaded_inverter`'s result,
which holds over its **whole** box.

> **A world is not "pinned" or "free"; each COORDINATE is. A deck can pin its
> fabricated instance and leave its environment open, and a classification that
> names the world rather than the coordinates will read the easy half and miss
> the binding one.**

This is the same error as `analog-4`'s repricing, one level finer: there I
generalised across decks from one deck, here I generalised across a world's
coordinates from one conjunct. **Both times the shape I checked was real and
the shape I skipped was the one that mattered.**

**Consequence for the remaining 7.** They are not "concrete-constant
arithmetic" as `analog-4` priced them. Each needs its environment coordinates
audited first: whichever are free must either be pinned by hypothesis (weaker
theorem, as here) or bounded like a corner (stronger theorem, as
`loaded_inverter`). **A12's real content is the pattern, not the count.**

**Next: A13 — `dram_sense_amp`'s 4 sites**, with the environment-coordinate
audit done FIRST this time.

**Iteration note.** Developed standalone against built oleans per the previous
landing's measurement: the rate identity and the full corollary each compiled
first try in the scratch loop, and the real files were built once. The one cost
was discovering that `Examples.spice.dram_1t1c.proof` had no olean yet — a
scratch probe against an unbuilt module fails on the import, not on the proof,
so the module has to be built once before the loop is worth anything.

---

## 2026-08-24-analog-6 — A13: the coordinate audit ran first, and found the gap somewhere else entirely

**The audit, as `analog-5`'s law requires.** `dram_sense_amp`'s sites all run
through `dramSenseWorld initialTrue initialComplement horizon`, which pins:

| coordinate | status |
| --- | --- |
| `fabricated` | **PINNED** — `dramSenseAmpLayout.fabricated`, thresholds 1 V, betas 1e-4, caps 3e-13 |
| `supply` | **PINNED at 5 V** — inside the world constructor |
| `initialTrue` / `initialComplement` | free, but coupled: `5/2 ± initialDeviation` |
| `horizon` | **FREE** |
| `required` | **FREE** (performance theorem only) |

**So the audit found FEWER free coordinates than `dram_1t1c`, not more.** Where
`dram_1t1c` leaves `supply` free above the threshold — the finding that forced
an explicit `hsupply` hypothesis — this deck pins it in the constructor. On the
coordinate axis, `dram_sense_amp` was the *easier* deck.

### AND THE BLOCKER WAS NOT A COORDINATE AT ALL

The audit was looking for a free parameter and found a **missing direction**.
`dramDifferentialSenseSmallSignalTrace initialDeviation time =
initialDeviation * exp (1000000000 * time)` — a **growing** exponential, because
a sense amplifier REGENERATES. Its `hsmall` hypothesis bounds that growth from
ABOVE, and the F2 kit had three of the four directions:

| direction | lemma | who needed it |
| --- | --- | --- |
| decay above | `exp_neg_le_of_pow_le` | every settling deck |
| decay below | `one_sub_div_pow_le_exp_neg` | two-sidedness |
| growth below | `one_add_div_pow_le_exp` | the `log` deadline |
| **growth above** | **absent until now** | **the sense amp** |

> **A kit built from settling circuits is complete for settling and silently
> missing a direction for regenerating ones. Decay and growth are not the same
> obligation with a sign flipped: bounding decay ABOVE and growth ABOVE need
> different lemmas, and only one of them falls out of `add_one_le_exp`.**

`exp_le_inv_sub_pow` closes it: `exp a ≤ (1/(1 - a/n))^n` for `a < n`, obtained
by inverting the growth-below bound. `dram_sense_amp_small_signal_realizable_at_1ns`
then discharges `hsmall` at a 100 mV deviation over one nanosecond —
`exp 1 ≤ (10/9)^10` at split depth 10, and `(1/10)·(10/9)^10 < 1/2`. Axioms
`[propext, Classical.choice, Quot.sound]`.

**The audit paid for itself by not finding what it was looking for.** Had I
started from the proof, the missing direction would have surfaced as a failed
`exact` deep inside a tactic block; starting from the coordinates surfaced it as
a property of the deck's *physics* — this circuit grows, the others shrink —
before a single tactic ran.

**Also found: `Circuit.Enclosure` was not in this module's import closure at
all.** Neither the new lemma nor the previously landed ones were visible from
`Examples/spice/dram_sense_amp/proof.lean`; the deck needed the import added.
A kit is only shared where it is imported, and three decks having it says
nothing about the fourth.

**Next: A14 — the remaining 8 siblings.** Every deck in the family now has a
worked exemplar, so these are instantiations rather than investigations. The
coordinate audit stays first, and the direction audit joins it.

---

## 2026-08-24-analog-7 — A14: F2 closes at 7/7, and the denominator it closed was not the one I had been quoting

**The last three certificates.** `dram_sense_amp_small_signal_behavior_at_1ns`
and `dram_sense_amp_small_signal_performance_at_1ns` discharge the remaining
obligations, the latter closing **two** at once — its `hsmall` by the growth
certificate at split depth 10, its `hdeadline` by the **deadline** certificate
at split depth 8 (`5/2 ≤ (9/8)^8`). Both directions of the kit, in one theorem.
The sense amplifier's performance claim — a 250 mV margin, inside the rail
domain, within one nanosecond, from a 100 mV deviation — now holds **outright**.
Axioms `[propext, Classical.choice, Quot.sound]` throughout.

The shared numeric facts are named (`..._cap_1ns`, `..._deadline_1ns`) rather
than inlined three times, and `analog-6`'s corollary was refactored onto them.

### THE DENOMINATOR

`N / 12` was wrong in four consecutive landings. The recount is in the standing
block above; the short version is that 12 counted library-internal occurrences
and six plain bounds, and the real figure is 7. **My first recount was also
wrong** — a regex that missed `loaded_rc` because its hypothesis nests
parentheses two deep, which is the third time in this lane a heuristic scanner
has produced a confident wrong number.

> **Three for three: the orphan-doc scanner accused two clean files, the
> `analog-4` repricing generalised from one deck, and the F2 denominator counted
> the wrong things. Every one was a MEASUREMENT taken with an instrument nobody
> had validated against a known answer. The instrument is part of the claim.**

### THE GATE CAUGHT MY OWN REGRESSION

Refactoring the `analog-6` corollary onto the shared lemma left its doc comment
attached to nothing. `harness/lean_comment_forms.py` reported
`ORPHAN DOC COMMENT …:783 — followed by '/-- The small-signal cap…', not a
declaration` **in under a second**, naming the line and what followed it.

> **The same defect class cost four tenures before the gate existed and one
> second after. A gate's value is not that it prevents the defect — I made the
> defect again — but that it moves discovery from the far side of an hour-long
> queue to the near side of a keystroke.**

### WHAT IS LEFT, AND WHAT IS NOT

F2 is closed. **The tier is not**, and the distinction is §9.0's waypoint law:
F4 still holds 88 sites, F3 eight, F5 two, F6 one, and F1 is unclosable by
construction and admitted 12×. What closing F2 buys is that **every settling
and regenerating claim in the corpus now rests on rational arithmetic rather
than on an assumed constant** — the tier's stated real-analysis frontier, and
only that.

**Next: A15 — F3 (unbalanced latch determinacy, 8 sites)**, which needs Grönwall
lifted from the scalar case to the 2-D pair field. That is the first item in
this lane's queue that is genuinely new mathematics rather than instantiation,
and the coordinate/direction audits go first.

---

## 2026-08-25-analog-8 — A15: F3 needed no new mathematics, and the audit is now 4-for-4 at overturning the census

**F3 was censused as "unbalanced latch determinacy — 8 sites — needs Grönwall
lifted from the scalar case to the 2-D pair field," and named as the first
genuinely new mathematics in this lane's queue. The audit says it is none of
those things.**

Three checks, before any proof was attempted:

* **Grönwall is already landed.** `LeanModels/Spice/LoadedInverter.lean:1401`
  applies Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` directly.
* **The scalar→2-D lift is already proved.**
  `dramDifferentialSenseNominalClampedPairRate_determinate`
  (`DramDifferentialSenseUnbalanced.lean:2175`) is a complete tactic proof over
  the pair field, and `..._nominal_unbalanced_determinate_on_domain` builds on
  it.
* **It is consumed and pinned.** `dram_sense_amp_vector_determinate_on_domain`
  uses it in `Examples/`, with a `#print axioms` pin showing the standard three.

> **The family was named for a lemma it already had. "Needs Grönwall" described
> the MATHEMATICS the theorem uses, not the WORK the theorem lacks — and a
> census that records the technique instead of the gap will price landed work
> as outstanding.**

**What F3 actually lacked was grounding.** Determinacy reads *any two
rail-domain trajectories agree*, universally quantified over the domain
premises — so it holds just as well of a deck no trajectory can satisfy.
`dram_sense_amp_determinacy_grounded_at_1ns` supplies the inhabitant from A14's
performance witness. **This is `2026-08-24-analog-1`'s two-link chain arriving at
a determinacy theorem**: the lane's founding finding and its latest rung are the
same finding.

`dram_sense_amp_determinate_at_1ns` instantiates the horizon. The domain
premises stay, correctly — they are properties of the two trajectories being
COMPARED, not of the deck — and the grounding theorem is what shows they are
satisfiable. Axioms `[propext, Classical.choice, Quot.sound]`.

### THE CENSUS SCOREBOARD, kept honestly

Four consecutive audits have overturned the thing they were sent to confirm:

| audit | expected | found |
| --- | --- | --- |
| A11 | monotone-on-box vocabulary applies | it does not; one `div_le_div₀` |
| A12 | decks are "pinned-nominal" | supply is FREE; each coordinate differs |
| A13 | a free coordinate blocks the sense amp | the KIT was missing a direction |
| A15 | F3 needs a Grönwall lift | Grönwall landed; F3 needed grounding |

Plus two bad denominators (F2's `12`, and the regex recount that missed
`loaded_rc`).

> **The F-family table was built once, early, from reading — and has been wrong
> about the FRONTIER every time it was checked against the tree. It was a fine
> instrument for finding where to look and a poor one for saying what is left.
> Re-derive a family from the tree at the moment you start it, never from the
> row that named it.**

### FOR THE COORDINATOR — the hold's premise does not hold for this lane

The ticket hold was issued because "your floor runs the register gate". **It
does not.** Verified three ways: `harness/divergence_register.py` appears
**zero** times in `tools/triad.sh` and **zero** times in `tools/ci.sh`; this
lane's `DEFAULT_FLOOR` is `docs_check; diff_test; refusal_census`; and the
`gates:` line in this lane's last tenure log reads exactly
`docs_check; diff_test; refusal_census; lean_comment_forms`. Its only callers
in the tree are `harness/sv_divergence_probe.py` and
`harness/pyc_divergence_probe.py`.

**The hold is being respected regardless** — a coordinator may hold tickets for
merge-side reasons that have nothing to do with a lane's floor, and that is the
coordinator's call, not this lane's. Surfacing the premise, not overriding the
instruction. This landing is committed and pushed but **NOT ticketed**; it will
be enqueued on signal.

---

## 2026-08-25-analog-9 — F4 COLLAPSES: 88 sites of "missing monotonicity" were one boundary, enforced once, already gated

**Re-derived from the tree before pricing, as the previous landing's law
requires. Nothing in the F4 row survived.**

| the row said | the tree says |
| --- | --- |
| 88 sites | **94** occurrences of `lambda := 0` — and they are the SUPPORTED constant being written, not work |
| needs `λ`-monotonicity of the square law | needs nothing: **no deck anywhere carries `λ ≠ 0`** (all 22 `.model` declarations are `lambda=0`) |
| 88 sites of outstanding proof | **11 refusal sites**, of which **1 is reachable** |

**λ ≠ 0 IS REFUSED, NOT UNPROVED.** `LeanModels/Circuit/Spice.lean:499` guards
`elaborate` — the `SourceCircuit → ElaboratedCircuit` step — with
`model.level == 1 && model.transconductance > 0 && model.channelLengthModulation
== 0 && …`. Every per-device projection (`toLoadedInverterNominal`,
`toDiffPairNominal`, `toCommonSourceNominal`, `toDram1T1CNominal`, and six
more) repeats the check, but each takes an `ElaboratedCircuit` whose models have
already passed it.

**Verified by instrument, not by reading.** A probe that mutates a real deck's
model and asks *which* error comes back:

    elaborate: REFUSED FIRST: MOS model `nmod` is outside the supported typed profile
      => the per-device lambda check never runs: UNREACHABLE

> **Ten of the eleven checks are DEFENCE IN DEPTH, not gaps. They are worth
> keeping — if the outer guard were removed they would catch it — but counting
> them as proof obligations prices a supported constant as outstanding work.**

**And the one live refusal was already gated**, twice, by
`dram_sense_amp_source_test.lean` and `dram_bank_256x32_source_test.lean` —
whose `withUnsupportedLambda` checks pass because ELABORATION rejects the deck,
not because the projection they name does.

### THE INSTRUMENT

`harness/spice/lambda_boundary_test.lean` makes the boundary a checked fact
across four decks — `loaded_inverter`, `diff_pair`, `cs_amp`, `dram_1t1c` —
twelve checks, all PASS: the committed deck is accepted, and both halves of the
named profile (`LAMBDA=0` **and** `IS=0`) are refused **at elaboration**.

**Both directions run.** Removing the mutation makes the same file exit 1 with
six FAILs, so the checks discriminate rather than always passing. The refusal
path is exercised, not admired.

**Prediction stated before building, and it held**: no defect would be found,
because the guard is a simple equality on a parsed field; the value is
converting a boundary *claim* into a boundary *check*. Zero defects found, nine
claims retired.

### THE SCOREBOARD IS NOW 5 FOR 5

| audit | expected | found |
| --- | --- | --- |
| A11 | monotone-on-box applies | it does not; one `div_le_div₀` |
| A12 | decks are "pinned-nominal" | supply is FREE; coordinates differ |
| A13 | a free coordinate blocks the sense amp | the KIT lacked a direction |
| A15 | F3 needs a Grönwall lift | Grönwall landed; F3 needed grounding |
| **F4** | **88 sites of missing monotonicity** | **a boundary, enforced once, already gated** |

> **Five families were priced from one early reading. Four were wrong about the
> frontier and the fifth did not exist. The row that names a family is a
> hypothesis about the tree, and it decays — because the tree moves and the row
> does not.**

**Minor finding.** `harness/spice/fixtures/{floating,isource_divider,single_r_across_v}.cir`
are referenced by nothing in the tree — three dead fixtures, F7's shape at the
harness layer.

### WHAT IS ACTUALLY LEFT

With F2 closed, F3 landed and F4 collapsed, the tier's remaining families are
**F5** (2 sites, AC for nonlinear devices), **F6** (1, interval width), **F7**
(dead surface, now 12 with the fixtures), and **F1**, unclosable by construction
and admitted 12×. **The lane's real frontier is much nearer than the F-table
said, and the honest next question is not which family to attack but whether
the tier's DENOMINATORS — 8/24 grounded, 4/21 circuits — are still the right
measure of what remains.**

---

## 2026-08-26-analog-10 — the AssuranceCase census: the tier was never 9/21, and the instrument now says so

**Prediction, stated before measuring** (the discipline that has now paid six
times): `8/24` unchanged but increasingly wrong; `9/21` badly understating the
tier; the right primary number near **19/21**.

**Measured: 20 / 20.** Every circuit carrying Lean has a non-vacuous behavior
guarantee. The prediction was off by one, and the miss is the finding.

### THE MISS: I PREDICTED BY COUNTING ONE IDIOM

I forecast 19 because I counted `..._realizable` twins. **`chain` has none** —
and is non-vacuous anyway, because `chain_contract` is an **iff**:
`LoadedChain sections input output current ↔ output = (2/3)^sections · input ∧ …`.
The reverse direction *is* the witness, constructively. Its
`#circuit_check chainSpecDeck dc shows "out3" = (2/3)^3 · 5` confirms it
independently by running the solver.

> **Non-vacuity has at least five idioms in this corpus. A `_realizable` twin
> is one; an exhibited observation is another; a `GroundedUnder` witness a
> third; an `ExhibitsUnder` existential a fourth; an iff whose reverse
> direction constructs the witness — or a computed operating point — a fifth.
> Counting the first and calling it the measure is precisely how `9/21`
> happened.**

### THE INSTRUMENT NOW COUNTS ALL FIVE, AND PROVES IT MATTERS

`harness/spice/assurance_census.py` enumerates the idioms explicitly and prints
which ones each circuit uses. Three circuits rest on a non-`_realizable` idiom
alone: **`chain`** (iff/computed-op) and **`and_gate`** and **`half_adder`**
(observation-exists — this lane's own A1 landing).

**Validated by ablation, not by inspection.** Cutting the idiom list back to
`_realizable` alone drops the figure to **17/20** and falsely flags exactly
those three. So the detector discriminates, and the size of the single-idiom
undercount is measured rather than asserted.

### THE SEVENTH INSTRUMENT ERROR, CAUGHT BEFORE IT WAS QUOTED

The first classification pass used a regex for "has a behavior spec" and marked
`cs_amp`, `diff_pair` and `chain` as having none. `cs_amp` alone has **28**
theorems including `_transfer`, `_gain`, `_swing`, `_dc_unique`. I caught it by
spot-checking three rows I found implausible, and then classified all 21 from
their actual theorem-name lists instead.

> **At 21 rows, hand-classification with the evidence quoted beats an
> unvalidated scanner — and the scanner only becomes trustworthy once it is
> ablation-tested against answers already known by hand.**

### WHAT THIS CHANGES

The tier is **not** a 9/21 tier with 12 circuits unguarded. It is a **20/20**
tier in which 9 circuits additionally carry the typed `AssuranceCase` bundle.
The remaining work was never coverage: it is bundling (11 circuits could gain
an `AssuranceCase`), plus F5's two sites, plus F1's permanent admission.

**F1 rides this number too**, unchanged: `model validity: MISSING`,
architecturally unclosable, admitted 12×. Twenty-of-twenty is a claim about
models, and none of it is evidence that a fabricated device matches one.

### F6 folded in — signed interval arithmetic

`add` and `mulNonnegative` were the whole algebra, and `mulNonnegative` requires
BOTH operands nonnegative — which a voltage difference or a gain is not.
`Enclosure.lean` now carries `neg`, `sub` and a sign-mixed `mul`, each with its
containment theorem.

The sign-mixed product is the only one with any content, and it needed no case
explosion: **a product over a rectangle attains its extremes at the corners
because it is monotone in each factor separately, the direction depending on the
sign of the other.** Four one-line lemmas (`mul_le_max_left`, `min_le_mul_left`
and their right-hand twins) say exactly that, and `mul_contains` composes them
without a single `nlinarith`.

**One measurement worth recording.** The first probe of `mul_contains` was
killed by my own tool timeout at 400 s and read like a hanging proof; the same
file compiled clean in the background. It was `nice -n 19` on a machine another
lane was building on. **A proof that times out under `nice` on a loaded machine
has not failed — and the two look identical from the exit code.**

---

## 2026-08-26 — PARKED (indefinite). Read this first on resumption.

**Thomas paused the campaign to save tokens and free Lean resources.** This
entry is the lane's hand-over. Nothing below is in flight; nothing is
half-edited; the working tree is clean.

### STATE OF THE NUMBERS

| number | value | how to reproduce |
| --- | --- | ---: |
| **primary — non-vacuous behavior guarantees** | **20 / 20** | `python3 harness/spice/assurance_census.py` |
| secondary — `AssuranceCase` bundling | 9 / 20 | same command, same denominator |
| grounded assurance cases | 8 / 24 | same command |
| declared divergences | **0** | F1 is a boundary, not a debt |

**Reproduce these, do not quote them.** The detector recognises **five**
non-vacuity idioms and is **ablation-tested**: cutting it back to
`_realizable` alone yields 17/20 and falsely flags `chain`, `and_gate` and
`half_adder`. That ablation is the reason to trust the 20, and re-running it is
the cheapest way to confirm the instrument still discriminates.

**F1 rides every one of these numbers**: `model validity: MISSING`,
architecturally unclosable, admitted 12×. All four figures are claims about
models; none is evidence a fabricated device matches one.

### WHAT IS DONE

F2 closed 7/7 · F3 landed (it needed grounding, not Grönwall) · F4 collapsed
(a boundary, enforced once, already gated) · F6 closed (signed interval
arithmetic) · the comment-forms gate is campaign infrastructure · the λ
boundary is a checked fact across four decks.

### WHAT IS NEXT, AND THE WARNING THAT COMES WITH IT

**F5 — 2 sites**, `ExactLinearizationAt` in `Circuit/AC.lean` and
`Spice/LoadedRCAC.lean`, wanting an `ApproxLinearizationAt` with a Taylor
remainder.

> **RE-DERIVE F5 FROM THE TREE BEFORE PRICING IT. I would expect the row to be
> wrong again.**

Five consecutive family audits overturned the row that named them, and the F5
row comes from the same early reading as the four that failed. The specific
question to ask first is not "how do I prove the remainder bound" but "does the
tree already have it, and is the gap somewhere other than where the row points"
— which is what F3 and F4 both turned out to be.

Also open, priced but unscheduled: **11 circuits could gain an `AssuranceCase`**
(bundling, not coverage); **F7's dead surface**, 12 items, one paragraph already
written on what deletion would require — *not* a cleanup landing uninvited.

### ONE TENURE CERTIFICATION IS PENDING

`f5918694f145723c4b8a48b4124f77807b88ec91` (branch `analog-census`) carries the
census + F6 and is **pushed but never certified**: its ticket was cancelled by
Thomas's wind-down instruction while queued at depth 7, never having acquired
the lock. Every gate passed locally — `docs_check`, `lean_comment_forms` (408
files, 0 defects), `backlog-index --check`, and a scoped
`lake build LeanModels.Circuit.Enclosure` — but **local green is not a triad
green**, and this lane does not bank one as the other.

**On resumption, re-ticket that sha before treating its contents as landed.**
The build was deliberately scoped to `Circuit.Enclosure`, `Circuit` and
`Examples.spice.dram_sense_amp.proof` — the two modules that import Enclosure,
so the green covers importers, not just the changed file. Keep
`dram_bank_256x32` out of this lane's build sets permanently; its elaboration
cost is its own lane's to price.

### THE LANE'S OWN LAW, FOR WHOEVER PICKS IT UP

> **The row that names a family is a hypothesis about the tree, and it decays —
> because the tree moves and the row does not.**

Seven instrument errors in this lane were caught by validating a scanner against
answers already known by hand. None was caught by reading the scanner. If you
resume by trusting a number in this file that you have not re-run, you will be
the eighth.
