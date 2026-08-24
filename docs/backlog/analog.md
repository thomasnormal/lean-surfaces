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

## SPEC COVERAGE — the completion metric (standing; updated every landing)

Reproduce it, do not quote it:

    python3 harness/spice/assurance_census.py

**The denominator counts what could have DISAGREED** (§9.0(a)). For this tier
that is not "theorems proved" but "premise sets shown to be inhabited", because
every obligation in `AssuranceCase` is universally quantified over `allowed`.

| landing | sha | grounded assurance cases | circuits fully grounded | circuits with any case |
| --- | --- | ---: | ---: | ---: |
| pre-lane baseline | `ed9f1f5` | 0 / 24 | 0 / 21 | 9 / 21 |
| `2026-08-24-analog-1` | *(next commit)* | **8 / 24** | **4 / 21** | 9 / 21 |

**TWO DENOMINATORS, and the gap is the point.** The table above counts
`AssuranceCase` declarations, which only 9 of the 21 circuits use. The other 12
carry proved behavior specs in the lane's older house style — a universal
theorem paired by hand with a `..._realizable` twin — and those are not worse,
they are unbundled. Against the corpus rather than the bundle:

* **19 / 21 circuits have a proved behavior spec.** `gnd_alias` is a parser
  regression fixture with no Lean file at all, and is out of the denominator by
  construction rather than by omission. `and_gate` is the one live gap (below).
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
| F4 | channel-length modulation, `LAMBDA ≠ 0` | 88 | monotonicity of `β/2·(vgs−vt)²·(1+λ·vds)` for `λ > 0` on `vds < 1/λ` |
| F3 | unbalanced latch determinacy / convergence / restore | 8 | Grönwall/ODE uniqueness lifted from the scalar case to the 2-D pair field |
| F1 | physical-envelope coverage (model ↔ fabricated device) | 19 | **none — not closable in Lean** |
| F7 | dead framework surface (carriers with zero suppliers) | 9 | nothing; the stated architecture is wider than the discharged one |
| F5 | small-signal AC for nonlinear devices | 2 | an `ApproxLinearizationAt` with a Taylor remainder bound |
| F6 | interval-arithmetic width | 1 | `sub`, `div`, sign-mixed `mul` in `Enclosure.lean` |
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

---

### THE OPEN QUEUE, censused and priced

**A1 — `and_gate` has no realizability twin, and its sibling proves the exact
missing lemma.** `cmos_and_mos1_correct : Mos1BinaryGateContract …` is purely
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
