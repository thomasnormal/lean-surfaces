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

**F1 RIDES THIS TABLE AND IS NOT OPTIONAL** (coordinator ruling): `model
validity: MISSING`, architecturally unclosable, admitted 12×. The numbers above
are model-level throughout; none of them is evidence that a fabricated device
matches its model.

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
