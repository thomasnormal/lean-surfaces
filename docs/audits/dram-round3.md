# DRAM lane audit — round 3 (bank 256x32 transient/sense work)

**Date:** 2026-07-30. **Scope:** the uncommitted working tree vs `ccd7951` ("DRAM bank
256x32: differential sense, source-derived projection, physics-pure behaviors") —
~18,700 changed lines across `LeanModels/Circuit/`, `LeanModels/Spice/Dram*`,
`Examples/spice/dram_bank_256x32/`, plus untracked library files and
`Examples/mixed-signal/dram_refresh/`. **Method:** four independent adversarial
auditors, one per standing lens (vacuity/realizability; spec-in-behavior;
dynamical-semantics soundness + sense-margin residual; ground-truth/gate integrity).
All satisfiability, tautology, and budget probes were **compiled against the kernel**
(every probe closes with only `propext, Classical.choice, Quot.sound`); all six DRAM
CI gates were re-run live during the audit.

**Verdict: the lane is going as planned — the strongest round yet.** No blockers, no
soundness holes, zero `sorry`/extra axioms anywhere in the diff. The vacuity and
spec-in-behavior failure modes caught in rounds 1–2 are structurally absent. The
findings below are ordered by what should happen before this work lands.

---

## 0. Tree state (fix first)

**T-0.** The working tree is currently red: `Examples.spice.dram_bank_256x32.proof`
fails at `proof.lean:10120:17` with unknown constant
`dram_bank_256x32_sense_transient_equation_manifest` — the constant exists nowhere in
the tree (checked by grep). It arrived with edits made after the last full-check
pass. Define the manifest or drop the reference.

**T-1.** Note for rebase: the Python benchmark landed beneath this work as
`1994be0` (touches only `Examples/python/bench_*`, `docs/benchmark.md`,
`harness/cases.json`, `AGENTS.md` — no overlap with the SPICE write set).

## 1. MAJOR findings

**M-1 — Six 45 ns theorems have an unwitnessed, likely-empty hypothesis set
(twin-law violation).** `…switched_reaches_{margin,logic_bands}_of_scalar_{region,
progress,rate}_certificate` and `…of_source_progress_certificate`
(`Examples/spice/dram_bank_256x32/spec.lean:1488, 1523, 1559, 1594, 1629, 1786`)
each hypothesize a rate certificate plus a budget
`progressUpper − progressLower < minimumRate · (45 ns − 20.1 ns)`. No witness meeting
the budget exists anywhere in the development, and the only concrete certificate
(`dramSenseRestoreNominalHalfPicocoulombFourVoltRateCertificate`) **kernel-provably
fails it** by roughly 320×. The honestly proved resolution horizon is 10.1 µs
(`spec.lean:1717`), which is properly twinned. These six read as "logic bands within
45 ns" but are conditional on an unexhibited numeric certificate — exactly the
pattern the realizability-twin law exists to catch, softened here by honest
docstrings. *Fix:* exhibit a checked certificate meeting the 24.9 ns budget, or
demote/restate at the proven horizon, or move to a clearly-marked interface module.

**M-2 — The precharge behavior's device anchor is proved but never consumed.**
`dramPrechargeField` (`LeanModels/Spice/DramPrecharge.lean:69-84`) is a hand-written
polynomial in `max 0 (Vref − v)` — a target-referenced paraphrase, not the primitive
MOS1 current (contrast `DramWrite.lean:59-64`, which is definitionally
`−mos1TerminalCurrent/C` and is the pattern to copy). The bridge lemmas
`dramPrechargeField_eq_mos1` (`:152`) and `nominalDramHighPrechargeField_eq_mos1`
(`:1089`) prove the anchor — but repo-wide grep shows **zero consumers** of either.
If the field drifted from the device law, only the decorative bridge would fail;
every settling/endpoint theorem would keep compiling. Sharpened by: the bridge holds
only under `DramPrechargeAdmissible` and `bitline ≤ Vref`, yet bank-level programs
(`DramBankCore.lean:319`, `DramBankFrontEnd.lean:46,383`) instantiate
`DramPrechargeBehavior` with source-projected worlds and no admissibility guard.
*Fix:* define the field from `mos1TerminalCurrent` on the operating domain and derive
the polynomial as a theorem; or route realizability/determinacy through the bridge;
plus a check that `_eq_mos1` bridges have consumers.

**M-3 — The precharge evolution clause bakes in solution smoothness.**
`DramPrechargeProgram.evolution` (`DramPrecharge.lean:127-131`) conjoins
`SmoothBehavesOn` (a classical derivative at *every* time) onto `ACBehavesOn`. That
is a solution-regularity assumption, not physics, so every universal precharge
theorem (`nominalDramPrecharge_determinate :740`, `…_behavior_eq_trace :843`,
`…_zero_ten_ns_settles :1013`) quantifies over a strictly smaller class than the
physical AC solutions. DramWrite proves the identical results for AC-only behaviors
via its FTC bridge (`dramWrite_nominal_hasDerivWithinAt`, `DramWrite.lean:659-743`),
so the conjunct is removable. *Fix:* drop `SmoothBehavesOn` and port/generalize the
FTC bridge.

**M-4 — "Unbalanced" means state offset, not device mismatch; intra-latch mismatch
is currently inexpressible.** Every theorem in
`DramDifferentialSenseUnbalanced.lean` pins
`world.fabricated = nominalDramDifferentialSenseInstance`, and
`DramDifferentialSenseInstance` (`DramDifferentialSense.lean:168-183`) carries a
*single* `nThreshold/pThreshold/nBeta/pBeta` shared by both cross-coupled halves
(only the capacitances are per-side) — so a threshold/β mismatch between the two
halves of the latch cannot even be stated. This bounds what "sense margin" can mean
until the structure is widened. *Fix (next increment for this lane):* per-device
parameters in the instance structure, then re-derive the resolution theorems with a
mismatch budget.

**M-5 — No CI gate on theorem strength; a `sorry` regression would pass.** The
adversarial gates guard the projection/matcher functions (and do that well — see §4);
`lake build` treats `sorry` as a warning and exits 0; the 150 `#print axioms` lines
only print. Nothing in `tools/ci.sh` fails on `sorryAx`/`ofReduceBool` in exported
theorems. *Fix:* a small axiom-set assertion step (grep the build log for
`uses 'sorry'`, or a `lake env lean` script over the exported theorem list).

**M-6 — Tracked docs cite untracked files.** The library core of this round —
`LeanModels/Spice/DramBankSwitched.lean` (~9,100 lines) plus
`DramBankFrontEnd/ChargeSharing/Protocol/SenseRestoreSpec.lean` — and
`Examples/mixed-signal/dram_refresh/` are untracked, while the modified tracked docs
(`docs/circuit-assurance-architecture.md`, `docs/circuit-spec-surface.md`) already
name them as landed. A commit that misses the `git add` ships docs pointing at
nothing and an example a fresh clone cannot build, and no gate would notice. *Fix:*
stage them in the landing commit; optionally assert doc-referenced example paths
exist in CI.

## 2. Minor findings

- **m-1.** Spec-meaning-bearing definitions live in `proof.lean` — the
  `Allowed`/`Specification`/`Domain` predicates and certificate structures that give
  the marquee statements their meaning (e.g. `proof.lean:422`, `:8305`). The trusted
  reading surface should not extend into a 12k-line proof file; move them to
  `spec.lean` (defs are allowed there) or the library.
- **m-2.** 19 of 169 spec theorems are missing from the `#print axioms` audit block
  (`spec.lean:3364-3513`), including `switched_column_transient_realizable`.
- **m-3.** `dram_bank_256x32_coupling_transient_stays_in_domain` (`spec.lean:2837`)
  bounds only the canonical `nominalDramSenseCouplingBoundary`, not all behaviors —
  rename or derive universally via determinacy.
- **m-4.** Dead parallel definitions bypass the provenance mechanism:
  `DramPrechargePhysicalBehavior`/`DramPrechargeSmoothBehavior`
  (`DramPrecharge.lean:92-106`, unused raw lambdas outside `EquationProgram`) and
  `DramWriteAdmissible` (`DramWrite.lean:51`). Delete or route through the program.
- **m-5.** DramPrecharge has no spec/physics file split (DramWrite does); a
  `DramPrechargeSpec.lean` would keep the audit surface uniform.
- **m-6.** The headline `3/22 V` bank margin runs through the legacy exactly-settled
  `DramCellChannelSettled` clause (`DramCell.lean:703-708`) — quasi-static endpoint
  algebra in the behavior, clearly labeled and realizably discharged, with the
  genuinely transient path (`DramCellFiniteChargeSharingCertificate`, `1/11 V` after
  a derived deadline) in parallel. Migrate the headline to the transient path when it
  matures.
- **m-7.** All sense-chain margins/rates are numeric literals at nominal parameters
  (3/22, 1/11, 1/30 V, …). The symbolic capacitance law exists
  (`dramCell_shared_voltage`), but no sense-connected theorem states the margin as a
  function of `C_cell`/`C_bitline`.
- **m-8.** CI runs only half the ngspice bank polarity matrix (read-of-1, write-of-0;
  `--full` adds the other two, `tools/ci.sh:62` doesn't pass it), and a doc sentence
  claims both polarities are exercised. Pass `--full` or soften the sentence.
- **m-9.** `Examples/system-verilog/*.sv.json` is not a lakefile `input_dir`, so on
  cached builds an edited envelope does not re-elaborate its consumers — and the new
  mixed-signal example is the first proof composing across that unprotected channel
  (the `.cir` channel has exactly this protection). Add the input_dir.
- **m-10.** The mixed-signal composition example (no in-directory source artifact; it
  re-verifies upstream artifacts from other example dirs) is a reasonable shape but
  formally undocumented — amend the AGENTS.md layout law with a composition-example
  clause. Also `spec.lean` importing `LeanModels.Sv.Tests` is a smell.
- **m-11.** Adversarial mutants index the deck by position (`subcircuits[6]`,
  `set! 13`); a re-ordered generator would silently retarget the scenarios. Derive
  indices by name lookup.
- **m-12.** `toSenseRestoreInstance`'s `[column.val]?.getD 0` would yield 0 F on an
  index miss; unreachable given the size checks, but a lemma pinning
  `bitlineCapacitances.size = columns` at projection time closes it by construction.
- **m-13.** Stale header: `DramDifferentialSenseSpec.lean:14` still lists
  "unbalanced … trajectories" among open obligations — now proved; refresh so the
  file doesn't understate the round.

## 3. Sense-margin residual: PARTIAL (honestly documented, not renamed)

1. **Unbalanced-trajectory coverage — CLOSED.** Arbitrary common-mode error, any
   positive delivered margin: existence via Picard–Lindelöf witnesses, barrier
   invariance, determinacy/uniqueness, and a *derived* finite deadline
   (compact-minimum rate certificate). Strict-order preservation is proved by swap
   symmetry + backward uniqueness, not an assumed invariant.
2. **Offset quantification — PARTIAL (signal-side only).**
   `dramRefresh_chargeSharing_robust_to_input_offset`
   (`DramRefreshLoop.lean:217`) is a genuine ∀-offset theorem with the `1/30 V`
   budget proved from charge conservation — but the offset is subtracted from the
   delivered signal; it never enters the latch DAE.
3. **Device-mismatch latch — OPEN**, blocked on M-4, and the docs say so verbatim
   ("mismatched-device and offset coverage remain intentionally open").

## 4. What is solid (verified, not just claimed)

- **Semantic foundation.** Time is `ℝ`; behaviors are absolutely-continuous
  trajectories satisfying the DAE residual almost everywhere; results go through
  Mathlib FTC, Grönwall, Picard–Lindelöf. The classic hole is absent: no hypothesis
  quietly assumes existence/settling anywhere in the audited files —
  `SettlesWithin` occurs only as a proved conclusion, and concrete trajectory
  witnesses + uniqueness are proved (`…nominal_unbalanced_realizable`,
  `ODE_solution_unique`). Backward-Euler machinery is explicitly quarantined from
  the continuous physics.
- **Non-vacuity, kernel-checked.** Auditor probes instantiated the flagship
  hypothesis sets at a concrete non-degenerate world (checkerboard pattern, row 17,
  column 11) and showed the sign specification is *falsifiable* on an allowed world.
  Marquee theorems quantify over fully symbolic 256×32 contents and addresses.
- **Tautology resistance.** The write/precharge/eq-trace marquee theorems all
  resist unfolding-only proofs (compiled attempts fail leaving genuine ODE goals);
  premise-retrieval trails for the write and restore chains reach `mos1ForwardCurrent`.
- **Gates.** All six DRAM gates re-run and pass; the adversarial suites are real
  mutation tests (aliased nodes/zeroed caps/retargeted couplings rejected; parameter
  edits shown to *flow through* to projected profiles); the 256×32 projection is
  kernel-checked against the full hierarchical deck (all templates × all instance
  wirings, 331-port header) with a byte-level generator tie; ngspice cross-checks the
  kernel-proved 29/11 and 25/11 charge-sharing rationals.
- **Docs honesty.** ~25 sampled identifiers/constants in the new doc text all exist
  and match (including the 10.1 µs horizon, the exponential-envelope constants, and
  the equation manifests); staging caveats are disclosed rather than papered over.
- **Proof content.** `proof.lean` is parametric analysis (ε-slope barriers,
  Grönwall envelopes, time-shifted ODE reductions) with zero per-column clone
  families. The Mos1 additions are three fully-proved passivity lemmas, consumed by
  the rail-barrier proofs.

## 5. Suggested landing order

1. T-0 (unbreak the build) and M-6 (stage the untracked core) — before anything else.
2. M-1 (witness or demote the six 45 ns theorems) — the only finding that touches
   what the theorems *say*.
3. M-2 + M-3 (re-anchor the precharge field; drop the smoothness conjunct) — no
   theorem statements change.
4. M-5 (theorem-strength CI gate) — cheap, closes the regression channel.
5. The minor tail, then M-4 (per-device mismatch) as the next real increment.
