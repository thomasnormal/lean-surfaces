# SYNTHESIS — Literature Review for the CV32E40P Program

Synthesized from four area reports in this directory: `temporal-spec-methods.md` (A),
`areaB-processor-correctness.md` (B), `area-c-isa-models.md` (C),
`area-d-compositional-verification.md` (D). Evidence levels are carried through
honestly: **[read]** = primary text or source code read substantially by the area
reviewer; **[secondary]** = read via faithful restatements / cross-corroborated
summaries; **[skimmed]** = abstract/search-grade only.

---

## 1. THE ADOPTION MATRIX

Every USEFUL-ADOPT and load-bearing USEFUL-IDEA-ONLY item, ranked by value/effort
(best deals first). Landing zones: **gallery** = `docs/sv-spec-surface.md` vocabulary
/ spec prelude; **sv_vcgen** = module-contract / VC-generation design deltas;
**ISA model** = the Lean RISC-V golden model; **phase-2** = the core refinement
proof tier; **harness** = differential-testing / falsifier infrastructure.

| # | Method | Source (evidence) | What we take | Where it lands | Effort | Value — the one-sentence argument |
|---|---|---|---|---|---|---|
| 1 | History variables, named | Abadi & Lamport, TCS 82(2) 1991 [skimmed]; Lamport & Merz, "Prophecy Made Simple," TOPLAS 44(2) 2022 [read, D] | Name the `n_q`-style latch (gallery ex. 10) as a history variable; add "does this proof need a fresh history field?" as an explicit checklist item, backed by their existence theorem | gallery + sv_vcgen design notes (D2/D4) | S | Areas A and D independently converged on this: it converts a recurring ad-hoc design move we already make into a principled rule with a completeness theorem behind it — the cheapest high-value item on the list. |
| 2 | Register-boundary-breaks-circularity lemma | McMillan, CHARME'99 (LNCS 1703); Rushby, SRI CSL TR Sept 2001 PVS mechanization [read via Rushby + Namjoshi–Trefler TOCL'10 restatements] | The `p ▷ q := ¬(p U ¬q)` "constrains" operator and its strong-induction-on-time soundness proof as *the* composition rule for stage contracts; a register boundary supplies exactly the t→t+1 offset `▷` needs, a combinational loop cannot state `▷` at all | sv_vcgen (contract composition rule) | S–M | This is the precise theorem our settled register-cut discipline was implicitly leaning on, and Rushby's PVS script shows the induction is a few lines once stated correctly — not a research project. |
| 3 | Semantic-bucketed ISA AST | Carneiro guidance in leanprover Zulip "RISC-V ISA in Lean" thread; LNSym (AWS, hand-written Arm-in-Lean); riscv-coq (MIT-PLV) [all read, C] | ~5 orthogonal semantic constructor families (branch/jump/arith/load/store…) instead of one constructor per opcode; hand-written in our idiom | ISA model | S (design decision, made once) | Independent confirmation from people with no stake in our project that opcode-per-constructor encodings fight the prover (quadratic `no_confusion`) and that orthogonality is the remedy — free to adopt, expensive to retrofit. |
| 4 | WARL `legalize_*` function shape | sail-riscv `sys_regs.sail` / `sys_control.sail` [read, C] | Small, named, config/extension-gated `legalize_<csr>` functions per CSR and a `getPendingSet`/`dispatchInterrupt`/`trap_handler` split for interrupt dispatch — the *shape*, with field values re-derived for priv-spec v1.11 | ISA model | S | The RISC-V golden model's own idiom for exactly the CSR/interrupt semantics CV32E40P needs, adoptable as structure without inheriting the version-skew risk. |
| 5 | Oracle-legality non-vacuity witness | GR(1) realizability (Bloem et al., JCSS 2012) [skimmed, A]; Interface Automata ∃-compatibility (de Alfaro & Henzinger, ESEC/FSE'01) [skimmed, D] | A cheap "some σ satisfies the legality predicate" lemma, plus later "CV32E40P's OBI port is compatible with at least the reference subordinate" as a paired non-vacuity witness | gallery (ScheduleOracle) + sv_vcgen (BusOracle) | S | The project has been bitten by vacuous soundness-shaped theorems twice in the SPICE lane already; GR(1)'s realizability check is the same discipline with 20 years of pedigree. |
| 6 | RVFI order-tag + effect-tuple retirement spec | riscv-formal `docs/rvfi.md` [read, B] | Strictly monotonic, gap-free retirement order tag + full per-commit effect tuple (rd/mem/trap/intr), restated as an ordinary port-level `Sv.onPosedgeIdx` predicate — *not* the literal wire bundle | sv_vcgen (controller contract) + harness (RVVI-style lockstep diff) | M | The order-tag makes "exactly-once retirement" hold by construction of the observable rather than as a separate theorem, and the rich tuple is precisely what a PC-only observable (OOPSLA'25's choice) provably misses. |
| 7 | MAETT-style in-flight validity ghost bit | Sawada & Hunt, CAV'97 / FM9801 [secondary, B]; cv32e40p issue #509 [read, B] | A per-in-flight-instruction "still valid to commit?" ghost bit threaded explicitly through the interrupt-retraction and debug-entry paths, checked at every stage transition | sv_vcgen (controller contract) + phase-2 | M–L | Issue #509 (stall + retracted interrupt + debug entry ⇒ wrong instruction executed) is exactly the bug class this ghost discipline exists to catch and that flushing-style or PC-only proofs are structurally blind to. |
| 8 | Assume-guarantee stage-cut template | Chen et al. (NCKU), DVCon, "Automate and Accelerate RISC-V Verification by Compositional Formal Methods" [read, B+D] | The `M ∥ A ⊨ P`, `N ⊨ A` ⟹ `M ∥ N ⊨ P` split at pipeline-stage boundaries, with former internal taps becoming ports of sub-module contracts | sv_vcgen (module contracts) | M | The only published precedent of anyone compositionally verifying a controller-like RISC-V sub-module, and it independently converges on the same stage-boundary granularity we planned — validation plus a concrete template. |
| 9 | `ScheduleOracle.machineClosed` obligation | Lamport, "Safety, Liveness, and Fairness," 2019 note [read, A]; Wan, J. Appl. Math. 2014 [skimmed — read only if/when proving it] | State (and eventually prove) that every finite σ-legal prefix extends to a σ-legal infinite schedule | gallery (oracle metatheory) | M | Without machine closure, "fairness bundled into oracle legality" can silently exclude real runs and every ∀σ theorem overclaims — this is the one checkable obligation that makes our settled position sound rather than sloganized. |
| 10 | Sail as validation oracle, not term source | sail-riscv + Sail C/OCaml emulator [read, C] | Differential-test our hand-written ISA model against the Sail emulator's concrete traces (same pattern as Xcelium for the SV lane); transliterate the fiddly bit-tables (CSR layouts, exception codes, interrupt priorities) from readable Sail *source*, BSD-2 with attribution | harness + ISA model | M | Gets us the RISC-V-International-blessed model's error-catching power with zero of its 175K-line generated-Lean legibility cost. |
| 11 | Bounded token progress measure | Choi/Kim/Kang OOPSLA'25 artifact, `Sim.v:288–441` [read from Rocq source, B] | "Progress" as a well-founded decreasing natural-number token carried *inside* the simulation invariant, not a separate temporal layer | phase-2 (refinement invariant shape) | M | The field's newest kernel-checked pipeline refinement proves its advertised "progress guarantees" exactly our way (concrete bound, no unbounded eventually) — reuse the invariant shape rather than rediscover it. |
| 12 | Per-opcode leaf-module proofs | Centaur/Slobodova ACL2 line [secondary, B] | One theorem per opcode against a bit-precise arithmetic spec for execute-stage functional units (ALU, mult, alu_div) | phase-2 (leaf tier) | M | The closest industrial precedent to our bottom-up leaf plan, with the famous "kernel proof caught what simulation missed" FP-adder origin story as ammunition. |
| 13 | Prophecy variables — parked, pre-flagged | Lamport & Merz, TOPLAS 2022 [read, D] | A one-paragraph flag in sv_vcgen notes: speculation/flush ghost state ("will this load be flushed by a later mispredict?") is a prophecy-variable problem; exactly-once tagging is not (history suffices, prefix-computable) | sv_vcgen design notes (D7/P5) | S | Knowing in advance which ghost-state needs are history-complete vs. prophecy-requiring turns a future surprise into a scheduled decision — and the diagnostic (prefix-function vs. suffix-function) is one sentence. |
| 14 | WF/SF fairness naming | Lamport 2019 note [read, A] | The names WF/SF (infinitely-enabled ⇒ infinitely-taken, etc.) for whatever fairness clauses oracle legality carries | gallery vocabulary | S | Free interoperability with 30 years of literature when writing the legality predicate for arbiter-class examples (gallery #19). |
| 15 | `∀`-environment framing citations | Module Checking (Kupferman–Vardi–Wolper, CAV'96/I&C 2001); Reactive Modules (Alur–Henzinger, FMSD 1999); I/O automata (Lynch–Tuttle 1989) [all skimmed, D] | The BusOracle design note's citation spine: adversarial 2-player framing for ∀σ; internal/external nondeterminism split; fairness-bundled-with-component as the oldest precedent. Reactive Modules is worth a primary read before the legality predicate is frozen | sv_vcgen (BusOracle design note) | S (M with the RM read) | No single paper is "BusOracle," but this composite is the principled answer to "why ∀-environment, why fairness in legality" — cheap to cite, expensive to re-derive from scratch under review. |
| 16 | Fixpoint-polarity decision for `Sv.eventually` | Coupet-Grimal, J. Logic & Comput. 13(6) 2003, `coq-contribs/ltl` [skimmed, A] | Deliberately decide induction-vs-coinduction polarity for the unbounded fallback combinator by comparison with the closest prior trace-combinator library | gallery (spec prelude) | S | Our `Nat → State` representation makes bounded response fixpoint-free — the polarity question only bites the unbounded corner (gallery #19), and deciding it deliberately costs an afternoon. |
| 17 | Deadline-helper idiom checklist | Konrad & Cheng, ICSE 2005; Dwyer–Avrunin–Corbett, ICSE 1999 [skimmed, A] | Pattern names (Bounded Response, Bounded Invariance, Bounded Existence, Response Chain…) as a coverage checklist when naming future `Sv.*` deadline helpers | gallery vocabulary | S | Empirically ~80% of industrial requirements fall in this catalog — a free completeness check on our combinator vocabulary. |
| 18 | Position-defense citations for bounded response | Jahanian–Mok RTL (TSE 1986); RTCTL (Emerson et al., CAV'90/RTS'92); Kupferman–Vardi + BMC completeness thresholds [all skimmed, A] | The docs paragraph: 35 years of real-time-systems precedent for bound-first specs, plus the formal reason finite-state liveness is secretly bounded — with the honest ∀-width caveat (see §3.1) | docs / positioning | S | When a reviewer asks "why not `s_eventually`," this is the answer with citations rather than taste. |
| 19 | Interface-automata vocabulary | de Alfaro & Henzinger, ESEC/FSE'01 [skimmed, D] | Input/output/internal alphabets and the alternating-refinement direction (weaker input assumptions, stronger output guarantees) for stating contract refinement order | sv_vcgen (contract definitions) | S | The standard vocabulary for the contravariant/covariant refinement shape our stage contracts need; we reject its ∃-compatibility as a correctness notion (§3.4) but keep the words. |
| 20 | Monitorability scoping citations | Bauer–Leucker–Schallhart, JLC 20(3) 2010; Havelund–Roşu, TACAS'02 [skimmed, A] | The pre-emptive scope-limiting argument for what a future `#sv_check`-style online oracle could ever certify for unbounded SVA | docs / future harness | S | Not needed for the current bounded fragment; saves a future argument about why `s_eventually` can't be simulation-checked. |
| 21 | Fairness-in-AG "problem we avoid" citation | Cohen–Namjoshi–Sa'ar, CAV 2010 [intro read, D] | Cite as evidence that folding global fairness into local per-module AG proofs is known-hard, and our oracle-legality design sidesteps it by construction | docs / BusOracle note | S | Turns a design choice into a documented avoidance of a published hard problem. |
| 22 | Safety-progress classification | Chang–Manna–Pnueli hierarchy [skimmed, A] | Name where `⊨sva`'s fragment sits (guarantee class) in docs | docs | S | Vocabulary only; our shallow embedding gets the classification for free by inspection. |

Explicitly **not** adopted (for the record): Burch–Dill flushing and Velev–Bryant
(single-instruction abstraction, blind to the multi-instruction interaction bugs
CV32E40P actually had — B [secondary]); Kôika as a correctness precedent (no ISA
theorem exists for its RV32I core; secondary summaries claiming otherwise did not
survive reading the paper — B [read]); Silver/Lutsig's verify-by-construction
(opposite of our verify-as-written commitment; its "Interrupt" is a synchronous
ECALL-like instruction, not async-interrupt prior art — B [read]); MTL/MITL
dense-time apparatus (solves problems discrete cycle time doesn't have — A
[skimmed]); GR(1) synthesis machinery (we prove, not synthesize — A [skimmed]);
TLM refinement literature (our `Sv.transaction` already operates a tier above it —
D [skimmed]); importing sail-riscv-lean as theorem-facing terms (§2).

---

## 2. THE ISA VERDICT: BUILD (validate against Sail, harvest its tables)

**Recommendation: hand-build** a small, orthogonal RV32IM(C) + Zicsr, M/U-mode-only
ISA model directly in Lean, sized to exactly what CV32E40P implements (privileged
spec v1.11), in the semantic-bucketed AST style (matrix #3), with the Sail-shaped
CSR/interrupt function structure (matrix #4). Evidence grade: this verdict rests on
**first-hand artifact inspection** (Area C cloned `opencompl/sail-riscv-lean`,
`rems-project/lean-sail` v5, and sparse-checked `riscv/sail-riscv`, and read the
generated Lean, build logs, and CI config directly), not on abstracts.

**Why import loses**, despite the Sail→Lean backend being real, live (daily cron
regeneration from sail-riscv master, CI-green `lake build`, 135/135 targets, commit
from the day of review), credibly staffed (Grosser/Stefanesco/Galois/LindyLabs with
original Sail authors consulting), and funded (Ethereum Foundation Verified zkEVM —
the same implementation ⊑ ISA-model problem shape as ours):

1. **Non-executable by its own README** ("neither executable nor polished in any
   way"; every file wrapped in `noncomputable section`) — kills the diff-testing
   role, which is the main thing an imported model would be for.
2. **Measured, not hypothetical, legibility cost against our primary design
   constraint** (prover-readable goals): ~130-line `open` floods per file; one
   72,378-line decode/execute file (`InstsEnd.lean`) spanning V/crypto/S-mode we
   have no obligations about, with decode match-arms indented past column 98;
   50-line single-expression nested CSR update chains (`legalize_mstatus`). The
   independent Zulip evidence (matrix #3) says exactly this style fights the prover.
3. **Version skew is material**: CV32E40P documents privileged spec **v1.11
   (20190608)**; mainline sail-riscv tracks the current ratified spec (20211203+),
   across which several WARL/WLRL classifications changed (`mstatus` WLRL→WARL,
   `pmp*` WIRI→WARL). Current sail-riscv's legalization functions are therefore
   *not* correct-by-import for CV32E40P even if the import were otherwise clean.
4. **Xpulp is greenfield either way**: ordinary PULP custom instructions fit
   Sail's documented extension mechanism, but **hardware loops do not** — HWLoop is
   a persistent CSR-driven fetch-time PC redirect requiring a change to the step
   function itself, with documented interrupt/debug interactions. No surveyed model
   (Sail, GRIFT, Forvis, riscv-coq, Kami) has Xpulp coverage, so the hardest
   modeling work is ours regardless of build-vs-import.

**Sail's correct role** (all three retained): (a) **validation oracle** — diff-test
our model against the Sail C emulator's traces, the same harness pattern the SV lane
uses against Xcelium; (b) **table mine** — transliterate CSR bit layouts, exception
codes, and interrupt priority ordering from the short, readable Sail *source*
functions (BSD-2-Clause, RISC-V International governance — licensing confirmed
clean); (c) **structural template** — the `legalize_*` / `getPendingSet` /
`dispatchInterrupt` idiom, re-derived at v1.11 field values against
`cv32e40p_cs_registers.sv` and the 1.11 spec text.

**Risks and mitigations.**
- *Our hand model is simply wrong somewhere.* Mitigate three ways: Sail-emulator
  diff-testing (above), riscv-tests / core-v-verif test suites through an
  executable `#eval`-able model (make executability a hard requirement — it is
  precisely what the import lacks), and the WARL audit against the 1.11 text.
- *v1.11 audit is skipped under schedule pressure.* This is the highest-risk
  silent-failure path (CS-register file is our own census's highest-Unsupported
  file); it is called out as Action 1's explicit sub-task, not an implicit one.
- *Hand-build stalls / scope creeps.* **Fallback**: adopt riscv-coq's structure as
  a line-by-line design template (hand-written-for-legibility, cross-checked
  against Kami in a different prover — the closest cross-prover precedent), and
  keep watching sail-riscv-lean: it regenerates daily and its maintainers are
  upstreaming BitVec improvements, so if it becomes executable and restyled, the
  *diff-oracle* role can be upgraded from C-emulator to in-Lean — but even then it
  enters as a cross-check, never as theorem-facing terms.

---

## 3. POSITION CHECKS — where the literature pushes back

### 3.1 Bounded response over unbounded liveness — **KEEP, with one honest caveat to state in docs**
**The contradiction (steelmanned):** Lamport — the one Area-A source read in full —
*agrees* the bound is what we really want but argues stating it is impractical
("distracting timing assumptions") and defends unbounded liveness as the
honest-enough approximation. Steelman: for asynchronous software, any concrete
bound is arbitrary and pollutes the spec with justification obligations that buy
nothing.
**Response:** his objection evaporates in synchronous hardware — the clock cycle is
the native unit, and BMC completeness-threshold theory (Kupferman–Vardi lineage)
guarantees a true bound *exists* for any fixed-width finite-state design. The
field's newest kernel-checked pipeline proof (OOPSLA'25) proves its "progress
guarantees" via a concretely bounded decreasing token, not an unbounded eventually
[read from Rocq source] — independent alignment. **But** the caveat is real and
ours specifically: the finiteness argument does not survive our ∀-width design law;
a bound proved at one width is not automatically a bound at all widths, so each
∀-width bounded-response theorem genuinely re-derives its bound — extra deductive
work a fixed-instance BMC treatment never faces. **Verdict: keep**; state the
caveat explicitly; retain the unbounded fallback combinator for the gallery-#19
corner and decide its fixpoint polarity deliberately (matrix #16).

### 3.2 Shallow trace-combinator embedding — **KEEP, uncontested**
No contradicting literature found. Three independent formalization effords in two
provers (Coupet-Grimal/Coq, Wan/Coq, Merz/Isabelle-TLA — A [skimmed]) converged on
the same shallow shape, Merz's shipping in the Isabelle distribution for two
decades; no retrospective preferring deep embedding for temporal logic surfaced.
The convergence itself is the finding.

### 3.3 Fairness bundled into oracle legality — **KEEP, but it now carries a debt**
**The pressure (steelmanned):** Lamport's machine-closure discipline [read] says a
spec whose liveness/fairness constrains which *finite* prefixes are legal is
pathological — you can't tell if a step is allowed by looking at the next-state
relation. If our σ-legality predicate is not machine-closed against the design's
step relation, "∀ legal σ" silently excludes real runs and every ∀σ theorem
overclaims. This is not a contradiction of the position but a soundness condition
the literature imposes on it that we currently state nowhere.
**Support:** Cohen–Namjoshi–Sa'ar [intro read] shows the alternative (global
fairness discharged per-module in circular AG) is a known-hard problem we sidestep
by construction; GR(1)'s assumption-side justice and I/O automata's task partitions
are the same architecture with decades of pedigree. **Verdict: keep, and pay the
debt** — `ScheduleOracle.machineClosed` (matrix #9) plus the non-vacuity witness
(matrix #5) turn the position from slogan into checked theorem.

### 3.4 Specs mention ports only — **KEEP, with two amendments**
**Pressure 1 (observable too thin):** OOPSLA'25's port-only observable is
PC-commit-only [read from source] — and issue #509's wrong-instruction-executed bug
can leave the PC trace looking plausible while wrong *data* is written. Ports-only
is right; *which* ports matters. **Amendment:** the retirement observable must be
RVFI-tuple-rich (matrix #6), not PC-only.
**Pressure 2 (compositional proofs want internal taps):** Chen et al. [read] had to
extend RVFI with internal pipeline taps to make stage-level AG proofs go through —
apparently violating ports-only. **Resolution:** at module granularity the tension
dissolves — a whole-core "internal" signal is a *port* of the stage sub-module, and
our contracts live at module boundaries; ghost/history fields for what no port
retains are legitimized by Abadi–Lamport (matrix #1).
**Pressure 3 (∃ vs ∀ environment):** Interface Automata's optimistic ∃-environment
compatibility [skimmed] answers a design-time question, not deployment
correctness; Module Checking's adversarial ∀-framing is our stance. **Verdict:
keep ∀**, adopt ∃-compatibility only as a paired non-vacuity lemma (matrix #5),
and flag the disagreement in the OBI contract doc so nobody imports IA's notion
expecting it to mean `⊨`.

### 3.5 Kernel proofs over model checking, BMC as falsifier only — **KEEP; the literature armed it**
**Steelman for the other side:** the OneSpin CV32E40P campaign found ~30 real bugs
with autogenerated properties and a BMC-class engine [secondary], and Chen et al.
found three real RTL bugs with JasperGold [read] — why not just run the tools?
**Response, from their own numbers:** Chen et al.'s headline *is* the rebuttal —
"proof core coverage 48.98%→60.60%" means a large residual was never proved, only
bounded-checked; and the OOPSLA'25 kernel-proof lineage shows what BMC-tier results
structurally cannot state (∀-width, ∀-schedule, machine-checked composition).
Centaur's origin story (kernel proof caught what simulation missed [secondary]) is
the positive existence proof. **Verdict: keep** — and keep the bug lists those
BMC campaigns produced as our falsifier-tier calibration corpus (§4).

**One settled position got *stronger*:** no formal OBI artifact exists anywhere
(Area D read the openhwgroup/obi repo directly: seven prose PDFs, no SVA, no
machine-readable spec). Our Lean OBI model will be the **first** formal artifact
for this protocol — which also means no second formal opinion will catch our
modeling mistakes; the RTL-simulation diff harness is the only cross-check.
(Also for the record: Area D could not substantiate the "Amazon AXI formal work"
the brief assumed — AWS's published formal program is distributed software, not
AMBA hardware.)

### 3.6 Honest gap statement (no precedent either way)
Our sv_vcgen plan — *kernel-proof* rely-guarantee contracts at register/stage
boundaries for a real pipelined core — has **no direct precedent** in the
literature. Every kernel-proof pipeline result found (Choi et al., Silver; Kôika
proves no core theorem at all) is one monolithic core-level theorem; the only
compositional stage-cut precedent (Chen et al.) is BMC-tier. Closest in spirit:
Sawada–Hunt's per-stage invariant fields inside one MAETT. We are combining two
proven ingredients (McMillan-style AG composition + kernel-proof refinement) in a
way nobody has published. That is opportunity and risk in equal measure; the
campaign spec should say so plainly.

---

## 4. THE REPLICATION TARGET — the CV32E40P bug corpus as acceptance benchmark

**Framing: our proofs must be able to catch their bugs.** Concretely: for each
target bug, re-introducing the buggy RTL must make the corresponding contract/
refinement proof *fail* (the goal becomes unprovable and, where applicable, the
BMC falsifier produces a counterexample trace). A proof style that would have
passed the buggy RTL is rejected at review.

**Tier 1 — the anchor bug (primary-source, fully specified).**
`openhwgroup/cv32e40p` **issue #509, "Core executes wrong instruction"** [read from
the GitHub issue, B]: a `lw` stalls on a data-memory wait state; an interrupt
request arrives and is **retracted** before service, leaving
`instr_valid_irq_flush_q` set; a **debug-mode** entry request arrives; on debug
exit the core executes a `sw` that the flush should have discarded. Found by
OneSpin 360 while proving a PC-update property. Acceptance criteria derived from
it: (a) the controller contract carries the MAETT-style validity ghost bit
threaded through interrupt-retraction and debug-entry paths (matrix #7) — this bug
is not even *representable* in the OOPSLA'25/Kôika no-interrupt models; (b) the
retirement observable is RVFI-tuple-rich, because the PC trace alone can look fine
while wrong data commits (matrix #6, §3.4). **#509 is the single sharpest test of
whether our spec surface is pointed at the right bug class.**

**Tier 2 — calibration bugs (primary-source, other cores, cheap to reproduce).**
From Chen et al. [read]: `sra`/`srai` implemented as logical instead of arithmetic
shift (Vscale); `jalr` target-address LSB clearing mis-ordered per spec (Vscale);
`csrrwi`'s rs1=x0 exemption applied to the wrong CSR-instruction subset (RV12).
These are ideal *seeded-bug* tests for the leaf tier (matrix #12) before touching
CV32E40P proper: each must be caught by the per-opcode ALU/CSR theorems on a
small demonstrator.

**Tier 3 — aggregate campaign statistics (secondary, vendor-blog grade — treat as
approximate).** OneSpin/Siemens campaign: ~430 autogenerated assertions + 29 CSR
descriptions from a Sail ISA description, 7 configurations; ~30 formal-found vs.
~20 simulation-found issues pre-RTL-freeze; v2.0.0 pass: 18 RTL bugs
(illegal-instruction exceptions, multi-cycle FP hazards, IEEE-754 compliance) + 12
manual clarifications; original IMC core: 8 bugs "in regular and exception
instructions," corner cases in instruction sequences, memory stalls, and CSR
programming. The distributional claim to carry into campaign planning: **the bug
mass sits at the pipeline-control × exception/interrupt/debug intersection, not in
functional-unit datapaths** — which is where our proof effort should be weighted.

**Known gap:** no itemized public per-bug list with RTL diffs beyond #509 was
found; Tier 3 numbers trace to vendor marketing and manual prose. Closing this gap
is Action 5.

---

## 5. TOP 5 CONCRETE NEXT ACTIONS

1. **Start the hand-written ISA model** (`LeanModels/RiscV/`): RV32IM(C)+Zicsr,
   M/U-only, privileged v1.11, semantic-bucketed AST, executable by construction;
   sub-tasks: WARL audit of every CSR against the v1.11 text and
   `cv32e40p_cs_registers.sv`, Sail-source bit-table transliteration with BSD-2
   attribution, and the Sail-C-emulator diff harness. *(Citations: Armstrong et
   al. POPL'19 / sail-riscv [read]; Carneiro Zulip guidance, LNSym, riscv-coq
   [read]; Area C's first-hand sail-riscv-lean inspection for the do-not-import
   verdict.)* — Effort L, starts the critical path.

2. **Specify the retirement ghost interface** as a port-level `Sv.onPosedgeIdx`
   contract: monotonic gap-free order tag + full effect tuple (rd/mem/trap/intr)
   + the MAETT-style "still-valid-to-commit" ghost bit with interrupt-retraction
   and debug-entry cases explicit; acceptance test = the spec is falsified by a
   mechanized #509 scenario. *(Citations: riscv-formal `rvfi.md` [read];
   Sawada & Hunt CAV'97 [secondary]; cv32e40p issue #509 [read].)* — Effort M,
   the highest-leverage spec-surface deliverable.

3. **State and prove the register-boundary AG composition lemma** in the Sv lane:
   McMillan's `▷` rule with hand-added ghost strengthening, soundness by strong
   induction on the cycle index per Rushby's PVS template; adopt Chen et al.'s
   stage-cut granularity as the sv_vcgen contract seam; document the honest gap
   (§3.6) in the campaign spec. *(Citations: McMillan CHARME'99 + Rushby SRI TR
   2001 [read via restatements]; Namjoshi–Trefler TOCL'10 [read]; Chen et al.
   DVCon [read].)* — Effort M, unblocks all compositional work.

4. **Pay the oracle-hygiene debt**: state `ScheduleOracle.machineClosed`, add the
   legality non-vacuity witness, name fairness clauses WF/SF; then draft the
   BusOracle/OBI contract design note (∀-environment framing, IA vocabulary with
   the ∃-compatibility disagreement flagged, history-vs-prophecy checklist,
   "first formal OBI artifact" stated explicitly) after a primary read of
   Reactive Modules. *(Citations: Lamport 2019 [read]; Abadi–Lamport 1991 +
   Lamport–Merz 2022 [read]; GR(1) [skimmed]; Alur–Henzinger, Kupferman–Vardi–
   Wolper, Lynch–Tuttle [skimmed]; openhwgroup/obi repo [read].)* — Effort M,
   mostly S-sized pieces; makes three settled positions checkable.

5. **Build the acceptance benchmark harness**: mechanize the #509 scenario as the
   anchor regression; seed the Tier-2 calibration bugs (`sra`/`srai`, `jalr` LSB,
   `csrrwi`) into small demonstrators and confirm the leaf-tier proof style
   catches each; trawl `openhwgroup/cv32e40p` closed issues (bug × formal/OneSpin/
   riscv-formal labels) to replace Tier-3 vendor numbers with an itemized per-bug
   list. *(Citations: issue #509 [read]; Chen et al. DVCon [read]; OneSpin/OpenHW
   campaign reports [secondary].)* — Effort M, converts "our proofs would catch
   real bugs" from a claim into a measured property.
