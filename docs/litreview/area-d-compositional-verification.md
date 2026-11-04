# Area D — Compositional Verification + Environment Modeling

Scope: assume-guarantee/rely-guarantee for hardware, Abadi–Lamport composition +
refinement mappings + history/prophecy variables, circular AG soundness, AXI/AMBA
and OBI formalization, interface automata, TLM refinement. Evaluated against our
settled positions: bounded response over unbounded liveness; fairness bundled into
oracle legality; shallow trace-combinator embedding; specs mention ports only;
∀-width parametric theorems; kernel proofs over model checking with BMC as
falsifier only. Does NOT re-review Choi/Kim/Kang OOPSLA'25, DVRTL, Fjfj/Kami, or
Dobis LATTE'25 — those are prior adoptions.

Reading-depth key: **[read]** = fetched and read substantial primary text (PDF
extracted via pdftotext, multiple pages digested). **[secondary]** = read a
faithful restatement/formalization by a later author, not the primary source
directly. **[abstract]** = search-snippet/abstract-level only, not verified by
reading the paper.

---

## D.1 Assume-guarantee / circular compositional reasoning for hardware

### D.1.1 McMillan's circular rule and the induction-over-time argument — **[read + secondary]**

Primary: K. L. McMillan, "Circular compositional reasoning about liveness," in
*Correct Hardware Design and Verification Methods (CHARME'99)*, LNCS 1703,
pp. 342–345, Bad Herrenalb, Germany, Springer, 1999. (4-page paper; I fetched it
directly but the PDF's font encoding was non-standard and pdftotext produced
garbage — content below is reconstructed from two independent faithful
restatements: Rushby's PVS formalization [read in full] and Namjoshi–Trefler's
TOCL 2010 journal restatement [read in full, §2.12–2.13], which quote and derive
from McMillan's Theorem 1 explicitly, so I count this as solidly corroborated
despite not parsing McMillan's own typography.)

Companion primary source I *did* read cleanly: John Rushby, "Formal Verification
of McMillan's Compositional Assume-Guarantee Rule," SRI CSL Technical Report,
September 2001 (PVS mechanization).

**This is the theorem docs/sv-spec-surface.md is implicitly leaning on for the
register-boundary-breaks-circularity claim.** McMillan's rule:

```
⟨H⟩ X1 ⟨P2 ▷ P1⟩
⟨H⟩ X2 ⟨P1 ▷ P2⟩
──────────────────────────────
⟨H⟩ X1‖X2 ⟨□(P1 ∧ P2)⟩
```

where `p ▷ q` ("p constrains q") is defined as `¬(p U ¬q)` — informally: *if p
holds at every point up to time t, then q holds at time t+1*. The crucial detail
is the strict **next-time offset**: the hypothesis about `X1` establishes `P1` at
`t+1` from `P2` known only up to `t`, and symmetrically for `X2`. This is exactly
what makes the circularity resolvable: McMillan's own motivating example is a
distributed clock-synchronization protocol (TTA) where "sync depends on
membership, membership depends on sync" is real, but *not* circular once you
notice sync-at-round-t depends on membership-at-round-(t−1). Rushby's soundness
proof (mechanically checked in PVS, and I read the actual tactic script) is
literally `(INDUCT "i" ...)` — **strong induction on the time/position index**
after unfolding `▷` and `□` via two helper lemmas (`agr_box_lem`,
`constrains_lem`). That induction is the "induction-over-time argument" the task
description points at.

**Direct mapping to our register-boundary claim:** a purely combinational
feedback loop between two modules has no `t`/`t+1` separation to induct on — you
cannot state `P2 ▷ P1` for it, only `P2 → P1` at the *same* instant, which is
exactly the naive circular rule Rushby shows is unsound (his introductory
counterexample: `X1` = "wait until y=1, then set x=1", `X2` = "wait until x=1,
then set y=1" — both wait forever, hypotheses true, conclusion false). A
synchronous register at the module boundary is precisely what supplies the `t →
t+1` separation the `▷` operator needs: the register's output at `t+1` is a
function only of what was established by `t`. **Verdict: this is the exact
theorem to cite when we write down our register-boundary-breaks-circularity
lemma** — our discipline ("cut the mutual dependency at a register, not a wire")
is a hardware-specific instance of McMillan's `▷`-shaped antecedent, and Rushby's
PVS proof is a template for how short the induction is once stated correctly
(a few lines, not a research project).

McMillan's own rule is known **sound but incomplete**. It's used in practice for
hardware (McMillan, "A methodology for hardware verification using compositional
model checking," *Science of Computer Programming* 37, 2000 — **[abstract]**,
not read) via SMV; industrial track record, not just theory.

### D.1.2 Sound-and-complete circular rules, and where the incompleteness bites — **[read]**

Kedar S. Namjoshi and Richard J. Trefler, "On the Completeness of Compositional
Reasoning Methods," *ACM TOCL* 11(3), Article 16, 2010 (journal version of their
CAV 2000 paper). I read this closely (§2–4).

Findings directly useful to us:

- The **noncircular** rule NC (compose via an explicit intermediate assumption,
  no back-reference) is *both sound and complete* when auxiliary assertions may
  be freely chosen (Prop. 2.10/2.11) — completeness proof is by induction on
  proof structure, nothing exotic.
- McMillan's rule (their "C1", a generalization to n components with a
  well-founded order over which components' properties may be assumed) is
  **provably incomplete** — they give an explicit 4-token juggling counterexample
  (`M1`, `M2` pass tokens `l,r` back and forth; `□(l1 ∧ l2)` is true of the
  composition but *cannot* be derived by C1 no matter how the well-founded order
  is chosen) and diagnose the cause precisely: **C1 as originally stated doesn't
  allow strengthening with auxiliary (ghost) state** — you can't add an
  `h`-style invariant conjunct the way ordinary inductive-invariant proofs do.
  This is the same lesson our own project has learned independently in the
  circuit lane (ghost/history state is what turns "true but unprovable
  locally" into "provable locally") — good cross-validation.
- Abadi & Lamport's own circular rule ("Conjoining Specifications," *ACM TOPLAS*
  17(3), 1995 — their rule "C2" in NT's numbering) *does* allow auxiliary
  assertions `E_i`, but is **also incomplete** because of the restricted syntactic
  form of its hypotheses (uses process-closure `C(·)` and a `+v` "eventually
  stutters" operator) — NT give an explicit counterexample with two
  fairness-dependent programs.
- NT's own rule ("C3") is **sound and complete**: it permits auxiliary properties
  defined *only on the process interface* (shared variables) plus a well-founded
  order, generalizing McMillan's shape just enough to add the missing
  strengthening freedom. They separately prove circular and noncircular proofs
  inter-translate (§6) — i.e., circularity per se buys no extra expressive power
  for LTL, only proof-engineering convenience.

**Reconciling with Maier's impossibility (below):** genuinely a literature
tension I did not fully resolve. Flagging honestly rather than papering over it.

### D.1.3 Maier's impossibility result — **[abstract only]**

Andreas Maier, "Compositional Circular Assume-Guarantee Rules Cannot Be Sound
and Complete," FoSSaCS 2003 (LNCS 2620) — I did not get past the abstract/citing
snippets (PDF not fetched). Abstract-level claim: for a class of circular AG
rules operating at the pure trace-language level (parallel composition = trace
intersection), no rule of that shape can be simultaneously sound and complete.
This looks like it contradicts NT00/NT10's completeness claim for their rule C3.

My best (unverified — **flag for follow-up before we lean on either result**)
read of the reconciliation: Maier's impossibility is stated for a *narrower*
rule format — no well-founded ranking device, no interface-local auxiliary
assertions as first-class rule parameters — whereas NT's C3 rule is a genuinely
richer proof-rule *schema* (it lets the prover choose both a well-founded order
over an n-way (not just 2-way) decomposition *and* per-pair-of-processes ghost
predicates). If that reading holds, there's no contradiction: Maier's theorem
characterizes what a "plain" circular AG rule (McMillan/Abadi-Lamport shape)
can't do, and NT's rule escapes the impossibility by adding exactly the extra
structure Maier's argument rules out for the plain shape. **This nuance does not
matter operationally for us** — we do kernel (interactive) proofs, not automated
proof-rule search, so *completeness* of a canned circular-AG proof rule is not
something we need; we only need any one instance of *sound* circular reasoning
to go through for CV32E40P's specific pipeline-stage cuts, and McMillan's rule
(with ghost strengthening added by hand, á la NT's diagnosis) already gives us
that. Completeness results tell us *when a proof rule will never find a
witness*, which is an automation concern, not a "can Lean prove this" concern.

### D.1.4 Environment-as-oracle precedent (Key Question 1)

Three genuinely distinct lineages answer "who else parameterizes semantics by
an explicit environment-strategy oracle, with fairness folded in":

1. **Alur & Henzinger, "Reactive Modules,"** *Formal Methods in System Design*
   15(1), 1999 (journal version; original LICS'96) — **[abstract + secondary
   via search synthesis, not directly read]**. Reactive Modules is the closest
   *semantic-framework* precedent: every module explicitly distinguishes
   **internal nondeterminism** (choices the system resolves) from **external
   nondeterminism** (choices the environment resolves), an AG rule is given in
   the same `⟨P1‖Q2 ⊨ Q1⟩ ∧ ⟨Q1‖P2 ⊨ Q2⟩` shape as McMillan's, and — importantly
   — **weak/strong fairness is a first-class per-module annotation**, not a
   bolt-on. This is architecturally the nearest ancestor of our `BusOracle`:
   Reactive Modules quantifies proofs over "every legal environment module,"
   which is our `∀σ`. Worth reading the primary paper before we finalize
   `BusOracle`'s legality predicate — this is the strongest textual precedent
   found, but I have not verified the fairness formalism at primary-source
   depth.

2. **Kupferman, Vardi & Wolper, "Module Checking,"** CAV'96 / journal version
   *Information and Computation* 164(2), 2001 — **[abstract only]**. This is the
   sharpest *conceptual* match for "the environment is an oracle you quantify
   over, and legality of its choices matters": a *module* is a Kripke structure
   with states partitioned into system-states and environment-states (a
   turn-based 2-player game); module checking asks "for every way the
   environment can restrict its choices, does the system satisfy φ" — literally
   the ∀-environment-strategy quantification our `⊨` judgment performs, phrased
   as an adversarial (not optimistic) game. The open-systems verification
   survey framing (Vardi, "Verification of Open Systems") is worth a closer
   read as the standard reference for *why* ∀-environment (not ∃-environment,
   see D.4 below) is the right stance for a hardware core that must work with
   *any* legal bus master/subordinate, not just a convenient one.

3. **Lynch & Tuttle, I/O automata** ("An Introduction to Input/Output
   Automata," 1989) — **[abstract only]**. Older but foundational: input actions
   are always enabled (the environment can never be blocked — a discipline we
   already assume implicitly for `req`-style OBI signals) and fairness is
   captured via an explicit "task partition"/"fairness structure" bundled with
   the automaton, which composes. This is the oldest instance of "fairness as
   part of what makes an execution admissible," i.e. exactly our "bundled into
   oracle legality" stance, predating both McMillan and Reactive Modules by
   ~7–15 years. Good historical grounding to cite even though it predates
   hardware-specific framing.

4. **Cohen, Namjoshi & Sa'ar, "A Dash of Fairness for Compositional
   Reasoning,"** CAV 2010 — **[read the introduction/abstract cleanly]**. Useful
   *contrast*, not precedent: they show incorporating **global** fairness into
   **local**, per-process compositional (circular AG) proofs is hard precisely
   because "process P is enabled infinitely often" is a predicate over every
   other process's local state — the opposite of a clean per-component
   contract. Their fix is a fully-automated iterative-refinement algorithm
   (add shared ghost variables until local reasoning suffices), not a
   change to what fairness *means*. **This validates our design choice**: by
   defining fairness as a property of the oracle itself (σ legality) rather
   than as a global temporal side-condition to be discharged compositionally
   per-module, we sidestep exactly the difficulty this paper spends 20 pages
   automating a workaround for. Worth citing as "the problem we avoid by
   construction," not as a technique to adopt.

**Verdict (Key Question 1):** no single paper is *exactly* "BusOracle" (an
explicit oracle-valued parameter to the semantics, with fairness as part of its
legality predicate, for a specific real bus protocol). The precedent is a
composite: Reactive Modules gives the internal/external nondeterminism split +
per-module fairness annotations; Module Checking gives the ∀-adversarial-
environment stance; I/O automata gives "fairness bundled with the component,
not the property" as the oldest instance of the idea. Cite all three when we
write the `BusOracle` design note; none needs adoption as machinery (we already
have the shape), but Reactive Modules' AG rule is worth a primary read before
we state our own OBI-boundary AG lemma, since it's the closest structural
sibling to McMillan's rule but phrased for exactly the internal/external split
we need at an OBI manager/subordinate boundary.

### D.1.5 Industrial precedent: assume-guarantee applied to a RISC-V pipeline — **[read in full]**

Yean-Ru Chen et al. (National Cheng Kung University), "Automate and Accelerate
RISC-V Verification by Compositional Formal Methods," Accellera/DVCon-style
slide deck (© Accellera Systems Initiative; presented as a DVCon paper). I
fetched and read the full deck (it downloaded cleanly as text via pdftotext).

This is the single closest "someone did roughly our program to a RISC-V core"
precedent I found, and it is directly relevant to the CV32E40P plan:

- Targets: **Vscale** (32-bit 3-stage pipeline RISC-V) and **RV12** (32/64-bit
  6-stage pipeline RISC-V) — i.e., pipelined open-source RISC-V cores, same
  class of design as CV32E40P.
- Method: classic 2-component assume-guarantee, `M‖A ⊨ P`, `N ⊨ A` ⟹ `M‖N ⊨ P`,
  applied at a **pipeline-stage cut**: `M` = "datapath writing to the correct
  destination register," `N` = "computing the correct writeback data," `A` =
  "data forwarding is correct" (assumed by M, discharged by N). This is exactly
  our own planned CV32E40P P6+ move (pipeline-stage rely-guarantee contracts,
  no file-local spec) — good validation that the stage-boundary cut is the
  natural granularity industry also converges on, independent of us.
- Tooling: Cadence JasperGold (BMC/IPC formal, **not a kernel proof** — this is
  the "untrapped BMC" epistemic tier we deliberately keep as falsifier-only, not
  ground truth). Their headline result is exactly the kind of thing we should
  *not* rely on for a theorem: "Proof core coverage 48.98%→60.60%" after
  abstraction, i.e., a fraction of the state space was formally covered, with a
  large uncovered "waived" residual (89–98% *after* waiving unconcerned logic,
  meaning a nontrivial fraction of even the "concerned" logic was never proved,
  only bounded-model-checked to some depth). They *did* find real RTL bugs this
  way (sra/srai using `>>` instead of `>>>`; a jalr immediate-masking bug in
  Vscale; a csrrwi x0-source-register bug in RV12) — good demonstration that
  compositional decomposition is worth doing even at BMC-only assurance, but
  it's a demonstration of our "BMC as falsifier" tier working, not of anything
  resembling our target kernel-checked tier.

**Verdict:** adopt the pipeline-stage-cut *granularity* as validated (industry
converges on the same natural seams we'd pick), reject the tooling/assurance
tier (JasperGold BMC coverage percentages are not proofs) — exactly consistent
with our existing "kernel proofs over model checking, untrusted BMC as falsifier
only" position; this paper is good ammunition *for* that position when
justifying it to reviewers who might otherwise ask "why not just run
JasperGold on CV32E40P."

---

## D.2 Abadi–Lamport: refinement mappings, history and prophecy variables

Primary sources actually read (not just abstract):

- Leslie Lamport & Stephan Merz, "Prophecy Made Simple," *ACM TOPLAS* 44(2),
  2022 — **[read in full, §4]**. This is a deliberately simplified, modern
  restatement of Abadi & Lamport's 1991 machinery, written by one of the
  original authors — I treat it as authoritative for the *intuition and
  worked examples*, though I did not separately verify against the 1988/1991
  originals' exact theorem numbering.
- Martín Abadi & Leslie Lamport, "The Existence of Refinement Mappings,"
  *Theoretical Computer Science* 82(2), 1991 (LICS Test-of-Time Award winner)
  — **[abstract/secondary only]**: I confirmed the three named conditions
  (machine closure, finite invisible nondeterminism, internal continuity) via
  search-snippet corroboration across three independent sources, but did not
  get clean primary text of the exact theorem statement (PDF fetch failed to
  decode). Treat the *conditions' names* as solid, the *exact quantifier
  structure* as not independently verified by me.
- Abadi & Lamport, "Conjoining Specifications," *ACM TOPLAS* 17(3), 1995 —
  read via Namjoshi–Trefler's careful restatement (§3.2, D.1.2 above), not
  the primary itself.

### D.2.1 The core mechanism, precisely (from the worked example I read)

Lamport & Merz's central illustrative pair (§4.1–4.2), which I read in enough
detail to trust:

- Spec `A`: alternates strictly between accepting an input and producing an
  output (`in ↦ out`, one-for-one, immediately committed).
- Implementation `C`: same as `A` but can, after accepting an input, *undo* it
  (discard without producing output) instead of committing.
- `A` (hidden-input version `Ã`) trivially **implements** `C` (every `Ã`
  behavior is a `C` behavior that just never exercises Undo) — this direction
  needs *no* auxiliary variables at all.
- The interesting direction is `C` implementing `Ã`: **you cannot build a
  refinement mapping using history variables alone**, no matter how you try.
  The fix is a **prophecy variable** `p ∈ {do, undo}` that, at the moment each
  input is accepted, *predicts* whether that input will eventually be
  committed (`Output`) or discarded (`Undo`) — information that is **not yet
  determined** by anything in the trace so far, only by what happens later.

This gives a crisp, generalizable diagnostic: **a history variable suffices
exactly when the auxiliary fact the refinement mapping needs is a function of
the trace-prefix-so-far (something that already happened); a prophecy variable
is needed exactly when the fact is a function of the trace-suffix-not-yet-
determined (something that will happen, and whose eventual outcome is not yet
fixed by the current state)**. Lamport also flags the "weirdness" honestly:
specifications augmented with a prophecy variable are typically **not machine
closed** (a prophecy can predict something that then can't happen, discussed
at length in §4.3 with a `halts`-vs-`WF` example) — but this is harmless
because the augmented spec is a *proof device*, never itself claimed to be
implementable.

### D.2.2 Answering Key Question 2 — history sufficiency for exactly-once ghost tagging

Our "exactly-once ghost tagging" need (tag that some transaction-completion
event has fired exactly once, for OBI-style request/response accounting, or
for any handshake we ghost-instrument) is, by the diagnostic above, **a
history-variable problem, not a prophecy-variable problem** — "has this fired
yet, and how many times" is a pure function of the trace-prefix-so-far,
computable online with no lookahead. **Prophecy would only become necessary if
we ever needed to tag *now* a fact that is only resolved by a *choice made
later and not yet determined*** — e.g., if OBI's spec let the subordinate
non-deterministically decide, at the moment of accepting a request, whether it
will *eventually* respond with an error vs. success, and we wanted to tag the
request with which outcome it's "destined" for before that's observably fixed.
As long as our exactly-once tags are computed strictly from what has already
been observed (request accepted, response returned, counted), we are safely in
the history-variable-suffices regime and the Abadi-Lamport machinery gives us
no reason to expect an obstruction — **the applicable completeness guarantee is
Abadi & Lamport 1991's three-condition theorem specialized to the "no
prophecy needed" case** (their own framing: prophecy variables are the
*general* completeness device; history variables alone are complete only under
the extra condition that the implementation's every future-relevant choice is
already resolved by the time the corresponding abstract-spec choice must be
made — which, for a simple counting ghost, is automatic since counting never
needs to look ahead). **Caveat**: I have not independently re-derived or
verified this specialization from the 1991 paper's exact theorem text (only
from Lamport & Merz's worked-example intuition) — treat as a well-motivated
working hypothesis, re-derive/cite properly if a headline theorem's soundness
ever hinges on it.

**Practical corollary for the SV lane**: if a future OBI/CV32E40P ghost-state
need ever requires predicting an outcome not yet observably resolved (e.g.
speculatively tagging a load with "will this be the one that gets flushed by a
later branch misprediict"), that is a genuine prophecy-variable situation, and
Abadi–Lamport's own completeness theorem is the right citation for "this is
provably always possible in principle, mechanically it may still be fiddly" —
we are not likely to need it for OBI-level exactly-once tagging, but we should
expect to need it once we get to pipeline-flush/speculation ghost state in the
core proof, and should flag that explicitly rather than being surprised later.

---

## D.3 Protocol/bus formalization: AXI/AMBA and OBI

### D.3.1 OBI — Key Question 3, answered definitively — **[read primary repo]**

I fetched `github.com/openhwgroup/obi` directly. **There is no formal artifact.**
The repository contains exactly seven versioned prose/diagram PDFs
(`OBI-v1.0.pdf` through `OBI-v1.6.0.pdf`) and a README — no SVA, no TLA+, no
reference checker, no machine-readable protocol description of any kind. I also
checked `Peter-Herrmann/obi-lib` (community OBI infrastructure blocks — muxes,
demuxes, a Wishbone-to-OBI adapter) — implementation RTL, explicitly "basic
Verilog, no formal claims," not a spec artifact either.

**Verdict: no published formal OBI artifact exists to differentially test
against.** This is not a gap in my search — the spec itself is authored as
prose (PDF, with waveform diagrams) by OpenHW, and no third party has produced
a formal shadow of it either. Two implications for our program: (1) our own
Lean OBI model, when we build it, will be the **first** formal artifact for
this protocol as far as I can find — worth stating that explicitly rather than
assuming there's prior art to check against; (2) our only "differential"
partner for OBI-boundary behavior is CV32E40P's own RTL simulated (Verilator/
Xcelium), not an independent formal reference — raises the bar on getting our
own OBI Lean model right the first time, since there's no second formal opinion
to catch our modeling mistakes the way Xcelium catches our SV-semantics
mistakes.

### D.3.2 AXI/AMBA — sparser than expected — **[mixed read/abstract]**

Searched specifically for "ARM's own" formal artifact, "Amazon's AXI work,"
and academic AMBA verifications, per the task brief. Results:

- **ARM's own spec**: the AMBA AXI/AXI4/ACE protocol specifications are, as
  far as I can determine, **prose PDF documents** (like OBI, but far larger and
  more mature) — I did not find any ARM-published formal (TLA+/Alloy/proof-
  assistant) artifact, and none of my searches surfaced one. ARM's own formal
  *methodology* work is elsewhere (e.g. ISA-Formal for processor datapaths,
  cited inside the DVCon RISC-V deck above, D.1.5) — I found no AXI-specific
  counterpart from ARM.
- **"Amazon's AXI work"**: I could not substantiate this as stated in the task
  brief. AWS's well-documented formal methods program (Newcombe et al.,
  "How Amazon Web Services Uses Formal Methods," *CACM* 2015, which I did find
  and which is genuinely excellent, widely-cited TLA+ industrial practice) is
  about **distributed software systems** (S3, DynamoDB, EBS) — I found no
  evidence of an AWS-published formal AXI/AMBA hardware-protocol artifact.
  Possible the brief is conflating AWS's TLA+ reputation with a hardware
  artifact that either doesn't exist publicly or that my search didn't surface
  under those terms (worth a follow-up search specifically inside AWS's
  Annapurna Labs / silicon-team publication venues if this matters later — I
  did not find one and am not confident enough to assert it exists).
- **Academic AMBA verification**: thin. I found (a) a general "Testing of
  AMBA AXI Protocol" paper (academia.edu-hosted, **[abstract only]**, appears
  to be testing/coverage-oriented, not proof-oriented); (b) commercial VIP
  (Cadence, Siemens/OneSpin AMBA formal apps) — proprietary SVA-based formal
  IP sold alongside JasperGold/OneSpin, not published formal semantics with
  proved metatheory, and not independently checkable by us; (c) a third-party
  open-source **beta** SVA property set (`dh73/A_Formal_Tale_Chapter_I_AMBA`
  on GitHub — **[read repo description]**), explicitly self-described as
  educational/beta, covering AXI4-Lite/Full and AXI4-Stream handshake
  properties as SVA `property...endproperty` blocks intended for model
  checking, not a proof-carrying artifact.

**Verdict:** the AXI/AMBA formal-artifact landscape is dominated by
**monitors** (SVA properties, checked by BMC/formal-app tools, industrial and
mostly proprietary) rather than **contracts** (assume-guarantee style,
machine-checked metatheory) — reinforcing our own judgment-family choice to
build contracts, not just monitors, since nobody else in this space has done
the contract-style artifact either. Since CV32E40P uses OBI (not AXI) at its
core boundary, this AXI landscape is mostly *context* for us (what "the
industry does for buses" looks like) rather than a direct dependency, but it's
useful to know we can't borrow an AXI-side formal model even as a stylistic
template beyond "monitors are the default genre; nobody publishes contracts."

### D.3.3 Monitor vs. contract conformance-checking styles

Both bus landscapes (AXI's SVA VIP culture, and the DVCon RISC-V paper's
"split SVA properties" technique, D.1.5) exemplify the **monitor** style:
protocol conformance = a set of always-check assertions, verified by
simulation or BMC against a *fixed* design instance, no compositional
metatheory beyond "these properties hold in this cone of influence to this
BMC depth." Our own approach — `HasContract`-style paired projection/
realization inclusions (already implemented in the analog lane,
`docs/circuit-assurance-architecture.md` §"Validation slice 3": every
implementation behavior projects to the contract, *and* every boundary point
satisfying the contract has an implementation behavior) plus a
`compose_contracts` frame-rule metatheorem — is the **contract** style:
protocol conformance = a proved bidirectional refinement between an
abstract port-level relation and the RTL-level behavior, composable by a
kernel-checked theorem, ∀-parametric, not tied to one instance. Nothing in
the AXI/OBI/RISC-V-formal literature I found does this for a bus protocol;
our own in-house `compose_contracts` (analog lane) and the sv_vcgen
rely-guarantee plan (SV lane, `MEMORY.md`: "pipeline stages have NO
file-local spec, only contracts") are, on current evidence, ahead of the
published state of the art specifically for *bus/interconnect* contracts
(McMillan/Namjoshi-Trefler-style AG theory is more mature for general
concurrent systems than for a specific industrial bus protocol like OBI/AXI).
Confidence: medium — absence of evidence is not strong evidence for a
fast-moving industrial space I can only search, not exhaustively survey.

---

## D.4 Interface automata — vocabulary check for port contracts

Primary: Luca de Alfaro & Thomas A. Henzinger, "Interface Automata," ESEC/FSE
2001 — **[abstract + secondary synthesis, not primary text read]**.

Useful vocabulary, worth borrowing regardless of adoption verdict:

- **Input/output/internal action alphabets** per component — maps directly onto
  our "specs mention ports only" discipline; IA's alphabet split is a clean
  formal handle for *why* that discipline is principled (internal actions are
  exactly what a port-only spec must existentially hide).
- **Alternating-simulation refinement**: interface `P` refines `Q` iff `P` has
  *weaker* input assumptions and *stronger* output guarantees than `Q` — the
  standard contravariant/covariant contract-refinement shape. This is precisely
  the right vocabulary for stating our planned pipeline-stage contracts'
  refinement order (a stage implementation may accept more environments and
  promise more than its contract requires, never less).
- **Compatibility = existence of a legal environment** ("optimistic
  composition"): two IAs are compatible iff *some* environment exists that lets
  them interoperate without violating either's input assumption. **This is a
  genuine, load-bearing disagreement with our settled position.** Our
  `BusOracle`/`⊨` stance is closer to Module Checking's *adversarial* framing
  (D.1.4-2): we want theorems that hold for **every** legal OBI environment
  (∀σ), because a shipped core must work with whatever subordinate/manager it's
  wired to, not just some convenient one. IA's ∃-environment compatibility
  check is a *design-time type-checking* tool (does this pairing make sense at
  all?), not a *correctness-for-deployment* tool — the two frameworks answer
  different questions and we should keep using ∀ for correctness, while noting
  IA's ∃-compatibility check could be a genuinely useful *sanity* lemma to state
  separately ("CV32E40P's OBI port is compatible with at least the reference
  OBI subordinate," proved once, cheaply, as a non-vacuity witness — this is
  structurally identical to our own project-wide "soundness-shaped theorems
  need paired non-vacuity witnesses" lesson, MEMORY.md, applied at the
  interface-compatibility level).

**Verdict:** adopt the vocabulary (input/output alphabets, alternating-
refinement direction), do **not** adopt the ∃-environment compatibility notion
as our correctness criterion — flag the disagreement explicitly in the OBI
contract design doc so a future reader doesn't reach for IA's compatibility
check expecting it to mean what our `⊨` means.

---

## D.5 Transaction-level modeling (TLM) refinement literature — **[abstract only, weak]**

Searched specifically for formal TL→RTL refinement semantics (SystemC TLM).
Findings, all abstract-level:

- SystemC/TLM itself has **no official formal semantics** — it's defined
  operationally as a C++ class library plus prose (the Accellera TLM-2.0
  Reference Manual), the same genre-gap OBI/AXI have.
  and RTL — I found "incremental assertion-based verification (ABV)" work for
  TL→RTL refinement checking (BMC/ABV-tier, not proof-tier) and older attempts
  to translate SystemC into Petri nets for timed-temporal-logic model checking
  — both abstract-only, neither read in depth, both clearly BMC/model-checking
  tier rather than kernel-proof tier.
- One partially promising thread: "Proving transaction- and system-level
  properties of untimed SystemC TLM designs" (academia.edu-hosted PDF,
  **[abstract only]**) — title suggests a deductive (proof, not BMC) approach
  to TL properties, but I did not verify depth or read the paper.

**Verdict: weak precedent, nothing to adopt.** The one genuinely useful
takeaway is negative-but-informative: **our own `Sv.transaction` judgment
(example 10 in the SV gallery — request/response abstraction with `n` latched
at acceptance, proved refined by a Python golden model) is already doing, in a
kernel-checked ∀-stimulus theorem, roughly what the TLM literature's TL→RTL
"refinement checking" aspires to do with BMC/ABV** — we are not missing
borrowable machinery here so much as operating a tier above what's published.
Flag for the record, not a design input.

---

## Verdicts summary

| Method / paper | Verdict | Why |
|---|---|---|
| McMillan circular rule (CHARME'99) + Rushby's PVS soundness proof | **Adopt as the cited theorem** for register-boundary-breaks-circularity | Exact `▷`-shaped, induction-over-time soundness proof; register boundary = the next-time separation the rule needs |
| Namjoshi–Trefler sound+complete rule C3 (CAV'00/TOCL'10) | **Cite, don't need to implement** | Completeness is an automation concern; we do interactive proofs. Their incompleteness diagnosis (missing ghost-strengthening freedom) validates our existing ghost-state discipline |
| Maier's impossibility (FoSSaCS'03) | **Flag, don't resolve** | Abstract-only; apparent tension with NT completeness not independently verified by me; doesn't affect us either way |
| Reactive Modules (Alur–Henzinger) | **Read before finalizing BusOracle** | Closest structural sibling: internal/external nondeterminism split + per-module fairness, AG rule in the same shape |
| Module Checking (Kupferman–Vardi–Wolper) | **Adopt the framing, cite for ∀-environment justification** | Strongest conceptual precedent for "quantify over adversarial environment strategies" |
| I/O automata (Lynch–Tuttle) | **Cite as oldest precedent** for fairness-bundled-into-legality | Predates hardware-specific framing; "task partition" = fairness as part of the automaton, not a side condition |
| Cohen–Namjoshi–Sa'ar fairness-in-AG (CAV'10) | **Cite as the problem we avoid, not a technique to adopt** | Shows global fairness is hard for *local* per-component AG proofs; our oracle-legality approach sidesteps it by construction |
| Chen et al., RISC-V pipeline AG via JasperGold (DVCon) | **Cite as validating our stage-cut granularity; reject the assurance tier** | Same pipeline-stage AG decomposition we plan for CV32E40P, but BMC-only ("proof core coverage" percentages, not proofs) — good ammunition for our "BMC as falsifier only" stance |
| Abadi–Lamport refinement mappings + history/prophecy (1991, and Lamport–Merz 2022 restatement) | **Adopt as the theoretical basis; history suffices for exactly-once tagging** | Our exactly-once ghost tags are trace-prefix functions → history-variable regime; prophecy will be needed later for speculation/flush ghost state, flagged as a known future need |
| Abadi–Lamport "Conjoining Specifications" circular rule (1995) | **Superseded for us by McMillan/NT** | Shown incomplete by NT; McMillan's simpler rule + hand-added ghost strengthening covers what we need |
| OBI formal artifacts | **None exist — we are first** | Confirmed by direct repo read; raises the bar on getting our own Lean OBI model right, no second formal opinion available |
| AXI/AMBA formal artifacts (ARM's own, "Amazon's," academic) | **None substantiated at contract tier; monitors only, mostly proprietary** | Could not confirm an "Amazon AXI" artifact as the brief assumed; only prose specs (ARM) + proprietary/beta SVA monitors found |
| Interface automata (de Alfaro–Henzinger) | **Adopt vocabulary (I/O alphabets, alternating refinement); reject ∃-environment compatibility as our correctness criterion** | Genuine disagreement: IA is optimistic/∃-environment, we need ∀-environment for deployment correctness; IA's compatibility check is useful only as a separate non-vacuity sanity lemma |
| TLM refinement literature | **Weak, nothing to adopt** | No formal-semantics standard for SystemC TLM exists; our own `Sv.transaction` example already operates above this literature's typical (BMC/ABV) assurance tier |
