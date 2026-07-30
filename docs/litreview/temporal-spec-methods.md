# Area A — Temporal Specification Methods for Hardware

Scope: LTL/CTL/PSL/SVA lineage; TLA+/TLA; timed/bounded logics; shallow vs deep
temporal embeddings in ITPs; runtime-verification monitor synthesis beyond
Dobis LATTE'25; GR(1)/reactive synthesis. Evaluated against our settled
positions: bounded response over unbounded liveness, fairness bundled into
oracle legality, shallow trace-combinator embedding, specs mention ports
only, symbolic parameters, kernel proofs + untrusted BMC falsifier. Does
**not** re-review Choi/Kim/Kang OOPSLA'25, DVRTL, Fjfj/Kami, Dobis LATTE'25,
or bv_decide-style certificate checking — those are prior adoptions.

**Honesty note on depth.** One source was read in full via the PDF tool
(Lamport's "Safety, Liveness, and Fairness" note, all 8 pages) — claims
attributed to it below are read-the-source-grade. Everything else in this
section is abstract/search-result-grade (WebSearch summaries plus, in a
couple of cases, a paper's own abstract/landing page) — I flag this
per-item rather than let venue/year precision imply I read the PDFs.

---

## 1. LTL/CTL/PSL/SVA lineage and the safety fragment

**Alpern & Schneider, "Defining Liveness," Information Processing Letters
21(4), 1985.** [skim-grade, but corroborated by Lamport's note, which I read
in full and which cites it as ref [2]] Founding safety/liveness
decomposition: every property = safety ∩ liveness; safety = "bad prefix
exists ⇒ violated," liveness = "every finite prefix extendable to a good
infinite behavior." This is the topological vocabulary everyone below
inherits.

**Chang, Manna & Pnueli's safety-progress hierarchy** (surveyed via later
treatments, e.g. Manna & Pnueli's *Temporal Verification of Reactive
Systems*, and the "Safety-Progress Classification" chapter literature)
[skim-grade]: refines safety/liveness into six classes — safety, guarantee,
obligation (safety∧guarantee combinations), response, persistence,
reactivity — with matching automata (deterministic safety/co-safety up
through Streett/Rabin) and Borel-hierarchy correlates (closed, open, Fσ,
Gδ, ...). Gives a name for where our current fragment sits: LATTE'25-style
bounded SVA (`|->`, `##k`) is squarely in the **guarantee** class (bounded
witness of good prefix); unbounded `[*]` repetition or `s_eventually`
without a bound moves into **response**/**persistence**.

**PSL (IEEE 1850) and SVA (IEEE 1800 ch.16-17)** [skim-grade]: both
standardize an LTL-with-regular-expressions temporal layer over the same
event-driven/cycle sampling discipline we model; industrial PSL/SVA usage
skews overwhelmingly toward the safety/guarantee fragment (bounded `|->`,
`throughout`, `until!`) precisely because that is what commercial formal
tools can check efficiently — this is independent, industry-side
corroboration of "bounded response is what the field actually specifies,"
converging with our position from the tooling-economics direction rather
than the semantics direction.

**Verdict: USEFUL-IDEA-ONLY** — the safety-progress hierarchy is good
vocabulary for classifying `⊨sva`'s current vs. future fragment in our own
docs, but it's a classification scheme for automata-theoretic model
checking, not machinery we import; our shallow embedding already gets
"what class is this property" for free by inspection of the Lean
proposition.

---

## 2. TLA+/TLA (Lamport) — refinement-as-implication and fairness

**Lamport, "Safety, Liveness, and Fairness," 26 May 2019 TLA+ note — READ IN
FULL (8 pp., fetched and read end-to-end).** Precise definitions, useful
for direct comparison against our `Sv.Deterministic`/`ScheduleOracle`
design:

- **Behaviors as `Nat → State`**, properties as predicates on behaviors,
  stuttering-insensitivity as the header property every TLA+ formula has by
  construction (so refinement can add/remove stutter steps for free). Our
  cycle-indexed traces are *not* stuttering-quotiented (a design choice —
  `⊑@clk[from rst]` samples every posedge, doesn't need a stutter
  equivalence), so this machinery doesn't transplant directly, but it
  explains *why* TLA+ needs it and we currently don't: we fix the sampling
  grid (clock edges) instead of letting the implementation take an
  arbitrary number of "internal" steps per spec step.
- **Machine closure**: pair (S = safety, L = liveness) is machine closed
  iff every finite S-satisfying prefix extends to an (S∧L)-satisfying
  infinite behavior. Lamport's own gloss: *"Specifications that aren't
  machine closed are hard to understand because you can't tell if a step is
  allowed just by looking at the Next action."* This is exactly the
  discipline our `ScheduleOracle` needs to satisfy for "fairness bundled
  into oracle legality" to be sound: **the legality predicate on σ must be
  machine-closed against the design's step relation**, i.e. every
  σ-legal-so-far prefix must be extendable to a σ-legal infinite schedule —
  otherwise "quantify over legal σ" can vacuously exclude real runs and the
  ∀σ theorems overclaim. This is a checkable proof obligation we don't
  currently state anywhere.
- **WF_v(A) / SF_v(A)** (weak/strong fairness on action A w.r.t. state
  function v): both defined via five equivalent phrasings (my favorite
  operationally: WF = "infinitely enabled ⇒ infinitely taken", SF =
  "infinitely often enabled ⇒ infinitely taken" — note SF ⇒ WF, not
  conversely). A conjunction of countably many WF/SF conditions is proved
  (sketch given in the note) to still be a fairness property for S by an
  explicit round-robin extension algorithm. This is the standard vocabulary
  for whatever our arbiter-class liveness examples (gallery #19,
  `arb2_no_starvation`) are secretly assuming about the schedule oracle —
  worth borrowing the *names* WF/SF even if we never need the general
  countable-conjunction machinery (finite designs, finite process counts).
- Cites **Abadi & Lamport, "The Existence of Refinement Mappings," TCS
  82(2), 1991** and **Lamport, "Auxiliary Variables in TLA+"** for history/
  prophecy variables — see §5 below, this is the direct answer to research
  question 3.

**Lamport, "The Temporal Logic of Actions," ACM TOPLAS 16(3), 1994**
[skim-grade]: the source of refinement-as-implication (`Impl ⇒ Spec` as
plain logical implication over behaviors, because both are formulas over
the same universe of behaviors) — the architectural idea our `⊑@clk` already
executes at cycle granularity, just without TLA's generality (we don't need
stuttering/refinement-mapping generality because our abstraction step is
fixed at "one clock edge").

**Verdict: USEFUL-ADOPT (machine closure as a proof obligation on
`ScheduleOracle`; WF/SF as naming for oracle-legality fairness clauses) /
USEFUL-IDEA-ONLY (refinement-as-implication architecture — confirms our
`⊑@clk` design pattern, nothing new to import).** One concrete, low-cost
action item: state and discharge a `ScheduleOracle.machineClosed` lemma
once, analogous to `fuelMono` — turns "fairness bundled into oracle
legality" from a slogan into a checked theorem.

**Merz, embedding of TLA in Isabelle/HOL** (`homepages.loria.fr/SMerz/
projects/isabelle-tla/`; ships in the Isabelle distribution) [skim-grade,
documentation-level only — did not read the underlying papers (Merz's PhD
thesis "The Specification Language TLA+", or the CADE/TPHOLs papers)]:
embeds "raw" (stuttering-sensitive) TLA as HOL predicates over behavior
sequences, using Isabelle's object-logic machinery for concrete surface
syntax; **Isabelle/TLA+** is a newer, closer encoding of full TLA+ semantics
in the same style. Two decades of continuous use (still shipped) is
evidence the "temporal operators = ordinary HOL/Lean functions over
`Nat → State`" shallow-embedding architecture is durable, not a shortcut
that breaks down at scale — direct precedent validating our `Sv.always` /
`Sv.eventually` / `Sv.onPosedgeIdx` design (functions taking a trace and a
cycle index, returning `Prop`).

**Verdict: USEFUL-IDEA-ONLY** — confirms our architecture is the field's
default choice for temporal-logic-in-an-ITP, no specific lemma/tactic to
port (I did not get far enough into Merz's material to extract concrete
transplantable lemmas — flagging as a gap if this area gets a follow-up
pass).

---

## 3. Timed/bounded logics — is there prior art for "leads-to-within-k" as
first-class?

Yes, extensively, predating our project by 30-40 years — but concentrated
in a *different* verification community (real-time/embedded systems,
model checking) than the ITP-for-hardware community. None of it hands us
Lean machinery; all of it hands us positioning and vocabulary.

- **Jahanian & Mok, "Safety Analysis of Timing Properties in Real-Time
  Systems," IEEE TSE 12(9), 1986.** [skim-grade] Real-Time Logic (RTL):
  events + explicit occurrence-time terms, safety-checked via a
  (semi-)decision procedure. RTL's entire founding premise is that
  real-time/embedded correctness statements are properly stated as
  bounded-occurrence constraints between events ("event B occurs within k
  of event A"), not qualitative eventualities — the closest 1980s
  antecedent I found to "bounded response is the honest spec," though
  aimed at general real-time software/embedded systems, not synchronous
  digital hardware specifically.
- **Emerson, Mok, Sistla & Srinivasan, "Quantitative Temporal Reasoning,"
  CAV 1990 / Real-Time Systems 4(4), 1992.** [skim-grade] RTCTL: CTL plus
  bounded modalities `EU≤k`, `AU≤k` (and derived `EF≤k`, `AF≤k`), same
  model-checking complexity as CTL. This is the closest *branching-time*
  formal cousin of our "leads-to-within-k": the paper's stated motivation
  is explicitly that pure qualitative CTL (`AF p`, unbounded "eventually")
  is *insufficient* for real-time systems and the bounded operator is the
  thing designers actually need to state and check. Model-checking-based
  (fixed finite Kripke structure), not a deductive/∀-parameter proof
  method — doesn't transplant as a proof technique, but is strong,
  citable, decades-old prior art for the *position*.
- **Koymans, "Specifying Real-Time Properties with Metric Temporal Logic,"
  Real-Time Systems 2(4), 1990** (MTL) and **Alur, Feder & Henzinger,
  "The Benefits of Relaxing Punctuality," JACM 43(1), 1996** (MITL, the
  decidable interval-constrained fragment of MTL over dense time)
  [skim-grade, both]: the dense/continuous-time lineage — `p U_{[a,b]} q`
  with real-valued bounds, whose entire technical content (punctuality's
  undecidability, MITL's non-punctual relaxation to regain decidability) is
  about problems that **don't exist in discrete cycle time**: "exactly k
  cycles" is just a `Nat`, trivially decidable, no continuous-time
  automaton theory required. This is useful mainly as a *negative* data
  point — it tells us our discrete, cycle-indexed setting sidesteps the
  entire MTL/MITL decidability apparatus, so none of it needs adopting.
- **Konrad & Cheng, "Real-Time Specification Patterns," ICSE 2005**
  [skim-grade]: extends the Dwyer/Avrunin/Corbett pattern catalog (below)
  with real-time variants (Bounded Response, Bounded Invariance, Bounded
  Existence, Periodic, ...) formalized in MTL/TCTL/RTGIL, aimed at helping
  non-logicians write correct timed requirements. A ready-made idiom
  checklist — useful for making sure `docs/sv-spec-surface.md`'s eventual
  `Sv.*` deadline-helper vocabulary covers the patterns practitioners
  actually reach for, beyond just "leads-to-within-k."
- **Dwyer, Avrunin & Corbett, "Patterns in Property Specifications for
  Finite-State Verification," ICSE 1999** [skim-grade]: the (untimed)
  parent catalog — Response, Constrained Response, Response Chain, Bounded
  Existence, etc. — empirically covers ~80% of 500 collected industrial LTL/
  CTL requirements. Same use: idiom checklist, not machinery.
- **Kupferman & Vardi, "Model Checking of Safety Properties," CAV 1999**
  and the **bounded-model-checking completeness-threshold** line (Biere,
  Cimatti, Clarke, et al.) [skim-grade]: operationalizes "liveness on a
  finite-state system is secretly bounded" — completeness threshold for
  `◇p` is the *recurrent diameter* (longest loop-free path), so any
  liveness property on a genuinely finite-state design (e.g. `arb2`, or any
  bounded-width CV32E40P unit at a *fixed* parameter instantiation) has
  *some* true numeric bound, whether or not the spec states it. This is a
  formal reason our example 19 (`arb2_no_starvation`'s unbounded `∃m`
  strengthens to `∃ m ≤ n+2`) is not a coincidence — it's the generic
  finite-state phenomenon these completeness-threshold results
  characterize. Important caveat for our program specifically: **this
  argument needs finiteness, and our headline design law is `∀`-width
  symbolic parameters** — a completeness threshold computed for one width
  need not extend uniformly to "the same bound works for every width."
  That's exactly the gap our deductive (not model-checked) proof of the
  2-cycle bound has to close by hand, and it is a genuine extra burden a
  pure finite-state RTCTL/BMC treatment never faces.

**Verdict, whole cluster: USEFUL-IDEA-ONLY.** Strong, citable, 30-40-year
precedent that "state the bound, don't hide behind an unbounded
eventually" is a recognized position in real-time systems (RTL, RTCTL,
real-time patterns) — useful ammunition/positioning for docs, and a
vocabulary/idiom source (Konrad-Cheng's pattern names) — but zero directly
reusable Lean lemmas or tactics, since all of it is model-checking or
dense-time machinery aimed at problems (undecidable punctuality, fixed
finite Kripke structures) that our discrete, symbolic-width, deductive
setting doesn't have.

---

## 4. Shallow vs. deep temporal embeddings in proof assistants

- **Coupet-Grimal, "An Axiomatization of Linear Temporal Logic in the
  Calculus of Inductive Constructions," Journal of Logic and Computation
  13(6), 2003** (code: `coq-contribs/ltl`) [abstract-grade for the paper;
  README-grade for the repo, both fetched]. Program executions = infinite
  co-inductive lists of states; temporal operators implemented as
  co-inductive types when they're greatest fixpoints (e.g. `□`, `always`)
  and inductive types when they're least fixpoints (e.g. `◇`, `eventually`)
  — i.e., the fixpoint *polarity* of the operator dictates whether Coq sees
  it as induction or coinduction, and getting this right is what makes the
  "several generic lemmas... elegant and efficient reasoning in practical
  cases" (their own claimed payoff) actually work. The library explicitly
  ships **safety**, **liveness**, **fairness**, and a **`leads_to_via`**
  relation plus a termination lemma for "B holds until C" — i.e. this is a
  *direct* prior instance of a shallow trace-combinator library with almost
  exactly our vocabulary (`Sv.always`/`Sv.eventually`/leads-to), just over
  Coq co-inductive streams instead of Lean `Nat → State` functions.
  **This is the single closest prior-art match to research question 2**
  ("best prior art for a trace-combinator library over cycle-indexed traces
  in an ITP") that I found, even though its traces are unindexed
  co-inductive streams rather than `Nat`-indexed functions like ours (a
  design difference worth being deliberate about: co-inductive streams give
  you `always`/`eventually` "for free" as (co)fixpoints but push you toward
  proof-by-(co)induction on the stream constructor, whereas our
  `Nat → State` function representation makes "leads-to-within-k" a
  first-class, ordinary `∃ m ≤ n + k` statement with no coinduction
  needed at all — arguably a better fit for a *bounded*-response-first
  design, since bounded properties are then just ordinary finite
  quantification, no fixpoint machinery required).
- **Wan, "Formal Proof of a Machine Closed Theorem in Coq," Journal of
  Applied Mathematics, 2014 (article 892832)** [abstract-grade only — the
  Hindawi page 403'd, worked only from the abstract/search snippet]:
  formalizes Abadi-Lamport machine closure itself as a Coq theorem, via a
  syntax-independent shallow embedding, with "a useful proof pattern of
  constructing a trace with desired properties." Directly relevant to the
  `ScheduleOracle.machineClosed` proof obligation flagged in §2 — if we
  ever discharge that obligation in Lean, this is the paper to check for
  the trace-construction proof pattern (their core technical device, per
  the abstract, for proving a machine-closed pair admits an extension).
- **Merz's Isabelle/TLA(+)** — see §2; same cluster of "shallow embedding
  of a temporal logic as functions over `Nat`/co-inductive traces," now the
  third independent instance (Coq/Coupet-Grimal, Coq/Wan, Isabelle/Merz) —
  the convergence itself is the finding: three unrelated formalization
  efforts in two different provers landed on the same shallow-embedding
  shape we already chose. Nobody in this cluster reports having tried deep
  embedding a general temporal logic (formula ASTs + a satisfaction
  relation) for full-scale proof work and preferring it — consistent with
  our own choice, though I did not find an explicit shallow-vs-deep
  *comparison/retrospective* paper for temporal logic specifically (the
  Coq "Deep Embedding v.s. Shallow Embedding" papers that turned up in
  search are about program logics/Hoare calculi, not temporal logic, so I
  am not citing them here).
- **Interaction Trees, Xia et al., POPL 2020** [background knowledge, not
  freshly searched this session]: coinductive event trees for denotational
  program semantics (Vellvm, DeepSpec-adjacent), not a temporal-*logic*
  library — mentioned only because it's the field's other well-known
  large-scale "shallow coinductive trace combinator" success story in Coq,
  evidence the general approach scales past toy examples, but it answers a
  different question (program denotation, not property specification) so
  it isn't the direct match Coupet-Grimal is.

**Verdict: USEFUL-IDEA-ONLY overall, with one concrete borrow.** The
architecture is validated three times over (adopt nothing new — we're
already doing it); Coupet-Grimal's `leads_to_via` naming/shape and the
inductive-vs-coinductive fixpoint-polarity discipline are worth a skim
before finalizing `Sv.eventually`'s exact definitional shape, in case our
bounded-first design still wants an *unbounded* fallback for the honest
`s_eventually` corner (gallery #19 already needs one). Wan 2014 is
USEFUL-ADOPT-conditional: only if/when we actually formalize
`ScheduleOracle.machineClosed` (§2's action item) — worth a real read at
that point, not before.

---

## 5. Spec-side ghost/auxiliary state for hardware traces (research
question 3)

- **Abadi & Lamport, "The Existence of Refinement Mappings," Theoretical
  Computer Science 82(2), 1991** (LICS'88 originally) [skim-grade, but
  corroborated as ref [1] in the Lamport note I read in full]. The
  canonical answer to this question. Two auxiliary-variable devices:
  - **History variables** — remember information from past states, added
    to a spec so that a refinement mapping (concrete state ↦ abstract
    state) becomes *definable*, when the "obvious" mapping isn't a
    function of the current concrete state alone.
  - **Prophecy variables** — the forward-looking dual: predict future
    states, needed when the abstract state depends on choices the
    concrete system hasn't made observable yet.
  - Main theorem (per multiple secondary sources, not verified against the
    primary proof): refinement mappings can *always* be found by adding
    history and prophecy variables, for specifications satisfying certain
    (internal-continuity-type) conditions — i.e. this isn't just a trick,
    it's complete for the class of specs TLA can express.
  - **Direct payoff for us**: our own gallery already does history-variable
    engineering by hand and doesn't name it as such — example 10
    (`tri_acc`) latches the live port `n` into internal register `n_q` "at
    acceptance," and the writeup explicitly notes *"comparing against the
    live port instead... falsifies it."* That is exactly an
    Abadi-Lamport history variable (`n_q` records "the value of `n` at the
    moment the request was accepted") solving exactly the problem their
    paper characterizes (the abstract/spec-level transaction value is not
    a function of the *current* concrete state, only of concrete state
    *history*). Naming this and lifting Abadi-Lamport's existence
    conditions into a reusable checklist ("does this `⊑@clk`/`Sv.transaction`
    proof need a fresh history field, or is the existing register file
    already sufficient witness state?") would turn a recurring ad hoc
    design decision into a principled one.
- **Lamport, "Auxiliary Variables in TLA+"** (web page, cited as ref [3] in
  the note read in full) [not independently fetched]: the TLA+-flavored
  practitioner treatment of the same material — likely the more directly
  transplantable read (closer to "how do you actually write it," vs.
  Abadi-Lamport's existence *theorem*).
- **Lamport & Merz, "Prophecy Made Simple," ACM TOPLAS, 2022** (also a 2020
  preprint) [skim-grade]: modernizes/simplifies prophecy variables. We
  don't currently need prophecy (nothing in our gallery requires a spec to
  reference a not-yet-determined future value at an earlier cycle — our
  bounded-response style resolves this by just waiting for the deadline
  instead of prophesying the answer early), but flagging it now: the
  moment sv_vcgen reaches pipelined designs where a spec wants to relate an
  *issue-cycle* signal to a *retirement-cycle* result before retirement has
  happened (plausible for CV32E40P's pipeline-stage contracts, D7 in the
  banked sv_vcgen design), prophecy variables are the named literature
  answer, not a symptom to design around ad hoc.
- **Jung, Lepigre, Parkinson, Vafeiadis et al., "The Future is Ours:
  Prophecy Variables in Separation Logic," POPL 2020** [skim-grade]: modern
  separation-logic treatment of prophecy for concurrent-program
  verification — likely not directly relevant (our state is a flat
  register file, not a heap), listed only for completeness since it
  surfaced repeatedly in search alongside Lamport & Merz.

**Verdict: USEFUL-ADOPT.** This is the strongest, most concretely
actionable finding in this whole section: Abadi-Lamport gives a name,
existence theorem, and design checklist for something we are already doing
by hand (`n_q`-style latching) with no theory backing it. Concrete next
step (small, cheap): write one paragraph in `docs/sv-spec-surface.md`'s
`Sv.transaction` discussion naming `n_q` as a history variable in the
Abadi-Lamport sense, and add "does this proof need a fresh history field"
as an explicit checklist item in the sv_vcgen design notes (D2/D4 in the
banked campaign spec) rather than rediscovering the pattern per-example.
Prophecy variables: **USEFUL-IDEA-ONLY / park it** — no current need,
revisit only when pipeline-stage contracts (P5/D7) actually require
referencing a future value early.

---

## 6. Runtime verification / monitor synthesis beyond Dobis LATTE'25

- **Havelund & Roşu, "Synthesizing Monitors for Safety Properties," TACAS
  2002** [skim-grade]: past-time LTL → dynamic-programming monitor
  algorithm, linear time / constant memory in trace length, one of the
  founding papers of the "compile a temporal formula to an executable
  monitor" line LATTE'25 (Dobis) sits in for SVA specifically. Confirms the
  general "monitor synthesis with a correctness proof against the source
  formula" pattern (which is exactly what we already committed to:
  `monitor_correct : (d.withMonitor p ⊨ safeMonitorState) ↔ (d ⊨sva p)`) has
  20+ years of precedent beyond LATTE'25's specific bounded-SVA proposal —
  reinforces confidence in the pattern, nothing new to port (their
  algorithm is for *past-time* LTL over software event traces; our target
  is *future* bounded SVA over hardware cycles, different enough that the
  algorithm itself doesn't transplant).
- **Bauer, Leucker & Schallhart, "Comparing LTL Semantics for Runtime
  Verification," Journal of Logic and Computation 20(3), 2010** (RV-LTL)
  [skim-grade]: the standard reference for **monitorability** — the paper's
  headline result is that the monitorable fragment (properties for which
  *some* finite observation can be conclusive) is **strictly larger** than
  safety ∪ co-safety, and it gives a 4-valued (later refined) semantics for
  what a monitor should report on a finite prefix (true / false /
  presumably-true / presumably-false, in follow-on work). This is the
  precise theory we'd need if `⊨sva`/`#sv_check` is ever extended to report
  something honest about an *unbounded* SVA property (`s_eventually`, `[*]`
  without a bound) under finite simulation — today our `⊨sva` fragment
  (LATTE'25-style bounded properties) is safety/guarantee, hence trivially
  monitorable in the classical (Kupferman-Vardi) sense, so we don't need
  this machinery *yet*, but the moment `Sv.FinishesBy`-style or
  gallery-#19-style unbounded properties get their own `⊨sva` treatment,
  this paper's monitorability classes tell us in advance which fragments a
  runtime `#sv_check`-style oracle could ever soundly answer, vs. which are
  fundamentally "wait forever" properties no simulator run can resolve —
  useful as a pre-emptive scope-limiting argument for docs.
- **D'Angelo, Sankaranarayanan et al., "LOLA: Runtime Monitoring of
  Synchronous Systems," TIME 2005** [skim-grade]: stream-based
  specification language purpose-built for **synchronous systems including
  circuits** — output streams defined by equations over input streams
  (and other output streams, with bounded look-ahead/-behind offsets),
  online monitoring via incremental partial evaluation. This is the
  closest runtime-verification-community analog to "trace combinators over
  cycle-indexed traces" that I found *outside* the ITP world — its
  stream-equation notation (`out[t] = f(in[t], in[t-1], out[t+1])`-style)
  is a plausible notational ancestor for how our `Sv.*` combinators read,
  even though LOLA compiles to an executable monitor rather than producing
  Lean proof terms — it has no proof theory, it's a checker, so it's an
  ergonomics/naming source, not a machinery source.
- **Copilot (Pike, Goodloe, et al.), Haskell-embedded stream DSL, used at
  NASA for UAV/embedded hardware monitors** [skim-grade, general
  awareness]: another shallow-embedded stream-combinator language
  (host language Haskell, same "specs mention only observable
  streams/ports" ethos), compiled to constant-memory hard-real-time C for
  embedded/hardware targets. Real-world validation that the shallow
  stream/trace-combinator style, hosted in a general-purpose language,
  scales to deployed safety-critical hardware monitors — again an
  ergonomics/precedent data point, not adoptable machinery (no proof
  obligations, it's a compiler not a prover).

**Verdict, whole cluster: USEFUL-IDEA-ONLY.** Havelund-Roşu and
Bauer-Leucker-Schallhart are the right citations if we ever write the
"why is `⊨sva`'s fragment what it is" paragraph properly (monitor-synthesis
pedigree + monitorability theory delimiting what any online oracle could
ever certify); LOLA and Copilot are notation/ergonomics precedent for the
trace-combinator surface, not proof machinery. Nothing here changes current
`⊨sva`/LATTE'25 scope — all of it is either subsumed by what we already
adopted or answers a question (finite-prefix monitorability) we haven't
asked yet.

---

## 7. GR(1) / reactive synthesis

**Bloem, Jobstmann, Piterman, Pnueli & Sa'ar, "Synthesis of Reactive(1)
Designs," Journal of Computer and System Sciences, 2012 (conference version
VMCAI 2006)** [skim-grade]. GR(1) specs = initial + safety + **justice**
(infinitely-often) assumptions and guarantees, both on environment
(input) and system (output) sides; winning condition
`(□◇p₁∧...∧□◇pₘ) → (□◇q₁∧...∧□◇qₙ)`; polynomial symbolic synthesis via a
game-solving fixpoint algorithm.

Relevance to our design: GR(1)'s structural move — **fairness/justice
lives on the environment-assumption side of an implication, not as a
property the system must prove unconditionally** — is the same shape as
our "fairness bundled into oracle legality": σ's legality constraints play
the role GR(1)'s environment-justice assumptions play (both say "we don't
promise anything for schedules/environments that behave unfairly forever;
we only quantify over the ones that don't"). Seeing this as a named,
well-studied pattern (assume-guarantee reactive synthesis) rather than a
project-specific expedient is reassuring, and GR(1)'s justice-assumption
side conditions (realizability requires the assumption itself be
satisfiable/fair, or the spec is vacuously "synthesizable" by refuting the
environment) is a sharp reminder of exactly the vacuity failure mode this
project has hit twice already in the SPICE lane (non-vacuity witnesses) —
worth an explicit non-vacuity check on `ScheduleOracle`'s legality
predicate too (does *some* σ actually satisfy it? — probably yes trivially
by construction via `choose_perm`, but it's the same shape of question GR(1)
realizability checking asks first, before anything else).

GR(1)'s actual payload — polynomial-time symbolic *synthesis* (build a
correct-by-construction Mealy machine) — is irrelevant to us: we verify a
fixed, already-designed RTL file, we don't synthesize one, and we don't
want a model-checking/game-solving TCB anywhere near the kernel proof.

**Verdict: USEFUL-IDEA-ONLY** — validates the assumption-side-fairness
architecture by analogy, and its realizability-vacuity discipline is a
useful cross-check to add to `ScheduleOracle`, but the synthesis machinery
itself (game solving) is NOT-FOR-US (wrong problem: we prove, not
synthesize).

---

## Key-question summary

**(1) Has anyone formalized "bounded response as the honest hardware spec"
as an explicit position?** Partially, and with an interesting asymmetry.
The real-time-systems community (Jahanian-Mok RTL 1986, RTCTL
Emerson-Mok-Sistla-Srinivasan 1990/92, Konrad-Cheng real-time patterns
2005) has argued for 35-40 years that bounded occurrence/response
constraints are what real-time/embedded correctness statements *actually
are*, in explicit contrast to qualitative "eventually" — this **supports**
our position, but from outside the ITP-for-hardware world, and stated as
"the practical requirement is bounded" rather than as an epistemic claim
about honesty. Lamport, in the one primary source read in full here, makes
almost the mirror-image argument for TLA+/software: he **agrees** the bound
is what we "really care about," but treats stating it as **impractical**
("distracting timing assumptions") and defends *unbounded* liveness as the
honest-enough approximation for general software — i.e. Lamport's reason
for *not* going bounded (the bound is hard to justify/state in general
async software) is precisely the reason that evaporates in synchronous
digital hardware, where the clock cycle is already the design's native
unit and (per Kupferman-Vardi/BMC completeness-threshold theory) a true
bound always exists for any fixed-width finite-state design — our position
sharpens rather than contradicts his, but the tension is real and worth
stating explicitly rather than glossing: hardware is the special case where
Lamport's own tradeoff comes out the other way, and our added twist (∀-width
symbolic designs) reopens a version of his objection, since a bound proved
for one width is not automatically a bound for all widths and each `∀`-width
bounded-response theorem has to actually re-derive that. I found no single
paper stating our exact position ("bounded response is the honest spec,
specifically for hardware, specifically as a contrast to TLA-style
unbounded liveness") — it appears to be a genuine synthesis, not
independently discovered, though every ingredient (RTL/RTCTL's bound-first
stance, Lamport's own honesty-vs-practicality framing, Kupferman-Vardi's
finite-state bound-always-exists result) is separately in the literature.

**(2) Best prior art for a trace-combinator library over cycle-indexed
traces in an ITP?** Coupet-Grimal's shallow LTL-in-Coq axiomatization
(J. Logic & Comput. 2003, code `coq-contribs/ltl`) is the closest direct
match — co-inductive-stream traces, `always`/`eventually`/`leads_to_via` as
(co)inductive combinators, explicitly reusable Coq libraries. Merz's
Isabelle/TLA(+) is the closest *architectural* match (state sequences
indexed the way ours are, `Nat`-style rather than raw coinductive streams)
though I only have documentation-level knowledge of it, not the underlying
papers. Wan's 2014 machine-closure-in-Coq paper is the closest match for
the specific *trace-construction proof pattern* we'd need if we ever prove
`ScheduleOracle` machine-closed. None of the three hand us Lean code
directly transplantable, but Coupet-Grimal's design choice (fixpoint
polarity ↦ induction vs. coinduction) is worth deliberately confirming or
rejecting when `Sv.eventually`'s unbounded form is finalized.

**(3) Anything on spec-side ghost/auxiliary state for hardware traces
(history variables)?** Yes, decisively: Abadi & Lamport, "The Existence of
Refinement Mappings" (TCS 1991), is exactly this, complete with an
existence theorem for when history/prophecy variables suffice to build a
refinement mapping. Our own gallery example 10 (`tri_acc`'s `n_q` latch) is
already an unnamed instance of their history-variable device; this is the
single most directly actionable finding in the whole section — worth
formally naming and turning into a checklist item for future `⊑@clk`/
`Sv.transaction` proofs rather than re-deriving ad hoc each time.

---

## Verdict table

| Method / paper | Verdict | One-line why |
|---|---|---|
| Alpern-Schneider safety/liveness decomposition (1985) | USEFUL-IDEA-ONLY | Vocabulary only; our shallow embedding gets the classification for free |
| Chang-Manna-Pnueli safety-progress hierarchy | USEFUL-IDEA-ONLY | Names where `⊨sva`'s fragment sits (guarantee), no machinery |
| PSL/SVA (IEEE 1850/1800) standardization | USEFUL-IDEA-ONLY | Industry corroboration that practice already lives in the bounded/guarantee fragment |
| Lamport, "Safety, Liveness, and Fairness" (2019, read in full) | USEFUL-ADOPT | Machine closure is the missing proof obligation on `ScheduleOracle`; WF/SF naming for oracle-legality fairness |
| Lamport, TLA (1994) refinement-as-implication | USEFUL-IDEA-ONLY | Confirms `⊑@clk`'s architecture; nothing new, we're more concrete (fixed clock-edge grid, no stuttering quotient needed) |
| Merz, Isabelle/TLA(+) | USEFUL-IDEA-ONLY | Validates shallow-embedding-over-`Nat→State` as durable field practice |
| Jahanian-Mok RTL (1986) | USEFUL-IDEA-ONLY | Decades-old precedent for bounded-occurrence-as-the-real-spec; positioning, not code |
| RTCTL (Emerson-Mok-Sistla-Srinivasan, 1990/92) | USEFUL-IDEA-ONLY | Bounded-until `U≤k` is the branching-time cousin of leads-to-within-k; model-checking algorithm, not deductive |
| MTL (Koymans 1990) / MITL (Alur-Feder-Henzinger 1996) | NOT-FOR-US | Dense/continuous-time decidability apparatus solves problems discrete cycle time doesn't have |
| Konrad-Cheng real-time specification patterns (2005) | USEFUL-IDEA-ONLY | Idiom checklist for naming future `Sv.*` deadline helpers |
| Dwyer-Avrunin-Corbett patterns (1999) | USEFUL-IDEA-ONLY | Same, untimed parent catalog |
| Kupferman-Vardi safety model checking / BMC completeness thresholds | USEFUL-IDEA-ONLY | Explains *why* finite-state liveness is secretly bounded; doesn't cover our ∀-width case |
| Coupet-Grimal, shallow LTL in Coq (2003) | USEFUL-IDEA-ONLY | Closest direct trace-combinator-library precedent; fixpoint-polarity discipline worth checking against our design |
| Wan, machine closure in Coq (2014) | USEFUL-ADOPT (conditional) | The proof pattern to read if/when `ScheduleOracle.machineClosed` is attempted |
| Abadi-Lamport refinement mappings / history+prophecy vars (1991) | USEFUL-ADOPT | Names and gives an existence theorem for the `n_q`-style latching we already do ad hoc |
| Lamport-Merz, "Prophecy Made Simple" (2022) | USEFUL-IDEA-ONLY / park | No current need; revisit for pipeline-stage contracts (P5/D7) |
| Havelund-Roşu monitor synthesis (TACAS 2002) | USEFUL-IDEA-ONLY | 20-year-old precedent for the monitor-synthesis pattern; algorithm itself (past-time LTL) doesn't transplant |
| Bauer-Leucker-Schallhart monitorability / RV-LTL (2010) | USEFUL-IDEA-ONLY | Delimits what a future `#sv_check`-style oracle could ever certify for unbounded SVA; not needed for current bounded fragment |
| LOLA stream RV language (2005) | USEFUL-IDEA-ONLY | Closest RV-community trace-combinator notation for synchronous/circuit traces; no proof theory |
| Copilot (Haskell EDSL, NASA) | USEFUL-IDEA-ONLY | Real-world validation shallow stream-combinator style scales to deployed hardware monitors; no proof theory |
| GR(1) reactive synthesis (Bloem/Jobstmann/Piterman/Pnueli/Sa'ar 2006/2012) | USEFUL-IDEA-ONLY | Validates assumption-side-fairness architecture by analogy; realizability-vacuity check worth adding to `ScheduleOracle`; synthesis algorithm itself NOT-FOR-US |

---

## Concrete, low-cost action items surfaced

1. State (and eventually prove) `ScheduleOracle.machineClosed`: every
   finite σ-legal prefix extends to a σ-legal infinite schedule — turns
   "fairness bundled into legality" from slogan into checked property
   (Lamport 2019 / Abadi-Lamport 1991).
2. Name `n_q`-style latching explicitly as an Abadi-Lamport history
   variable in `docs/sv-spec-surface.md`'s `Sv.transaction` discussion; add
   "does this proof need a fresh history field?" as a checklist item in the
   sv_vcgen design notes.
3. When finalizing `Sv.eventually`'s unbounded form, deliberately decide
   induction-vs-coinduction fixpoint polarity by comparison with
   Coupet-Grimal's Coq LTL library rather than by accident.
4. Add a realizability/non-vacuity sanity check to `ScheduleOracle`'s
   legality predicate (does some σ satisfy it, cheaply, e.g. via
   `choose_perm`) — same shape as GR(1) realizability and the project's own
   recurring non-vacuity lesson from the SPICE lane.
5. Flag prophecy variables (Lamport-Merz 2022) as the literature answer
   *in advance*, for whenever pipeline-stage contracts (sv_vcgen D7/P5)
   need to relate an issue-cycle signal to a not-yet-computed
   retirement-cycle value.
