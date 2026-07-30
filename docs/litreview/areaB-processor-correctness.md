# Area B — Processor-correctness methodology
Literature review for the lean-surfaces project / CV32E40P program.
Read-the-source claims are marked **[primary]** (paper text or actual proof-assistant
source fetched and inspected); everything else is marked **[secondary]** (search-engine
summaries / secondary write-ups I did not verify against the primary text).

---

## 0. Where this sits relative to what we already adopted

Already reviewed and not re-litigated here: Choi/Kim/Kang OOPSLA'25's **discipline
metatheorem** (least-fixpoint ≡ standard scheduling semantics, proved once), DVRTL
contracts, Fjfj/Kami interface disciplines, Dobis LATTE'25 SVA-to-monitor lowering,
bv_decide-style certificates. This review goes one layer deeper on the *same* OOPSLA'25
paper (its actual RISC-V case study, which the earlier review didn't reach), and broader
into the classical processor-correctness literature (Burch-Dill and its two successor
lines) plus the CV32E40P-specific industrial record.

---

## 1. Burch-Dill flushing and its two successor lines

**Burch & Dill, CAV'94, "Automatic Verification of Pipelined Microprocessor
Control"** [secondary, well-corroborated]. The technique: build a *flushing function*
that drains the pipeline (lets in-flight instructions complete, injects no new ones)
to map an implementation state to an ISA state; then check the one-step diagram
commutes: `flush(step_impl(s)) = step_ISA(flush(s))`. Two properties made it durable
for 30 years: (1) it needs no manual invariant — the flushing function *is* the
abstraction map, found automatically for the control logic by symbolic simulation
with uninterpreted functions/terms (this is also why it was historically paired with
term-level decision procedures — EUF, "Positive Equality" — rather than bit-blasting);
(2) verification cost is independent of datapath width / register-file size / ALU
operation count, because data values are left as uninterpreted terms throughout.

**Known weakness, inherited by everyone downstream**: flushing assumes a *single*
instruction is "in flight to be checked" at a time (surrounded by flushes on both
sides) — it is fundamentally a **single-instruction correctness argument bootstrapped
by induction**, not a genuine multi-instruction interleaving argument. Corner-case bugs
that only manifest from the *interaction* of two or more simultaneously in-flight
instructions (classic hazard/forwarding bugs) can slip through a naively-applied
flushing proof if the invariant checked at the flush points doesn't capture enough
of the pipeline's internal state. This is exactly the failure mode later work
(Sawada-Hunt, Choi et al.) targets by keeping an explicit table/model of every
in-flight instruction instead of flushing them away.

**Velev & Bryant (DAC 2000), "Formal Verification of Superscalar Microprocessors with
Multicycle Functional Units, Exceptions, and Branch Prediction"** [secondary].
Extends flushing to multicycle/variable-latency functional units and memories, and
folds exceptions and branch prediction *into* the same EUF-with-"Positive Equality"
decision procedure rather than treating them as a separate proof layer — i.e. their
answer to "how do you handle exceptions" is: encode exception-taken as another
uninterpreted-term-valued control signal and let the same flushing commutation
diagram absorb it. This is squarely a **model-checking/decision-procedure**
methodology (their own later papers are literally about UCLID and automatic
term-level model checking), not a kernel proof — falls on our "untrusted-BMC-only"
side of the line if we were to reuse the technique.

**Sawada & Hunt (CAV'97 "Trace table based approach…"; and the later FM9801
out-of-order machine with Hunt as advisor)** [secondary, cross-checked against
multiple independent summaries]. This is the line that actually answers "how do you
handle precise exceptions/interrupts in a pipelined machine, mechanically." Their
correctness criterion is **not** flush-and-compare; it is an *invariant relating a
running implementation to an explicit ghost data structure*, the **MAETT**
(Micro-Architectural Execution Trace Table): one row per in-flight instruction,
recording which pipeline stage it occupies, its speculative/committed status, and
enough abstracted state to reconstruct what the ISA-level effect of committing it
will be. The correctness statement compares the *sequence of committed ISA states*
of the pipelined machine against the sequence produced by a non-pipelined reference
machine — **including in the presence of asynchronous external interrupts**: an
interrupt is modeled as an event that can be *taken* only at a committed instruction
boundary (never mid-flight), so the MAETT's per-instruction "commit" flag is exactly
the ghost state that makes "precise" (interrupts/exceptions appear to happen between
two whole instructions, never inside one) a provable, not assumed, property. The whole
thing is proved in ACL2 by induction on cycles with the MAETT invariant as the
induction hypothesis, hand-found by the verification engineer (not automatic, unlike
Burch-Dill) — this is the CAV'94→CAV'97 trade: give up automation, gain the ability to
state and prove precise-exception correctness for out-of-order machines with
speculation, which flushing cannot express at all (flushing has nothing to say about
*which* instruction an interrupt lands between).

**Verdict vs. our settled positions.** MAETT is the direct ancestor of what "exactly-once
retirement ghost state" means in a kernel proof, and it is closer to riscv-formal's RVFI
discipline than flushing is (§7 below draws the line explicitly). It also validates our
own instinct that a controller-like sequencing module needs an explicit per-instruction
tracking structure rather than a whole-pipeline flush argument. It is *not* itself a
precedent for bounded-response liveness — MAETT correctness is a safety property
(trace-of-commits equality up to the interrupt point); it says nothing about *how long*
an instruction may sit un-committed, which is exactly the gap our bounded-deadline
discipline is designed to close on top of it.

---

## 2. Choi/Kim/Kang OOPSLA'25 — the actual RISC-V case study, read from source

The earlier review covered the paper's headline contribution (least-fixpoint semantics,
discipline metatheorem). I went back to the **primary Rocq artifact**
(Zenodo record 10.5281/zenodo.16923443, `pfv.tar.gz`, `src/Ex/RvCore/*`) to answer the
brief's specific questions — the ACM PDF is Cloudflare-gated, but the artifact contains
the same theorem statements, unabridged. **[primary — read directly from the .v source]**

**The core.** `src/Ex/RvCore/Core.v` is a small in-order pipeline: a `frontend` module
(fetch+decode, with a `btb` branch-target-buffer predicting `pc_fetch_next`),
one execute stage, one writeback stage, with a misprediction-flush signal (`exec_bad`)
that re-steers `pc_fetch` from the BTB's prediction to the resolved `pc_exec`, and a
`d2e`/`e2w` valid/ready handshake pair providing the only pipeline stalling
(`e2w_avail`/`d2e_rdy`). Memory is a separate `Mem.v` data-cache module. It is
comparable in scope to Kôika's RV32I core (§3 below) — a small textbook-style in-order
pipeline, not CV32E40P-scale.

**The theorem, verbatim (`EndToEnd.v:74`):**
```
Theorem core_refine_riscv_formal btbf initial_imem
  (IMEM_OK: List.Forall (fun iv => 0 <= fst iv < 2 ^ 30) initial_imem):
    Beh.of_program (ModSemL.compile_itree (initialize (tgt btbf initial_imem)))
    <1=
    Beh.of_program (ModSemL.compile_itree (initialize (src initial_imem))).
```
i.e. **trace inclusion**: every observable behavior of the target (`tgt`, the pipeline
compiled to an ITree via the least-fixpoint Verilog semantics and interpreted through
`FormalSim.translate_riscv_output`) is also a behavior of the source (`src`, a
sequential RISC-V ITree built directly from `riscv-coq`'s `run1`/`Run.run1`, MIT's
existing off-the-shelf RISC-V Rocq spec, reused rather than reinvented). This is proved
by composing FreeSim's generic ITree "adequacy" theorem (simulation relation ⇒ trace
inclusion — a CompCert-style forward-simulation-implies-refinement lemma, imported as
a black box from the `FreeSim` library) with a hand-built simulation relation between
pipeline flop state and ISA state (`Sim.v`, `FormalSim.v`).

**The observable is thin — this is the load-bearing methodological fact.** The only
port treated as observable is `pc_commit`/`pc_commit_vld` (`EndToEnd.v:23-28`,
`riscv_ioE := Output (pc : Z)`): the trace being matched is *the sequence of committed
program counters*, nothing else. Register writeback data, memory writes, etc. are
**internal** to the simulation relation (used to prove the PC trace matches) but are
*not themselves part of the theorem's observable claim*. Compare this to RVFI (§7),
whose observable trace is the *much* richer per-instruction tuple (rd_addr/rd_wdata,
mem address/mask/data, trap flag, …) — Choi et al.'s case study is intentionally
minimal (enough to demonstrate the framework), not an attempt at RVFI-parity coverage.
This is a genuine methodological choice point for us: a PC-only refinement target is
far cheaper to state and prove but is silent on whether register/memory *values* are
correct — precisely the class of bug RVFI is designed to catch (wrong rd_wdata,
wrong mem_wdata) that a PC-only spec would miss entirely.

**Interrupt/exception story: there is none — and the paper is explicit that there is
none.** `src/Ex/RvCore/Machine.v:105-156` instantiates riscv-coq's `RiscvProgram`
interface with `getCSRField f := fail_hard`, `setCSRField f v := fail_hard`,
`getPrivMode := fail_hard`, `setPrivMode v := fail_hard`, `makeReservation/
clearReservation/checkReservation := fail_hard` (atomics), `fence _ _ := fail_hard`,
and crucially `endCycleEarly{A} := fail_hard` — `endCycleEarly` is riscv-coq's own hook
for "an exception was raised, end the instruction early"; wiring it to `fail_hard` means
the ISA-level spec is *undefined* the instant any instruction would trap (illegal
opcode, misaligned access, ECALL/EBREAK, CSR access — CSRs are entirely absent from the
decoder). `FormalSpec.v:105-113` confirms the consequence at the top level: `run1`
returning `None` routes straight to `ModSemE.triggerUB` — **"Error leads to UB"**, their
own comment. Since the refinement theorem is trace-*inclusion* against this spec, and
the spec becomes universally-quantified-away (UB permits any behavior) the moment a
trap would fire, **the theorem is vacuously true, and says nothing, for any program that
ever executes an instruction that would trap** — there is no privilege mode, no CSR
file, no external-interrupt input, no exception vector, nothing. This is not a
criticism of the paper (its stated contribution is the *semantics* and the *modular
verification method*, demonstrated on a case study — not RISC-V coverage completeness)
but it is the single most important scoping fact for our purposes: **the field's most
recent from-first-principles Verilog-to-ISA refinement result for a pipelined RISC-V
core explicitly does not attempt precise exceptions or interrupts.** CV32E40P's
interrupt controller, debug-mode entry/exit, and exception/CSR logic are *exactly* the
part of the design this precedent has nothing to say about — we inherit the Sawada-Hunt
MAETT tradition for that part, not the OOPSLA'25 one.

**"Progress guarantee" — and it is a bounded/well-founded argument, matching our own
design stance.** The paper's abstract advertises "functional correctness *and progress
guarantees*." In the proof (`Sim.v:135-441`) this cashes out as a simulation invariant
`pc_prediction_status` carrying a natural-number **token**, with an explicit step in the
proof (`Sim.v:288-334`, `:406-441`) that asserts `token' < token` on every pipeline cycle
that doesn't yet retire the awaited instruction, and case-splits on the invariant to
show the token *cannot* decrease forever without a commit happening. In other words:
"progress" here is not an abstract `◇P` fairness assumption discharged by an oracle —
it is a **concretely bounded, well-founded-measure argument**, cycle-counted, baked
directly into the same relation that proves functional correctness. This is a strong,
independent point of alignment with our "bounded response over unbounded liveness"
design law: even a paper that explicitly frames its contribution as including "progress
guarantees" ends up proving them via a decreasing rank function with a concrete bound,
not via an unbounded-eventually temporal operator.

**Role of the discipline metatheorem in this case study.** It is *not* re-invoked
per-module inside the RISC-V proof. The equivalence between the least-fixpoint
semantics and standard event-driven scheduling semantics (`StfStd.v`, Theorem 4.4 in
the paper) is proved **once, generically**, for any Verilog module whose fixpoint
computation terminates (a decidable syntactic/semantic side condition); the RISC-V case
study then works entirely inside the least-fixpoint/ITree world (`ModuleITree.v`) and
gets **module-level determinism "for free"** as a corollary
(`ModuleITree.v:142`, `Theorem determinism`, proved once for the generic
`module_itree` construction: same input trace ⇒ same output trace, no scheduler
quantification needed at all downstream). This is precisely the "discharge σ once,
reuse everywhere" shape we already adopted from this paper (D6 in our design notes) —
seeing it exercised end-to-end on the case study confirms the shape holds up in
practice, not just in the abstract metatheorem statement.

---

## 3. Kôika / "Essence of Bluespec" (Bourgeat, Pit-Claudel, Chlipala, Arvind, PLDI'20)

**[primary — read from the paper PDF]**. Kôika's RV32I core (§6.6, Appendix B: "4-stage
RISC-V processor (Fetch, Decode, Execute, Writeback), RV32I **without interrupts**")
is used **exclusively as a synthesis/performance benchmark** — area, critical path,
clock frequency, comparing Kôika-generated Verilog against a hand-written Bluespec
(BSV) twin, both run through Yosys/ABC on a 45nm PDK and Verilator/Vivado. There is
**no theorem in the paper claiming the RV32I core implements the RISC-V ISA** — I found
no refinement/simulation statement analogous to Choi et al.'s `core_refine_riscv_formal`
anywhere in the case-study section. The paper's actual formal content (§5,
"Characterization of a Pipelined System") is a *general, abstract* metatheorem proved
on a two-stage toy pipeline (`f1`∘`f2` composition): One-Rule-At-A-Time (ORAAT)
semantics — Kôika's core determinism guarantee, itself a discipline-metatheorem-shaped
result — implies the *scheduled/pipelined* circuit computes the same function as
running the rules in sequence, once the pipeline has filled. This generic composition
lemma is available to be applied to the RISC-V core but the paper does not do so.
**Verdict**: Kôika is a strong precedent for "language design that makes the
scheduling-discipline metatheorem cheap to obtain" (directly comparable to, and an
influence on, Choi et al.'s discipline metatheorem), but it is *not* a precedent for
"someone proved a RISC-V core ISA-correct" — that claim about Kôika, which shows up in
secondary summaries, does not survive reading the primary text. No interrupt/exception
story exists because CSRs/traps are simply absent from the modeled ISA subset, same
gap as Choi et al.

---

## 4. Lööw et al. — Lutsig (CPP'21) and Silver (PLDI'19 "Verified Compilation on a
Verified Processor")

**[primary — read from paper PDFs]**. Two papers, one methodology, worth separating:

- **Lutsig** (Lööw, CPP'21) is the *verified Verilog-to-netlist compiler* (behavioral
  Verilog → FPGA-technology-mapped netlist, in HOL4), the piece that lets a property
  proved about behavioral Verilog transport down to gates. It is not itself a processor
  paper; it's the missing compilation link the Silver methodology needs.

- **Silver** (Lööw, Kumar, Tan, Myreen, Norrish, Abrahamsson, Fox, PLDI'19) is the
  processor, and is architecturally the opposite design point from Choi et al. and
  Kôika: **"the implementation is not pipelined, and executes instructions in-order"**
  (their words, §4.1) — single-issue, essentially single-cycle-per-instruction at the
  ISA level. The correctness theorem (paper eq. 7) has the classic ISA-refinement shape
  — `∀k. ∃m. vstep m = Ok fin ∧ (state after m implementation cycles) ~ (Next^k of the
  ISA state)` — a **stuttering, many-implementation-cycles-per-ISA-step simulation**,
  the same relational shape flushing produces but here obtained by *construction*: the
  Verilog itself is generated **by a proof-producing code generator directly from the
  HOL circuit function**, so there is no separate "does this RTL implement this ISA"
  proof obligation to discharge after the fact against hand-written RTL — correctness
  is inherited from the generator's own correctness theorem plus a manually-written HOL
  circuit description. This is the sharpest methodological contrast in this whole
  review: **verify-by-construction (author writes the HOL model, the tool emits
  provably-equivalent Verilog) vs. verify-as-written (someone else's existing RTL is the
  ground truth, as CV32E40P is for us)**. Our program is committed to the latter (per
  our memory: "Fjfj/Kami = new-language approach (we verify SV as-written instead —
  harder semantics, easier adoption)"); Silver is the cleanest example of the former in
  the processor-specific literature.

  **Interrupt story — real but narrow, and worth being precise about, since it is easy
  to over-read the word "interrupt" here.** Silver's ISA *does* include an explicit
  `Interrupt` **instruction** (not an asynchronous external event): executing it
  notifies external hardware (in their FPGA setup, an ARM co-processor over a
  memory-mapped interface) and *waits synchronously* for a response before the next
  instruction proceeds; at the ISA level "Interrupt silently records the current state
  of memory by pushing it onto the trace of I/O events" (§4.1). This is functionally an
  **ECALL/syscall-style, synchronous, software-invoked trap-to-monitor mechanism** for
  talking to a host OS/co-processor (used for CakeML's `stdin`/`stdout`/file syscalls) —
  there is no asynchronous external-interrupt line, no privilege-mode switch, no
  interrupt vector/priority, no precise-exception rollback machinery, and the paper
  never uses the words "exception" or "trap" in the RISC-V-privileged-spec sense.
  Do not cite Silver as prior art for asynchronous-interrupt or precise-exception
  handling — cite Sawada-Hunt (§1) for that instead.

---

## 5. ACL2 industrial line: Centaur and Hunt's FM9001/FM8501 lineage

**[secondary, consistent across multiple independent sources — I was not able to pull
full paper PDFs before the budget ran out; treat bug-count specifics as approximate]**.

**Hunt/Brock, FM9001** (late 1980s–90s, originally Nqthm/DUAL-EVAL, later reverified in
ACL2): a simple non-pipelined 32-bit CPU verified gate-level-netlist-to-ISA and then
*fabricated* — "the only formally verified microprocessor design that has been
manufactured," tested extensively by LSI Logic with no errors found. This is the
oldest and starkest existence proof that kernel-checked hardware proofs survive contact
with silicon; it predates the pipelining problem entirely (FM9001 is not pipelined), so
it is a precedent for "kernel proofs over model checking" as a philosophy but not for
any of our specific pipeline/exception questions.

**Centaur Technology** (Slobodova and the Centaur FV team, ACL2, ~2009 onward, on their
production x86-compatible media/floating-point unit): the origin story itself is the
most useful data point — a subtle floating-point-adder bug was **found by the ACL2
proof effort, not by simulation**, and this single event is credited with triggering
Centaur's ongoing investment in formal (i.e., a real industrial "our kernel proof caught
what our simulation testbench didn't" anecdote, the exact shape of evidence our
untrusted-BMC-as-falsifier-only design bet is trying to earn in reverse — theirs is a
*kernel proof* catching what simulation missed; ours is BMC as an *untrusted* front-end
that never has to catch anything by itself because the kernel proof is still required).
Methodologically this line proves properties **per-instruction / per-opcode**
(SIMD float add/sub, int/float multiply, compares, bitwise ops, int↔float conversions
— "over one hundred instructions" in the media unit), each as its own ACL2 theorem
against a bit-precise IEEE-754 or integer-arithmetic specification, composed with a
symbolic-simulation/BDD-based equivalence backend for the RTL-to-spec gap — i.e. this
is architecturally the closest existing industrial precedent to our own "leaf-module
proofs bottom-up" plan (ALU, mult, alu_div, …) for CV32E40P's execute-stage functional
units, even though it targets x86 rather than RISC-V and doesn't touch pipeline control
or exceptions at all (those are Centaur's separate control-logic FV effort, not covered
in what I could retrieve).

---

## 6. Industrial formal verification **of CV32E40P itself** — the direct replication
target

**[primary for the concrete bug report (GitHub issue #509) and the DVCon slide deck;
secondary/blog-sourced for the OneSpin narrative and aggregate bug counts]**.

**OneSpin/Siemens EDA campaign (2020–21, OpenHW Verification Task Group).** Tool: the
"RISC-V ISA Processor Verification" app on top of Siemens' Questa/OneSpin 360 formal
engine. Property-generation style is notable and directly answers "what spec style did
they use": rather than hand-writing SVA, they fed the app a **Sail-language pseudocode
description of the ISA** (including XPULP's ~300 custom instructions) and the app
**auto-generated the formal properties** — one production report cites "more than 430
assertions and 29 CSR descriptions," applied across seven hardware configurations
(parameter corners). This is architecture-level, one-instruction-at-a-time property
generation (the same granularity RVFI checks target, see §7), not a whole-core
refinement proof, and not the compositional style of §8 below.

**Aggregate bug attribution** [secondary, single source — treat the raw numbers as
approximate]: across the full CV32E40P verification campaign, one report gives **30
issues found by formal, 20 by simulation, 4 by lint/RTL review** (all resolved except
one lint warning) before "Functional RTL Freeze" in early 2021. A separately-reported
snapshot of the *later* v2.0.0 (XPULP/F/Zfinx) formal pass gives **18 RTL bugs + 12
user-manual clarifications**, with the RTL bugs characterized as "illegal-instruction
exceptions, multi-cycle floating-point instruction hazards, IEEE-754 compliance
issues." Earlier reporting on the original IMC-only core specifically calls out
**8 bugs "related to regular and exception instructions"** plus additional
privileged-spec bugs, explicitly noting these were corner cases "triggered under rare
conditions in the instruction sequence, memory stalls, and CSR programming" — i.e.
precisely the class of bug that lives at the intersection of pipeline control and
exception/interrupt logic, not in a single functional unit.

**A concrete, primary-source bug — issue #509, "Core executes wrong instruction"**
[primary, read from the GitHub issue]. Found by OneSpin 360 while proving a
program-counter-update property. The scenario: a load (`lw`) stalls on a data-memory
wait state; an interrupt request arrives and is then **retracted** before it is
serviced, leaving `instr_valid_irq_flush_q` set (recording "there is still a
flushed-but-pending instruction to (re-)execute"); a **debug-mode** entry request then
arrives; the core enters debug mode while that stale flag is still set, and on the way
out incorrectly executes an instruction (a `sw`) that should have been discarded by the
flush. This is a three-way interaction — memory-stall + interrupt-retraction +
debug-mode-entry — none of which is even *representable* in Choi et al.'s or Kôika's
RV32I-without-interrupts models, and it is exactly the shape of bug the Sawada-Hunt
MAETT discipline (an explicit per-in-flight-instruction "is this still valid to commit"
ghost bit, checked at every stage transition) is built to catch, and that a PC-only
observable (§2) would likely never expose (the PC trace can look fine while the wrong
*data* gets written). **This is a strong argument that our controller-module contract
needs an explicit "instruction validity" / "about-to-be-flushed" ghost bit threaded
through debug-entry and interrupt-retraction paths specifically**, not just a clean
happy-path retirement predicate.

**core-v-verif's "Step-and-Compare 2.0"** [secondary]: the *simulation*-side sibling
effort — RTL run in lockstep against the Imperas ISS reference model via the **RVVI**
(RISC-V Verification Interface, a standardization of the tracer boundary between DUT
and reference model, explicitly built to be RVFI-compatible/adaptable) at every
retirement, comparing register/PC/CSR state cycle-by-cycle. This is *not* formal — it's
industrial-strength differential simulation — but it is useful to us as the concrete
shape of "what does the reference-model comparison ghost interface look like when an
industrial team builds one for exactly this core," and it independently converges on
the same per-retirement-tuple discipline RVFI formalizes (§7).

---

## 7. riscv-formal / RVFI — the practical bounded-harness interface

**[primary — read from `docs/rvfi.md` on the `cliffordwolf/riscv-formal` repo, cross-
checked against the OpenHW CV32E40S user-manual's RVFI page]**.

**Design.** A core wishing to be checked implements an optional `rvfi_*` port bundle
(bound in via SV `bind`, so it costs nothing when unused) that, once per cycle per
retirement channel (`NRET` wide, `XLEN` bits/reg), exposes: `rvfi_valid` (this channel
retired an instruction this cycle), `rvfi_order` (a **strictly monotonic, gap-free**
64-bit instruction index — this is the field that operationalizes "exactly-once
retirement": any core that ever skips a number or repeats one is, by construction, not
RVFI-conformant, no separate exactly-once theorem needed), `rvfi_insn`,
`rvfi_pc_rdata`/`rvfi_pc_wdata`, `rvfi_rs1/2_{addr,rdata}` (pre-state, sampled *before*
the instruction executes), `rvfi_rd_{addr,wdata}` (post-state), `rvfi_mem_{addr,rmask,
wmask,rdata,wdata}` (byte-masked, so partial/narrow accesses are exact, not just
word-aligned), and — the trap/interrupt fields directly relevant to us —
`rvfi_trap` (this instruction itself faulted: illegal opcode, misaligned access, memory
violation) and `rvfi_intr` (this is the *first* instruction of a trap handler, i.e. a PC
discontinuity happened getting here, whether from an exception or an asynchronous
interrupt) plus `rvfi_mode`/`rvfi_ixl` for privilege level and XLEN. The riscv-formal
*checks* (`insn_*.sv` per-opcode files, driven by a k-induction/BMC backend —
SymbiYosys/`yosys-smtbmc`) then compare each retired instruction's RVFI tuple against a
golden per-instruction ISA function, essentially instruction-at-a-time — this is by
design a **bounded** methodology (BMC/k-induction to some depth, not an unbounded
kernel proof), matching our "untrusted BMC as falsifier" bucket rather than our kernel
tier, but the *interface design* (the ghost-state discipline itself) is reusable
independent of what backend consumes it.

**Answering the brief's key question 1 directly: is per-instruction retirement tracing
(`rvfi_order`, monotonic/gap-free) the right ghost-state discipline for our
"exactly-once controller contract"?** Yes, with one caveat worth internalizing rather
than copying blindly. The monotonic-gapless-order-tag idea is exactly right as a
*specification device* — for a `Design`-as-Lean-function controller module, the
analogous ghost field is "the retirement channel emits a strictly increasing sequence
tag, one value per committed instruction, with no value skipped and no value repeated,"
and it composes cleanly with our `Sv.onPosedgeIdx`/trace-combinator style (§ our own
`docs/sv-spec-surface.md`, example 16's `pipe2_sva`-style per-datum tracking is already
structurally the same idea). The caveat: RVFI's tuple is deliberately **whole-core** and
**post-hoc black-box** (see next paragraph) — its per-instruction observable (rd_wdata,
mem access, trap) is *exactly what an external verifier needs to check ISA conformance*,
but it says nothing about how a decompositional proof gets *there* from a controller
module's internal state. For our leaf/stage-contract program we want the *idea*
(monotonic tag + full instruction-effect tuple as the ghost/ports-only observable) but
stated as an ordinary `Sv.onPosedgeIdx` port-level spec on the specific module being
proved, not literally RVFI's fixed wire bundle — which brings us to:

**Answering key question 2 — RVFI itself is not a compositional discipline.** I looked
specifically for guidance on checking a controller-like sub-module (vs. whole-core)
using RVFI and found none in the primary docs; the interface is explicitly "the
processor itself must implement an RVFI module" — a whole-core, black-box wrapper. The
core-v-verif docs for CV32E40P likewise only describe RVFI/RVVI as the whole-core
tracer boundary for both formal and Step-and-Compare simulation. **The one concrete
precedent I found for compositional, sub-module-level, RVFI-flavored reasoning is
Chen et al. (NCKU), DVCon, "Automate and Accelerate RISC-V Verification by
Compositional Formal Methods"** [primary — read from the DVCon PDF, downloaded and
`pdftotext`'d]: they extend RVFI with extra internal tap signals
(`rvfi_de_insn`, a pipelined shift-register of the retiring instruction word through
decode/execute/writeback, mirroring exactly our `Sv.onPosedgeIdx`-with-local-variable
pattern from spec-surface example 16) and then explicitly split a single whole-datapath
SVA property ("the ADD instruction's result is correctly forwarded *and* correctly
written back") into two properties over two sub-components — **M** = "write-back
datapath writes the right value to the right register" and **N** = "forwarding mux
selects the right forwarded value" — connected by textbook **assume-guarantee
composition**: `M ∥ A ⊨ P`, `N ⊨ A` ⟹ `M ∥ N ⊨ P`, where `A` is exactly the assumption
"forwarding is correct" that lets `M`'s proof stay ignorant of `N`'s internals. Applied
to a small in-order core (Vscale, 3-stage) and a 6-stage core (RV12), this **halved to
two-thirds-reduced** the number of formally-inconclusive (state-explosion-timeout)
properties per instruction class, and independently found three real RTL bugs (`sra`/
`srai` using logical instead of arithmetic right-shift; `jalr`'s target-address LSB
clearing done in the wrong order per-spec; `csrrwi`'s `rs1=x0`-exemption rule applied to
the wrong CSR-instruction subset). **This is the concrete answer to "how did anyone spec
a controller-like module compositionally vs. whole-core": extend the RVFI ghost-tap
discipline into the pipeline interior, and use assume-guarantee, not a heavier interface
language, to split the property at the module boundary** — methodologically identical in
shape to our own rely-guarantee/DVRTL-adjacent design, just instantiated with SVA+formal
tooling instead of a kernel proof. It is bug-finding evidence (bounded model checking,
not a kernel proof) but the *decomposition strategy* is directly reusable as a template
for how our `sv_vcgen` module contracts should carve up e.g. CV32E40P's decode/forwarding
logic.

**Other RVFI design notes worth carrying forward**: the `RISCV_FORMAL_ALTOPS` escape
hatch (replace mul/div by cheap operations that are semantically-tagged-equivalent for
BMC tractability) is an SMT-solver-scalability trick with no kernel-proof analog we'd
want — a reminder that RVFI's tractability tricks are backend-specific and shouldn't be
mistaken for spec-discipline; and the explicit causality constraint for out-of-order
retirement ("register/memory writes must retire before the reads that depend on them")
is a clean, reusable *shape* for a same-cycle-interference side condition, structurally
close to our own commutativity-VC discipline (SV_VCGEN class (1) in our design notes).

---

## 8. Direct answers to the brief's three key questions

1. **Is RVFI-style monotonic per-instruction retirement tracing the right ghost-state
   discipline for our exactly-once controller contract?** Yes as a *specification
   pattern* (monotonic gap-free tag + full per-commit effect tuple, expressed as an
   ordinary port-level `Sv.onPosedgeIdx` predicate in our surface, not a literal fixed
   wire bundle); no as a *ready-made compositional discipline* — RVFI itself is
   whole-core/black-box, and the one place anyone made it compositional (§7, NCKU/DVCon)
   had to hand-extend it with internal taps and bolt on assume-guarantee themselves.
   Sawada-Hunt's MAETT (§1) is the deeper ancestor for the "is-this-instruction-still-
   valid-to-commit" ghost bit specifically, which issue #509 (§6) shows is exactly the
   bit that CV32E40P's real bugs live on (retracted-interrupt + debug-mode interaction).

2. **How did anyone spec a controller-like module compositionally vs. whole-core?**
   The only genuine precedent found is Chen et al.'s extended-RVFI + assume-guarantee
   split (§7) — property-level compositionality (`M ∥ A ⊨ P`, `N ⊨ A` ⟹ `M ∥ N ⊨ P`)
   over an RVFI-style tapped trace, not module-type-level compositionality in the
   Kami/Koika sense (rule/method interfaces) and not a kernel-proof discipline. Every
   from-first-principles *kernel-proof* precedent we found (Choi et al., Kôika, Silver)
   proves a single monolithic core-level refinement theorem and does not decompose the
   proof by pipeline stage at all — our own `sv_vcgen` rely-guarantee module-contract
   plan (register-boundary composition, per our design notes) currently has no direct
   kernel-proof precedent in the RISC-V-pipeline literature; it is closest in *spirit*
   to Sawada-Hunt's per-stage invariant fields inside one MAETT structure, and in
   *mechanism* to Chen et al.'s assume-guarantee split, but neither is quite our shape.
   This is a genuine gap, not just an oversight on our part — worth stating plainly
   rather than papering over.

3. **Published bug lists for CV32E40P — replication targets.** Concrete, citable:
   issue #509 (retracted-interrupt + debug-mode flush corner case, §6); the `sra`/
   `srai`/`jalr`/`csrrwi` bugs found on *other* RISC-V cores (Vscale, RV12) by the same
   extended-RVFI method (§7) are not CV32E40P bugs but are excellent
   cheap-to-reproduce **calibration targets** for "would our proof style catch this
   class of bug" before attempting CV32E40P itself. The aggregate "8 bugs in regular
   and exception instructions" / "18 RTL bugs at v2.0.0" / "30 formal-found issues"
   numbers (§6) are real but I could only source them at the level of vendor blog posts
   and the user manual's prose summary — I did not find a itemized public bug list with
   per-bug RTL diffs beyond #509 itself; if a more complete list matters for
   replication-target planning, the next step is trawling closed GitHub issues on
   `openhwgroup/cv32e40p` for the "bug" + "formal"/"OneSpin"/"riscv-formal" label
   combination rather than relying on vendor marketing copy.

---

## 9. Verdicts, in the common-brief format

| Method | Kernel proof or bounded/model-checked? | Handles precise exceptions/interrupts? | Compositional? | Verdict for us |
|---|---|---|---|---|
| Burch-Dill flushing | Automatic, EUF/term-level decision procedure (not a from-scratch kernel proof, though mechanizable) | No — single-instruction abstraction has no notion of *where* an interrupt lands | No | Historically important, not directly reusable; our `Sv.transaction`/refinement judgment already supersedes its expressiveness |
| Velev-Bryant | Model-checking-adjacent (UCLID-style term-level MC) | Encoded as another EUF term, absorbed into the same commutation diagram | No | Same bucket as Burch-Dill; falls on our "untrusted falsifier" side if reused at all |
| Sawada-Hunt / MAETT | Kernel proof (ACL2), hand-found invariant | **Yes — the direct precedent**, precise exceptions by construction via per-instruction commit ghost state | No (whole-machine invariant, not module-decomposed) | Adopt the *ghost-state shape* (per-in-flight-instruction validity/commit bit) for our controller contract; do not adopt ACL2's proof-automation style |
| Choi/Kim/Kang OOPSLA'25 RISC-V case study | Kernel proof (Rocq) | **No** — CSR/priv/traps are `fail_hard`→UB, explicitly out of scope | No (one monolithic core-level theorem) | Confirms the discipline-metatheorem shape we already adopted works end-to-end; explicitly does *not* extend to the interrupt/exception tier we need |
| Kôika RV32I core | N/A — no ISA-correctness theorem exists for it | No (RV32I without interrupts, unverified besides) | N/A | Not a correctness precedent at all, despite reading that way in secondary summaries; the *language*-level ORAAT metatheorem is a discipline-metatheorem cousin worth remembering |
| Silver / Lutsig | Kernel proof (HOL4), but verify-*by-construction* | Narrow — synchronous software `Interrupt` instruction (ECALL-like), no async interrupts/precise exceptions | N/A (single monolithic ISA-refinement theorem; not pipelined so the question is moot) | Confirms our verify-as-written commitment is the harder road relative to this alternative; not reusable for exception handling |
| ACL2/Centaur, per-instruction functional-unit proofs | Kernel proof (ACL2) + symbolic-simulation backend for RTL gap | N/A (functional units only, not control/exception logic) | Yes, in the loose sense of one theorem per opcode | Closest existing industrial precedent to our own leaf-module (ALU/mult/alu_div) proof plan |
| OneSpin/Siemens CV32E40P campaign | Bounded (formal property checking / BMC-class engine), Sail-autogenerated assertions | Yes, and this is where most of their real bugs live (§6) | No (property-per-instruction, whole-core context) | Direct replication target; property style (ISA-pseudocode → autogenerated assertion) is a reasonable model for what our extractor's `sv_vcgen` residual VCs should resemble at the leaf level |
| riscv-formal / RVFI | Bounded (SymbiYosys BMC/k-induction) | Yes — `rvfi_trap`/`rvfi_intr` are first-class, and the ghost-order-tag *is* the exactly-once discipline | No out of the box; yes when hand-extended (Chen et al.) | Adopt the ghost-tap/order-tag *pattern* into our port-level spec surface; do not adopt the bounded-BMC backend as anything beyond an optional untrusted falsifier |
| Chen et al. compositional extended-RVFI (DVCon) | Bounded (JasperGold), assume-guarantee on top | Not the focus (RV32I base ISA only in their case study) | **Yes — the one real precedent for controller-sub-module compositional specs** | Best available template for how to carve `sv_vcgen` module contracts at pipeline-stage boundaries |
