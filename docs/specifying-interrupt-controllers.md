# Can you completely specify an interrupt controller?

*A note for hardware engineers skeptical of formal specification — written around a
real objection: "there is no way to specify the behavior of an interrupt controller
completely, because it sits between other modules; to model its I/O you'd need a
behavioral model of the entire CPU."*

The objection deserves respect before rebuttal: a naive formalization fails **exactly**
this way. Spec the controller's FSM in isolation, invent assumptions about its
neighbors, and you get a theorem that is either false or — worse — vacuously true.
This project has caught precisely that failure twice in its own work, by adversarial
audit, and now enforces structural rules against it (every safety theorem ships with a
realizability witness; behavior relations may contain only physics/semantics, never
desired conclusions). The instinct behind the objection is the instinct of someone who
would catch bad formal work. The answer is not "formal methods can do everything" —
it is that *"you need a model of the entire CPU"* conflates **three different layers**,
and each layer has a closed, complete specification at its own level.

## Layer 1: the module itself needs nothing

Read the RTL before theorizing. CV32E40P's `cv32e40p_int_controller.sv` is:
a registered mask, a priority cascade, and an enable gate —

```
irq_q          <= irq_i & IRQ_MASK            (one flop stage)
mip_o           = irq_q
irq_req_ctrl_o  = |(irq_q & mie_bypass_i) && global_irq_enable
irq_id_ctrl_o   = highest-priority set bit (fixed, documented cascade)
```

Its complete file-local specification is a handful of adjacent-cycle equations over
its **ports** — no pipeline, no CPU, no environment model anywhere. It is total: for
every input trace, the outputs are fully determined. Most "unspecifiable" modules
dissolve like this on contact with their source. (The drafted Lean statements live in
`docs/cv32e40p-spec-surface.md`; the spec never mentions an internal register or FSM
state — ports only, which is a house law.)

## Layer 2: "when is it *taken*" needs a contract, not a CPU model

The genuinely entangled question — *when does the pending interrupt actually get
taken* — is not the interrupt controller's property; it belongs to the boundary
between the controller module, the main controller FSM, and the pipeline. The
conceptual key is the theory of **open-system specification** (Abadi–Lamport): a
component's spec has the form **rely ⟹ guarantee**. You do not *model* the pipeline;
you *quantify over every environment behavior* satisfying named assumptions:

> **Rely** (assumptions on neighbors, stated as port disciplines): handshakes are
> well-formed; the pipeline does not stall forever without an architectural cause;
> masking updates follow the CSR write protocol.
>
> **Guarantee**: `pending ∧ enabled ∧ ¬masked  ⟹  taken within k cycles`, taken at
> an instruction boundary, at the highest pending priority, with the correct
> `mstatus`/`mepc`/`mcause` update — where `k` is a function of the pipeline's
> longest uninterruptible window (multicycle instructions + outstanding memory
> transactions).

Three things make this rigorous rather than hand-wavy:

1. **The rely clauses are not trusted — they are discharged.** Each assumption is
   later proved as a *guarantee of the neighboring module's own contract*. The
   apparent circularity ("the controller assumes things about the pipeline, which
   assumes things about the controller") has a soundness theorem: McMillan's circular
   assume-guarantee rule, mechanized by Rushby, whose induction-over-time argument is
   made sound by exactly the thing hardware gives us for free — a **register boundary**
   between the modules supplies the t → t+1 offset the rule requires.
2. **Environment nondeterminism is quantified, not modeled.** Arbitrary interrupt
   arrival timing, arbitrary software masking behavior: the theorem holds *for all* of
   them. "The environment can do anything" is an argument **for** universal
   quantification, not against specification. (Where fairness is genuinely needed —
   e.g. a bus that must eventually respond — it is bundled into an explicit oracle
   parameter's legality, so every "eventually" becomes "within a bound, under stated,
   named assumptions.")
3. **The deadline `k` is the content, not a nuisance.** Computing it forces the spec
   to name every source of interrupt latency. A spec that says "eventually taken" is
   satisfied by a CPU that takes the interrupt after 10^100 cycles; the bounded form
   is what an interrupt controller is *for*. Ghost/auxiliary state (an instruction
   ledger tracking in-flight instructions, minted purely from port handshakes) makes
   "taken at an instruction boundary, exactly once" precise — a technique with a
   30-year pedigree (history variables; Sawada–Hunt's MAETT).

## Layer 3: "completely" lives at the ISA level — and that model is small

Complete behavioral specification is delivered by **refinement**: the core (including
its interrupt machinery) implements the ISA's architectural step function, which
includes trap dispatch. The crucial size fact: RISC-V's own machine-readable formal
specification — `sail-riscv`, adopted by RISC-V International — expresses interrupt
dispatch (`getPendingSet` / `dispatchInterrupt` / `trap_handler`, the `mstatus`
stack discipline, priority order) in a couple hundred readable lines. The behavioral
model the objection says you'd need **is the spec-sized object, not the
implementation-sized one** — that is the entire point of refinement.

## Reading list (ordered for a skeptic)

1. **OpenHW / OneSpin formal verification of CV32E40P** (core-v-verif formal program;
   DVCon 2021 reports). Commercial formal verification of *this exact core*,
   interrupts included, which found real RTL bugs. Not an argument — a receipt.
2. **Sawada & Hunt**, *Processor verification with precise exceptions and speculative
   execution* (CAV 1998; J. Automated Reasoning 2002). A pipelined machine **with
   interrupts and precise exceptions**, mechanically verified end to end. The direct
   existence proof against "this can't be specified."
3. **Choi, Kim & Kang**, *Revamping Verilog Semantics for Foundational Verification*
   (OOPSLA 2025). A pipelined RISC-V proved in a modern proof assistant, modularly —
   the 2020s form of the same result, mechanized in Rocq.
4. **Abadi & Lamport**, *Composing Specifications* (TOPLAS 1993). The canonical
   theory of specifying a component *without* modeling its environment — the paper
   that answers the objection at its conceptual root.
5. **McMillan** (CHARME 1999) + **Rushby**'s PVS mechanization (SRI CSL, 2001). Why
   mutually dependent module contracts are sound; why the register boundary is what
   makes the circularity legal.
6. **`sail-riscv`** (Armstrong et al., POPL 2019; github.com/riscv/sail-riscv). Read
   `dispatchInterrupt` and `trap_handler`: the "complete behavior" the objection says
   cannot be written — written, readable, and adopted as the standard.
7. **riscv-formal / RVFI** (C. Wolf). The practical per-instruction interface
   commercial flows use to check exactly these properties on cores of this class.

## The falsifiable close

Don't argue in the abstract. This repo contains drafted specifications of CV32E40P's
interrupt path at all three layers (`docs/cv32e40p-spec-surface.md`, entries 8–10:
the module conformance equations, the contract-level boundary/priority/bounded-response
properties with their rely clauses named, the ISA-level trap semantics). The
productive question to put to any skeptic is:

> **"Which behavior of the real controller do these statements fail to capture?"**

Either no example can be named — or one is named, and it becomes a better
specification the same afternoon. Both outcomes are wins; that asymmetry is the whole
reason to write specs down formally in the first place.
