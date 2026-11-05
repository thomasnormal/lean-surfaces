import LeanModels.Core.Basic
import LeanModels.Cpp.Tests
-- The family's shared semantic monad (docs/family-architecture.md §3.4, §3.8).
-- Landed in Core so that no tier writes its own copy — §3.8's rule is that a
-- second interpreter arriving with its own stack is a defect, not a design.
-- Additive: nine new names, all measured to collide with nothing in the tree.
import LeanModels.Core.Outcome
import LeanModels.Python
-- The SystemVerilog lane. The specs under `Examples/system-verilog/` already pull the
-- core Sv chain in transitively; these imports make the whole lane (including
-- the interpreter's #guard test suite, the self-check tier, and the toggle
-- walkthrough) an explicit part of `lake build` — and therefore of CI.
import LeanModels.Sv.Tests
import LeanModels.Sv.SelfCheck
import LeanModels.Sv.ToggleExample
-- The parametric (sv-0.2) layer: symbolic design families + their ingestion
-- (`load_design_sv2`) — the CV32E40P phase-2 pipeline.
import LeanModels.Sv.Param
import LeanModels.Sv.Ingest2
-- The Design2 proof layer over the sv-0.2 semantics: the fuel-free evaluator
-- (Pure2), the spec judgment `⊨₂` (Spec2), the known-value BitVec calculus and
-- `sv2_known` (Known2), the generate-loop expansion lemmas (Gen2), the
-- combinational settle theorem (Comb2Base/Sound/Term/Comb2), fuel monotonicity
-- (Mono2), and the worked full adder (Comb2Example). Concatenation targets
-- (Comb2ConcatExample) and `always_comb` bodies (Comb2Proc, Comb2ProcExample)
-- are in the settle profile; module instances flatten through Hier2/Hier2Gen.
-- Acceptance examples: `Examples/system-verilog/ripple_add` (the N-bit
-- generate-loop ripple adder), `mul2d`, `partsel` and `ripple_fa`.
import LeanModels.Sv.Pure2
import LeanModels.Sv.Spec2
import LeanModels.Sv.Known2
import LeanModels.Sv.Gen2
import LeanModels.Sv.Comb2Base
import LeanModels.Sv.Comb2Sound
import LeanModels.Sv.Comb2Term
import LeanModels.Sv.Comb2
import LeanModels.Sv.Comb2Example
import LeanModels.Sv.Comb2ConcatExample
import LeanModels.Sv.Comb2Proc
import LeanModels.Sv.Comb2ProcExample
import LeanModels.Sv.Hier2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Mono2
-- The loop rows (WS3): `always_comb` statement fuel counted in `Design2.combFuel` and sufficient
-- (Comb2Fuel), and procedural `for` loops as trip schemas, row recurrences and `sem N`, with loop
-- bodies read by recursion (Loop2, Loop2Rows, Loop2Sem, Loop2Frag). Acceptance examples:
-- `Examples/system-verilog/loop_edges` and `loop_nested_clmul`.
import LeanModels.Sv.Comb2Fuel
import LeanModels.Sv.Loop2Frag
-- The word-level proof library (`LeanModels/Sv/Lib.lean`): `Nat` and `XF.val` lemmas that carry
-- `sv_equations`' printed netlists into `Nat` arithmetic (restoring division, row-major offsets).
import LeanModels.Sv.Lib
-- R1 inches 2-3: the IEEE 1800 §4.4 event-region TYPES, the region-aware
-- oracle (introduced additively, with the conservativity of the widening
-- proved), the slot-structured trace, and the `cycleOf` abstraction every
-- observation is stated through. No semantics — see docs/sv-r1-scheduler.md.
import LeanModels.Sv.Regions
-- F1: retained concurrent-assertion properties over E's clocked samples. The
-- property envelope is separate from the frozen procedural `Stmt2` AST.
import LeanModels.Sv.Sva
import LeanModels.Sv.SvaContract
-- R1 inch 4a: the resumable stepper. `stepSStmts` runs a process body to
-- completion OR to its first suspension point, with the continuation kept as
-- DATA (the residual statement list) because `SemM` cannot suspend. Carries
-- the proof that `execSStmts` is RECOVERED as its non-suspending case, so the
-- walker is subsumed rather than replaced by a second interpreter.
import LeanModels.Sv.Step
-- R1 inch 4a-0: the SV tier on the family substrate — W/rho/pi/sigma, the
-- SvM abbrev, and the two `rfl` adoption facts (Res.le IS Core's FlatLe at
-- timeout, adopted by iff so the monotonicity ladder transfers untouched).
import LeanModels.Sv.World
-- R1 inch 4a: the SvM primitive layer -- the operations slotStep is built
-- from, with their laws as #guards. This is what 9.0's `semantics on SvM`
-- counts.
import LeanModels.Sv.Prim
-- R1 inch 4a: slotStep -- one IEEE 1800 4.4 time slot as the Active /
-- Inactive / NBA loop over the SvM primitives, ITERATING rather than falling
-- through, because work an NBA commit schedules re-enters Active.
import LeanModels.Sv.Slot
-- R1 inch 4a: runSlots -- the trace-producing driver. slotStep runs ONE slot
-- and mutates the world; this drives a stimulus through it and collects a
-- RegionTrace, which is the left-hand side the adequacy lemma needs.
import LeanModels.Sv.Drive
-- R1 inch 4a: wakeEdges (the half stepRegion was missing -- regionQ was only
-- ever drained) and elabDesign (Design -> SvWorld, the adequacy lemma's third
-- obligation). always_comb/assign stay LOUD: comb sensitivity has no Trigger.
import LeanModels.Sv.Load
-- R1 inch 4b: the adequacy lemma STATED -- clockExpand (the M0 clock is
-- implicit, so one cycle is TWO region slots) and posedgeSlots, plus the
-- guard that both models agree on a real design through them.
import LeanModels.Sv.Adequacy
-- The exact semantics E (docs/sv-kernel.md): E-core-0 (assigns, `always_comb`) and E-core-1
-- (`always_ff`, NBA, the clocking discipline) under the `Kernel` root; the observation interface,
-- cycle machine and module contracts over `run2` under the `ObsLib` root; the XOR-sum calculus
-- (XorSum) and the 4-state operator monotonicity theorems (XMono).
import LeanModels.Sv.Kernel
import LeanModels.Sv.ObsLib
import LeanModels.Sv.XorSum
import LeanModels.Sv.XMono
-- The E route for loop and ordinary `always_comb` bodies: the loop seam and single-process slots over
-- E-core-0 (Loop2E, Loop2Slot) and the comb fragment with its slots (CombFragE, CombSlotE).
import LeanModels.Sv.CombSlotE
-- `sv_exhaustive`: a flat comb netlist compiled once into a gate program over one packed `Nat`, with its
-- soundness (CombExhaustive, CombExhaustiveSound) and the tactic (CombExhaustiveTactic). Its goal shape is
-- svGolf's task statement, which is not on master, so no example here runs it.
import LeanModels.Sv.CombExhaustiveTactic
-- The RISC-V lane: the RV32IMC + machine-mode ISA model (single source of
-- truth for the CV32E40P projections; Step pulls Priv, Csr, Exec, Decode and
-- Ast transitively).
import LeanModels.Rv.Step
import LeanModels.Isa.RiscV.Oracle
-- R1: the core-independent commit observation and trace-refinement theorem.
import LeanModels.Refine
-- SoftFloat: the family's shared IEEE 754 component (docs/family-architecture.md
-- §3.5, docs/softfloat-charter.md). Layer 2 — the spec algebra over a general
-- `Float.Model.Format`. Depends on NO package: core's float model and nothing
-- else. Not in `LeanModels/Core/` yet, and that is §3.8's second-consumer
-- trigger rather than a preference — see docs/backlog/softfloat.md.
import LeanModels.SoftFloat
