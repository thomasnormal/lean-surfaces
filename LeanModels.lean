import LeanModels.Core.Basic
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
-- R1 inches 2-3: the IEEE 1800 §4.4 event-region TYPES, the region-aware
-- oracle (introduced additively, with the conservativity of the widening
-- proved), the slot-structured trace, and the `cycleOf` abstraction every
-- observation is stated through. No semantics — see docs/sv-r1-scheduler.md.
import LeanModels.Sv.Regions
-- The RISC-V lane: the RV32IMC + machine-mode ISA model (single source of
-- truth for the CV32E40P projections; Step pulls Priv, Csr, Exec, Decode and
-- Ast transitively).
import LeanModels.Rv.Step
-- SoftFloat: the family's shared IEEE 754 component (docs/family-architecture.md
-- §3.5, docs/softfloat-charter.md). Layer 2 — the spec algebra over a general
-- `Float.Model.Format`. Depends on NO package: core's float model and nothing
-- else. Not in `LeanModels/Core/` yet, and that is §3.8's second-consumer
-- trigger rather than a preference — see docs/backlog/softfloat.md.
import LeanModels.SoftFloat
