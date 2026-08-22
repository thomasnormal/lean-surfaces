import LeanModels.C.Ast
import LeanModels.C.Value
import LeanModels.C.Json
import LeanModels.C.Load

/-!
# The C lane (`LeanModels.C`)

C as the project's third modeled language, after Python and SystemVerilog.
The charter is `docs/c-tier-charter.md`; the architecture it continues is
`docs/c-tier-architecture.md`.

**M1 (ingestion) is complete; M2 has begun.** The lane contains the
deep-embedded AST of the `c-0.1` envelope
(`docs/c-envelope-schema.md`), the ingester that builds it, and — as M2's
first inch — the VALUE model (`Value.lean`): fixed-width integers and the
arithmetic that makes unsigned wrap and signed refuse.

There is still no interpreter, no memory model and no world. The plan for
those is `docs/c-semantics-design.md`; the goal they are scored against
is `docs/c23-goal.md` (Thomas ruled option (c) — the C23 completeness
ladder, measured against real test suites).

Importing this from `LeanModels.lean` is what puts the lane in
`lake build`, and therefore in CI.
-/
