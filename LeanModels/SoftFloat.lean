/-
SoftFloat — the family's shared IEEE 754 component (`docs/family-architecture.md`
§3.5, `docs/softfloat-charter.md`).

TWO FILES, AND THE SPLIT IS THE POINT: `Basic` is the spec algebra and mentions
no interpreter; `Theorems` is the thin layer that connects it to core's
operations.

DEPENDENCY POSTURE (§3.2 item 4): this component depends on NO package.  It
imports `Init.Data.Float.Model` and nothing else.  Mathlib is a repository
dependency, not this component's.

IT DOES NOT LIVE IN `LeanModels/Core/` YET, and that is the family's own rule
rather than a preference: §3.8 fixes the trigger for a move into `Core` at the
SECOND CONSUMER, and SoftFloat has zero in-tree consumers today (ES is blocked,
SV is dormant).  The move is a named trigger in `docs/backlog/softfloat.md`.
-/
import LeanModels.SoftFloat.Basic
import LeanModels.SoftFloat.Theorems
