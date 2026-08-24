/-
SoftFloat — the family's shared IEEE 754 component (`docs/family-architecture.md`
§3.5, `docs/softfloat-charter.md`).

FIVE FILES, AND THE SPLIT IS THE POINT: `Basic` is the spec algebra and
`Round` the declarative rounding spec — neither mentions an interpreter;
`RoundAlg` is the computable rounding, kept in its own file precisely so the
anti-circularity argument stays visible; `Theorems` is the thin layer that connects it to
core's operations; `Transfer` carries those facts across core's packed
boundary to `Float.Model`/`Float32.Model` — from ONE statement per fact,
because the two wrappers are instances of a class rather than duplicates.

DEPENDENCY POSTURE (§3.2 item 4): this component depends on NO package.  It
imports `Init.Data.Float.Model` and nothing else.  Mathlib is a repository
dependency, not this component's.

IT DOES NOT LIVE IN `LeanModels/Core/` YET, and that is the family's own rule
rather than a preference: §3.8 fixes the trigger for a move into `Core` at the
SECOND CONSUMER, and SoftFloat has zero in-tree consumers today (ES is blocked,
SV is dormant).  The move is a named trigger in `docs/backlog/softfloat.md`.
-/
import LeanModels.SoftFloat.Basic
import LeanModels.SoftFloat.Round
import LeanModels.SoftFloat.RoundAlg
import LeanModels.SoftFloat.Theorems
import LeanModels.SoftFloat.Transfer
