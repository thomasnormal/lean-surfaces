import LeanModels.Sv.ContractFA
import LeanModels.Sv.ObserveRedrive
import LeanModels.Sv.REdgeRun2
import LeanModels.Sv.FlatMemRun2

/-!
# The observation lane's library root (WS2)

No module under `LeanModels` imports the observation interface or its `run2` libraries: their only
importers are `svgolf/design` drafts. So neither `lake build LeanModels` nor a landing's scoped build
reached them, and they were built only by hand from `compile-obs.sh`'s prerequisite comment.

This module imports the leaves. That builds, transitively, `Observe`, `ObserveFrame`,
`ObserveRedrive`, `CycleMachine`, `REdgeRun2`, `FlatMemRun2`, `Contract` and `ContractFA`. It is in
`tools/check_sv_chain.sh`'s library group. It declares nothing.
-/
