/-
sunfish pin shard: the MIDGAME board `posMid` at DEPTH 3.

Sub-shard of `pins_bound_mid` (2026-08-25). The profile measured `_mid` at
875 s — 74% of the whole bound family — so the board was split by DEPTH,
which is the axis the cost actually follows: node counts rise steeply with
depth and they are printed in the certificates themselves. A red here names
the board AND the depth. Every `#guard` moved VERBATIM; `posMid` moved to
`pins_common.lean` unchanged.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_bound_mid_d3

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

-- midgame, depth 3 (653 nodes across the pair)
#guard boundProbe posMid 0 3 == some (2, 413)
#guard boundProbe posMid 60 3 == some (59, 240)

end Examples.python.sunfish.pins_bound_mid_d3
