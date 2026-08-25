/-
sunfish pin shard: the OPENING board (`posH 0`), depths 1-3.

SHARD of the `pins_bound` battery (2026-08-25 topology change): the
capstone prose, and the map of which board lives in which shard, are in
`pins_bound.lean`. Nothing here is new — every `#guard` moved VERBATIM
from that file, and the shard boundary is by POSITION so a red names its
board. `boundProbe` moved to `pins_common.lean` unchanged.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_bound_h

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

-- the opening board, depths 1-3 across failing-low and failing-high windows
#guard boundProbe (posH 0) 0 1 == some (0, 2)
#guard boundProbe (posH 0) 40 1 == some (37, 34)
#guard boundProbe (posH 0) (-100) 1 == some (0, 2)
#guard boundProbe (posH 0) 0 2 == some (0, 2)
#guard boundProbe (posH 0) 40 2 == some (36, 138)
#guard boundProbe (posH 0) 0 3 == some (0, 34)
#guard boundProbe (posH 0) 40 3 == some (39, 197)
#guard boundProbe (posH 0) (-100) 3 == some ((-46), 2)

end Examples.python.sunfish.pins_bound_h
