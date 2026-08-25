/-
sunfish pin shard: the ROOK endgame (`posEnd`) — the correction arms.

SHARD of the `pins_bound` battery (2026-08-25 topology change): the
capstone prose, and the map of which board lives in which shard, are in
`pins_bound.lean`. Nothing here is new — every `#guard` moved VERBATIM
from that file, and the shard boundary is by POSITION so a red names its
board. `boundProbe` moved to `pins_common.lean` unchanged.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_bound_end

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

/-- Rook endgame (KRK-shaped — the mop-up/correction territory). -/
private def posEnd : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n ....k...\n ........\n ....K...\n ........\n .R......\n ........\n ........\n ........\n         \n         \n",
      .int 0, .tuple #[.bool false, .bool false],
      .tuple #[.bool false, .bool false], .int 0, .int 0]

-- endgames: the correction arms
#guard boundProbe posEnd 0 1 == some (111, 5)
#guard boundProbe posEnd 0 2 == some (91, 5)
#guard boundProbe posEnd 0 3 == some (0, 2)
#guard boundProbe posEnd 60 3 == some (137, 13)

end Examples.python.sunfish.pins_bound_end
