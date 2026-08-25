/-
sunfish pin shard: the MIDGAME board (`posMid`), depths 1-3.

SHARD of the `pins_bound` battery (2026-08-25 topology change): the
capstone prose, and the map of which board lives in which shard, are in
`pins_bound.lean`. Nothing here is new — every `#guard` moved VERBATIM
from that file, and the shard boundary is by POSITION so a red names its
board. `boundProbe` moved to `pins_common.lean` unchanged.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_bound_mid

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

/-- Midgame (Italian-shaped, after 1.e4 e5 2.Nf3 Nc6 3.Bc4 Nf6 4.d3
Bc5 — the position the side to move sees). -/
private def posMid : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n r.bqk..r\n pppp.ppp\n ..n..n..\n ..b.p...\n ..B.P...\n ...P.N..\n PPP..PPP\n RNBQK..R\n         \n         \n",
      .int (-13), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

-- midgame
#guard boundProbe posMid 0 1 == some (2, 66)
#guard boundProbe posMid 60 1 == some (35, 5)
#guard boundProbe posMid 0 2 == some ((-1), 586)
#guard boundProbe posMid 60 2 == some (59, 240)
#guard boundProbe posMid 0 3 == some (2, 413)
#guard boundProbe posMid 60 3 == some (59, 240)

end Examples.python.sunfish.pins_bound_mid
