/-
sunfish pin shard: the TACTICAL board (`posTac`) and the QUIET PAWN
endgame (`posPend`).

SHARD of the `pins_bound` battery (2026-08-25 topology change): the
capstone prose, and the map of which board lives in which shard, are in
`pins_bound.lean`. Nothing here is new — every `#guard` moved VERBATIM
from that file, and the shard boundary is by POSITION so a red names its
board. `boundProbe` moved to `pins_common.lean` unchanged.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_bound_tac

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

/-- Tactical (a Scholar's-mate-shaped attack: the side to move has a
mate-band line — the king-capture sentinel path). -/
private def posTac : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n r.bqkb.r\n pppp.ppp\n ..n..n..\n ....p..Q\n ..B.P...\n ........\n PPPP.PPP\n RNB.K.NR\n         \n         \n",
      .int (-38), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

/-- Quiet pawn endgame (kings and one pawn each). -/
private def posPend : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n ....k...\n .....p..\n ........\n ........\n .....P..\n ........\n ....K...\n         \n         \n         \n",
      .int 0, .tuple #[.bool false, .bool false],
      .tuple #[.bool false, .bool false], .int 0, .int 0]

-- tactical: pass 7 answered MATE_LOWER exactly here; engine master
-- settles on the futility cap first (see the header)
#guard boundProbe posTac 0 2 == some (277, 3)
#guard boundProbe posTac 0 3 == some (417, 24)

#guard boundProbe posPend 0 2 == some (19, 2)
#guard boundProbe posPend 60 2 == some (50, 13)
#guard boundProbe posPend 0 3 == some (50, 14)

end Examples.python.sunfish.pins_bound_tac
