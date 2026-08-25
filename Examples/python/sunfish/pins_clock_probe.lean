/-
sunfish pin shard: the seeded SURFACE — `boundProbeT` on the opening
and tactical boards.

SHARD of the `pins_clock` battery (2026-08-25 topology change): the prose
and the shard map are in `pins_clock.lean`. Every `#guard` moved VERBATIM;
`searcherWT`/`boundProbeT` moved to `pins_common.lean` unchanged.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_clock_probe

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

/-! ### The seeded surface, pinned natively

`boundProbeT []` agrees with the battery's `boundProbe` rows
(pins_bound.lean) — the `[]`-boundary sanity — and a NONEMPTY trace
answers the same pairs, the transport's content sampled on concrete
traces (all `#guard`: the untrusted evaluator, the batteries' standing
trust level; the theorem above is what upgrades any of these to
`∀ tr` the moment its empty-trace instance is proved). -/

#guard boundProbeT [] (posH 0) 0 1 == some (0, 2)
#guard boundProbeT [123] (posH 0) 0 1 == some (0, 2)
#guard boundProbeT [7, 8, 9] (posH 0) 40 1 == some (37, 34)

/-- Tactical. Pass 7 answered `MATE_LOWER` exactly here — the
king-capture sentinel path; engine master's futility cap settles the
position first (pins_bound.lean's header records the measurement). The
row is kept for its TRACE content, which is what this file pins. -/
private def posTacC : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n r.bqkb.r\n pppp.ppp\n ..n..n..\n ....p..Q\n ..B.P...\n ........\n PPPP.PPP\n RNB.K.NR\n         \n         \n",
      .int (-38), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

#guard boundProbeT [] posTacC 0 2 == some (277, 3)
#guard boundProbeT [55] posTacC 0 2 == some (277, 3)

end Examples.python.sunfish.pins_clock_probe
