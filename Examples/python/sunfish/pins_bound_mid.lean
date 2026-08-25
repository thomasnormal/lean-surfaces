/-
sunfish pin shard: the MIDGAME board `posMid` — now a sub-facade.

MEASURED, and it is why this file has no probes left: the first sharding put
all six `posMid` guards here and the profile came back at 875 s — 74% of the
bound family, capping its win at 1.3x when 2x was hoped. The cost is not the
board, it is DEPTH: node counts across the pairs run 71 / 826 / 653 for
depths 1 / 2 / 3, and those numbers are printed in the certificates.

  `pins_bound_mid_d1`   71 nodes   ~5%
  `pins_bound_mid_d2`  826 nodes  ~53%
  `pins_bound_mid_d3`  653 nodes  ~42%

Splitting by depth therefore predicts a critical path of ~7.8 min against
14.6 — the d2 pair — rather than the even thirds a guard COUNT would suggest.
An even split was available by mixing depths across shards and would have been
marginally better still, and it was NOT taken: it muddies what a red names,
and the fleet floor is `pins_clock_walk` at 19.1 min either way, so the
balance buys nothing that matters.

NO probe dropped, NO fuel changed, every expected value byte-identical.
-/
import Examples.python.sunfish.pins_bound_mid_d1
import Examples.python.sunfish.pins_bound_mid_d2
import Examples.python.sunfish.pins_bound_mid_d3
