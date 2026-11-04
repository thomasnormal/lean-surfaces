#!/usr/bin/env python3
"""F3b/F3c CENSUS — the depth-0 QS fold's CUT exit, measured on the shipped engine.

Census-first, per §L30. Before `Inv` is stated for the cut arm, this measures
what the arm actually does on real search traffic:

  * how the depth-0 schedule is SHAPED (stand-pat, killer?, sorted rounds),
  * which EXIT each node takes (cut / settled / ran),
  * WHERE in the schedule the cut fires,
  * and whether a shadow fold built from the model's own round classification
    reproduces the engine's answer at every node (the §L30 discipline: measure,
    then check the model reproduces the engine, before writing a premise).

Nothing here is a proof. It is the table the statement gets written against.
"""
import sys, os, collections
sys.setrecursionlimit(100000)

HERE = os.path.dirname(os.path.abspath(__file__))
SF = os.path.join(HERE, "lean-basecase", "Examples", "python", "sunfish")
sys.path.insert(0, SF)
import sunfish as SFM

MU, ML, QS, ER = SFM.MATE_UPPER, SFM.MATE_LOWER, SFM.QS, SFM.EVAL_ROUGHNESS

# ---------------------------------------------------------------- observation
REC = []            # one record per FOLDING depth-0 node
PROBE_HIT = [0]     # depth-0 nodes the table answered without folding
KING_GONE = [0]     # depth-0 nodes the king check answered
_seen = set()
_busy = [False]

_orig_bound = SFM.Searcher.bound


def traced_bound(self, pos, gamma, depth, root=False):
    """Census wrapper. The shadow fold runs BEFORE the real call so it sees the
    SAME table; the real call then reproduces it (a same-gamma table hit returns
    the very number the child's fold produced, so warming is benign)."""
    if _busy[0] or root or max(depth, 0) != 0:
        return _orig_bound(self, pos, gamma, depth, root)
    if pos.score <= -ML:                      # the king-capture leaf, not a fold
        KING_GONE[0] += 1
        return _orig_bound(self, pos, gamma, depth, root)
    entry = self.tp_score.get((pos, 0), SFM.Entry(-MU, MU))
    if entry.lower >= gamma or entry.upper < gamma:
        PROBE_HIT[0] += 1                     # the stale-table leaf: NO fold runs
        return _orig_bound(self, pos, gamma, depth, root)
    key = (pos, gamma)
    if key in _seen:
        return _orig_bound(self, pos, gamma, depth, root)
    _seen.add(key)
    _busy[0] = True
    try:
        shadow = shadow_fold(self, pos, gamma)
    except Exception:
        shadow = None
    finally:
        _busy[0] = False
    r = _orig_bound(self, pos, gamma, depth, root)
    if shadow is not None:
        REC.append((shadow, r, len(schedule(self, pos, gamma))))
    return r


SFM.Searcher.bound = traced_bound


# ------------------------------------------------------------- shadow fold
def schedule(searcher, pos, gamma):
    """The depth-0 schedule, exactly as `moves()` yields it at depth 0.

    `2 < depth < 6` is false and the killer needs `val >= QS` (because `depth`
    is falsy), so this is `standPat :: killer? :: sortedRounds` and nothing else.
    """
    rounds = [("standPat", None, pos.score)]
    killer = searcher.tp_move.get(pos)
    if killer is not None:
        val = pos.value(killer)
        if val >= QS and (val >= ML or pos.score + val >= gamma):
            rounds.append(("killer", killer, val))
    rest = sorted(((v, m) for m in pos.gen_moves() if (v := pos.value(m)) >= QS),
                  reverse=True)
    for v, m in rest:
        rounds.append(("move", m, v))
    return rounds


def shadow_fold(searcher, pos, gamma):
    """Re-derive the engine's answer from the round classification alone.

    Returns (answer, exit, cut_index, n_rounds, kinds). The child call is the
    REAL `bound` at `move_depth = -1`, which re-floors to 0 — which is why the
    induction is on F1's board measure and not on depth.
    """
    rounds = schedule(searcher, pos, gamma)
    best, live = -MU, False
    kinds = []
    for idx, (kind, mv, val) in enumerate(rounds):
        if kind == "standPat":
            score = pos.score
            kinds.append("standPat")
        elif val >= ML:
            score, live = MU, True
            kinds.append("mateBand")
        else:
            cap = pos.score + val                    # depth 0: no slope term
            if cap < gamma:
                best = max(best, cap)
                kinds.append("settle")
                return best, "settled", idx, len(rounds), kinds
            score = min(cap, -_orig_bound(searcher, pos.move(mv), 1 - gamma, -1))
            live |= score > -MU
            kinds.append("searched")
        best = max(best, score)
        if best >= gamma:
            return best, "cut", idx, len(rounds), kinds
    return best, "ran", None, len(rounds), kinds


# ------------------------------------------------------------------- driver
def main():
    hist = [SFM.Position(SFM.initial, 0, (True, True), (True, True), 0, 0)]
    searcher = SFM.Searcher()
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 12000
    try:
        for _ in searcher.search(hist):
            if searcher.nodes > budget:
                break
    except Exception as exc:
        print(f"(search ended: {type(exc).__name__})", file=sys.stderr)
    SFM.Searcher.bound = _orig_bound

    exits, cutpos, sched_len, kindmix = (collections.Counter() for _ in range(4))
    mismatch = cut_on_standpat = 0
    for (ans, ex, idx, n, kinds), r, nsched in REC:
        exits[ex] += 1
        sched_len[min(n, 12)] += 1
        for k in kinds:
            kindmix[k] += 1
        if ex == "cut":
            cutpos[min(idx, 8)] += 1
            if idx == 0:
                cut_on_standpat += 1
        if ans != r:
            mismatch += 1

    tot = sum(exits.values()) or 1
    print(f"engine nodes: {searcher.nodes}")
    print(f"depth-0 entries answered by the KING check (no fold): {KING_GONE[0]}")
    print(f"depth-0 entries answered by the TABLE PROBE (no fold): {PROBE_HIT[0]}")
    print(f"depth-0 nodes that actually FOLD, censused: {tot}")
    print()
    print("EXIT distribution among FOLDING nodes")
    for k in ("cut", "settled", "ran"):
        print(f"  {k:8s} {exits[k]:6d}  {100*exits[k]/tot:5.1f}%")
    print()
    print("CUT position in the schedule (0 = the stand-pat itself)")
    for i2 in sorted(cutpos):
        lbl = f"{i2}" if i2 < 8 else ">=8"
        print(f"  round {lbl:>3s}  {cutpos[i2]:6d}")
    print(f"  cut on the STAND-PAT alone: {cut_on_standpat}"
          f"  ({100*cut_on_standpat/max(exits['cut'],1):.1f}% of cuts)")
    print()
    print("SCHEDULE length (rounds available, capped at 12)")
    for i2 in sorted(sched_len):
        print(f"  {i2:>3d} rounds  {sched_len[i2]:6d}")
    print()
    print("ROUND KINDS consumed")
    for k, v in kindmix.most_common():
        print(f"  {k:10s} {v:7d}")
    print()
    print(f"SHADOW-FOLD MISMATCHES vs the engine: {mismatch}   "
          f"({'MODEL REPRODUCES THE ENGINE' if mismatch == 0 else 'MODEL DIVERGES'})")


if __name__ == "__main__":
    main()
