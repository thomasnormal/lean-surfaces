"""Module-global dict shared across nested calls (acceptance case 15,
docs/memory-model.md): the transposition-table shape of sunfish's
`Searcher.tt_score` reduced to its module-global essence. One PUBLIC call
sees every mutation its nested calls made (the world threads through
`callIn`); two public calls start fresh (closed-function semantics:
`initWorld` per call). The fresh-across-public-calls half is pinned
Lean-side (`spec.lean`) — CPython's imported module persists, so a
differential row for it would compare different lifecycles by design."""

tt = {}
BIG = 60000


def tt_put(k, v):
    tt[k] = v


def tt_get(k, d):
    return tt.get(k, d)


def put_get(k, v):
    # sharing within one public call: the nested calls mutate/read ONE dict
    tt_put(k, v)
    tt_put(k + 1, v + 10)
    return (tt_get(k, -BIG), tt_get(k + 1, -BIG), tt_get(k + 2, -BIG), len(tt))


def fresh_probe(k):
    # on a fresh world the table is empty: the default comes back
    return tt.get(k, -BIG)
