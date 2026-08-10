"""init_lab — module-init EXECUTION (pass 3, docs/memory-model.md
§module-init execution) at lab scale: the padding loop's constructs
(dict .items() iteration with subscript stores, a module-level lambda
rebound per iteration reading the loop target THROUGH THE LIVE GLOBALS,
sum over a genexp of computed slices, tuple repetition), a top-level
while, and post-loop bindings reading the mutated table — every getter
differential against CPython."""

tbl = {"a": (1, 2), "b": (3, 4)}
base = {"a": 10, "b": 100}
for k, row in tbl.items():
    pad = lambda r: (0,) + tuple(x + base[k] for x in r) + (0,)
    tbl[k] = sum((pad(row[i : i + 1]) for i in range(2)), ())
    tbl[k] = (9,) * 1 + tbl[k]

TOTAL = tbl["a"][2] + tbl["b"][3]

x = 1
while x < 5:
    x = x * 2
M = x


def get_a():
    return tbl["a"]


def get_b():
    return tbl["b"]


def get_total():
    return TOTAL


def get_m():
    return M


def get_k():
    return k


def call_pad(n):
    # the loop's LAST lambda, called post-init from a function body: the
    # closure dispatches through the live view; its body reads base and
    # the final k the same way
    return pad((n,))
