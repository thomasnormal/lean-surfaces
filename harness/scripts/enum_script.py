"""leanpy corpus: `enumerate` IN A MODULE WITH NO GENERATOR DEF.

`enumerate(…)` allocates a generator FRAME, and `moduleGenFree` used to
claim that impossible without a generator `def` ("`callIn` is the only
allocator"), so the `for`-over-generator arm refused this file with
`internal: … heap well-formedness violation — report this` — ordinary
Python reported as an interpreter bug. Found 2026-08-13 by pointing
`tools/leanpy` at the shipped sunfish; `gen_script.py` never caught it
because that module defines generators of its own.
"""

tot = 0
for i, c in enumerate("PNBRQK"):
    tot += i * ord(c)
print(tot)


def enum_sum(s):
    out = 0
    for j, ch in enumerate(s):
        out += j * ord(ch)
    return out


print(enum_sum("abc"))
