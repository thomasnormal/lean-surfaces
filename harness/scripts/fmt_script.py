"""leanpy corpus: %-formatting at module scope — the opcode.py shape.

`opname = ['<%r>' % (op,) for op in range(256)]` was opcode.py's SOLE
wall (docs/memory-model.md §`%`-formatting on strings); this is the same
construction at lab scale, with the def_op-style mutators and the
trailing `del` that follow it there.
"""

opname = ["<%r>" % (op,) for op in range(8)]
opmap = {}


def def_op(name, op):
    opname[op] = name
    opmap[name] = op


def_op("POP_TOP", 1)
def_op("NOP", 4)

print(len(opname), opname[0], opname[1], opname[4], opmap["NOP"])
print("%s=%d (%d%% sure)" % ("depth", 7, 95))
print("%r %r %r" % (True, None, "it's"))
print("%s %r" % ("plain", "quoted"))

del def_op
