# the opcode-shaped fallback (docs/backlog.md paragraph "del RECONCILED
# with the one pipeline"): module-level defs mutating module tables,
# calls and prints, then a TRAILING `del` of the def names. Static definition
# bindings cannot be tombstoned by the tier, so this remains a loud boundary.
opmap = {}
hasname = []


def def_op(name, op):
    opmap[name] = op


def name_op(name, op):
    def_op(name, op)
    hasname.append(op)


def_op('POP_TOP', 1)
def_op('ROT_TWO', 2)
name_op('STORE_NAME', 90)
print(opmap['POP_TOP'])
print(opmap['STORE_NAME'])
print(len(opmap))
print(len(hasname))
del def_op, name_op
