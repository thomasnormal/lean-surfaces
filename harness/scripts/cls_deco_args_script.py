"""leanpy corpus: the PRECISION pin beside `cls_deco_script.py`.

The third-door fix must refuse a class for a DECORATED method and for
nothing else. The tempting cheap implementation reads the method's
`args_unsupported`, which is a comma-joined message carrying
"decorators" alongside "*args", "**kwargs" and "defaults" — none of
which is a creation effect: an unusual SIGNATURE is refused at CALL
time and does nothing whatever at the `class` statement.

So ingestion reads the structured `has_decorators` flag instead
(`methodCreationPure`, Json.lean), and this script is what would go red
if that ever regressed to matching on the message: `Sig`'s methods are
out of tier to CALL, its creation is pure, and the script runs to
completion exactly as CPython does.
"""


class Sig:
    """Creation-pure: undecorated methods, whatever their signatures."""

    def wide(self, *rest, **kw):
        return len(rest)

    def defaulted(self, x, y=3):
        return x + y


class Plain:
    def __init__(self, n):
        self.n = n

    def double(self):
        return self.n * 2


print(Plain(21).double())
print("creation pure with odd signatures in the file")
