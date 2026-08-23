/-
**The MONADIC REBUILD of the Python tier** — `docs/python-monadic-rebuild.md`.

A SECOND Python semantics on the family substrate (`docs/family-architecture.md`
§3.4), written in do-notation, whose acceptance test is parity with the trunk
interpreter on the trunk's own differential battery.

**THE BOUNDARY, and it is deliberate.** This umbrella is imported by `Main.lean`
— so `lake build` CHECKS the whole rebuild and it cannot rot — but by NOTHING
else. In particular NOT by `LeanModels/Python.lean` and NOT by `LeanModels.lean`.
The trunk's consumers therefore see nothing of the rebuild: `Semantics.lean`
stays authoritative, no landed theorem's import graph moves, and the campaign's
files are untouched. §0.1 principle I is what forbids the other arrangement — a
validated definition is not swapped for an unvalidated one, and the differential
gate is what would eventually earn that right.

**And the import site was chosen by MEASUREMENT, not by tidiness.** 65 files
under `Examples/` import the `LeanModels` umbrella, including the expensive
sunfish proofs; gating the rebuild from there would invalidate every one of them
and charge the rebuild to the eleven other lanes sharing this master. `Main.lean`
is the one target that must know about the rebuild anyway — it is where the
`--monadic` shim lives — so the gate costs exactly the rebuild's own files.

`Monadic/` is a PRESENTATION sibling, never a VERSION sibling: it claims the same
edition (CPython 3.9), oracle and corpus as the trunk. §1.1's `<Lang>/<Ver>/`
convention does not apply to it.
-/
import LeanModels.Python.Monadic.Substrate
import LeanModels.Python.Monadic.Prim
import LeanModels.Python.Monadic.Eval
import LeanModels.Python.Monadic.Mono
import LeanModels.Python.Monadic.Spec
import LeanModels.Python.Monadic.Script
