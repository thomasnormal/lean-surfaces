/-
**The MONADIC REBUILD of the Python tier** — `docs/python-monadic-rebuild.md`.

A SECOND Python semantics on the family substrate (`docs/family-architecture.md`
§3.4), written in do-notation, whose acceptance test is parity with the trunk
interpreter on the trunk's own differential battery.

**THE SURFACE, AS IT ACTUALLY IS SINCE THE COLLAPSE** (corrected per
docs/quality-audit-2026-08-23.md §python — this header described the
arrangement that the acceptance gate RETIRED, which is the stated-vs-actual
defect the audit exists to catch):

* **The RUNNER is the rebuild, unconditionally.** `Main.lean` calls
  `Monadic.callInMono` and `Monadic.runScriptClockMono` directly; the
  `--monadic` flag and `harness/monadic_gate.py` are both gone. So
  `diff_test`, `script_corpus`, `refusal_census` and every leanpy surface
  measure THIS definition, and the differential's other side is CPython.
* **The PROOF umbrella is still the trunk.** `LeanModels/Python.lean` imports
  `Semantics.lean` and not this file, so every landed theorem's import graph
  is unchanged and the campaign's files are untouched.

That split is the whole of the current arrangement: **executable behaviour is
the rebuild's, proved behaviour is still the trunk's**, and the two are held
together by the pure workers they SHARE (`Monadic/Substrate.lean` §what is
shared) rather than by a gate comparing them. A capability that opens here
therefore reaches the harnesses immediately and the proof layer not at all —
which is what the no-backwards-compat ruling intends, and what makes the
trunk's remaining arms refusals rather than implementations.

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
