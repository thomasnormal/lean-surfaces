# Let expressions

IEEE 1800-2023 §11.12 `let` declarations introduce expression templates.
The frontend expands each use with its actual/default arguments and binds
free names in the declaration scope. The extractor consumes that bound
expression through the ordinary integral, conversion, four-state and statement
rules. A declaration allocates no runtime value. Module, generate, package,
compilation-unit, hierarchy and procedural declarations compose with the
existing store and scheduler; no function activation or new scheduler is added.

The shared storage pass preserves declaration identity when a procedural local
has the same spelling as another local or a module variable. Module names stay
public; colliding locals receive deterministic compilation-local names. Original
symbol references, including expanded template reads, use those identities.
Generated/source-name collisions refuse explicitly.

Slang also expands a forward use that §11.12 forbids. A separate check resolves
original syntax names in their actual lexical scopes, including nested templates
and macro expansion locations, and rejects a use before its declaration.
Whole-source errors and redefinitions remain loud even for unused templates.
Nonmodule roots now retain the existing `Hierarchy:module-kind` barrier rather
than acquiring module scheduling semantics. Symbolic extraction, unsupported
calls/effects/types and the single-module runtime boundary remain loud.

The paired **22,035** paths gain **33 clean extractions** and withdraw **12**
previous program admissions: **4,320 → 4,341 clean**, **17,649 → 17,628 partial**,
**66 include skips**, zero errors. Of 4,320 previously clean designs, 4,297 remain
identical, 11 change only their lexical storage bindings, and 12 now refuse.
All eleven binding regressions match complete independent transcripts under
both tested region oracles. Twenty-nine gained files also match both orders;
one gained multi-root file and one continuous-driver file retain runtime
refusals, and two explicit-formal-type files lack a usable reference result.
Extraction is distinct from runtime conformance.

Seven authored programs match complete independent transcripts under both
orders: lexical shadowing, named actuals, nested local templates, context sizing,
X/Z, package/unit/generate/hierarchy scopes, live reads, unused effectful actuals,
and NBA capture before later source writes. Three authored programs preserve
call, effect and program-scheduling refusals despite successful references.
The independent simulator rejects explicit formal data types (`LTUXDF`) and
the authored default-argument form (`LTUNDEF`). Their structural extraction is
checked, but no expected runtime transcript or execution agreement is claimed.
Fifty-one successful final-source references, including refused rows, are
bound to exact source bytes, invocation, status, complete stdout and provenance.

Four kernel theorems are checked against the actual parsed certificate source:
live declaration/actual reads, independence from the same-spelled local,
modular four-bit addition, and copyback retaining output and queued work.
They establish properties of this fixture, not a general frontend correctness
theorem. See [the fixtures and receipts](../Examples/system-verilog/let_expressions/README.md).
