# C++ automatic integral declarations: specification and price

2026-10-19. **Strict frontend admission with bounded callable execution.** The
automatic-local adapter admits a narrow `DeclStmt` shape into the
object-backed frame, and the object-backed callable profile now threads those
declarations through real callable bodies. This contract connects source
declarations to [integral objects](cpp-integral-objects.md), rather than
introducing another value store beside the lifetime model. The pricing tool
measures archived body inventories; it does not execute a body or validate a
function signature.

## Normative anchors

Baseline: N4950, the public C++23 working draft linked by the
[charter](cpp-charter.md). The relevant clauses are:

- §6.4.2 `[basic.scope.pdecl]`: a declarator introduces its name before its initializer.
- §6.7.3 `[basic.life]`: initialization completion matters to lifetime start.
- §6.7.5.4 `[basic.stc.auto]`: block and parameter objects have automatic storage, unless otherwise specified.
- §8.8 `[stmt.dcl]`: exited automatic objects are destroyed in reverse construction order.
- §8.6.4 `[stmt.for]`: the loop initializer has loop scope; a body `continue` reaches the step.
- §9.4.1 `[dcl.init.general]` and §9.4.5 `[dcl.init.list]`: initialization forms remain distinct.

The remaining sections are the proposed model contract and implementation
obligations, not claims that the current interpreter already satisfies them.

## Object-backed frame contract

An executing frame has one `IntegralObjectStore`, declaration-handle bindings,
and a stack of scopes. Parameters and automatic locals both use that store.
Bindings distinguish Clang declaration occurrences; equal spellings do not
identify objects. Each dynamic execution of a declaration allocates a fresh
`ObjectId`, including repeated loop-body declarations. Object identities are
not recycled when a scope ends.

Entering a declaration allocates storage and installs its binding **before**
evaluating its initializer. A self-reference consequently resolves to the new
declaration, not an outer same-named variable. It must not acquire an invented
value. `IntegralObjectStore`'s not-yet-live and indeterminate-read refusals stay
loud; this slice does not classify every rejected access as one C++ UB rule.

After a successful initializer, `initializeConverted` publishes the validated
destination value and live object atomically. Default initialization without
an initializer uses `defaultInitialize`: a mutable scalar can subsequently be
assigned without first reading it. An empty braced initializer is **not** this
operation; its integral value-initialization supplies zero. Constness belongs
to the object/access type and remains enforced after declaration admission.
Lvalue-to-rvalue conversion can remove top-level cv from the expression's
value type without removing constness from its storage access.

Multiple declarators execute left to right, each binding being available to
later initializers. Retain the state after every completed prefix, including
if a later initializer refuses. Copy, direct, direct-list and copy-list scalar
initialization retain their frontend form and conversion evidence. A resolved
`auto` type or typedef spelling is not guessed from `qualType`: it needs the
same structured canonical type witness as a spelled builtin.

The automatic integral target includes initialization and assignment after
default initialization, const objects, multiple declarators, shadowing, nested
blocks and loop-local declarations. Static/thread storage, extern declarations,
volatile operations, references, arrays, records, local type declarations,
attributes and exceptional cleanup require separately represented semantics.
Unsupported declarators must never be rewritten to `skip` or silently treated
as automatic integral storage.

## Scopes and control transfers are prerequisites

The callable embedding now retains ordinary `CompoundStmt` nodes as `block`
boundaries (the `switch_` node retains its compound clause boundary) and each
admitted `ForStmt` as a first-class `forLoop` with separate initializer,
condition, step and body. The evaluator runs the step after the body returns,
including a propagated `continue`, and runs the initializer only once. It no
longer injects the step inside source blocks. These are represented control
boundaries; with declarations still refused they neither allocate objects nor
implement scope cleanup.

`LeanModels/Cpp/IntegralObjectFrame.lean` now supplies the object-backed frame,
scope state and a small stateful control shell. Its binding API attaches a
declaration occurrence to a fresh object and retains the frame on every result;
its `Statement` executor handles blocks, conditions, loops and transfers.
`LeanModels/Cpp/AutomaticDeclarations.lean` is the frontend step: given a
validated probe, it joins an exact `DeclStmt` path to direct `VarDecl` children,
structured type rows, variable storage/initializer rows and binary-expression
rows. It emits `IntegralObjectFrame.Statement` declarations, so the frame can
reserve storage before evaluating an initializer and retain self-initialization
failures. The adapter admits only automatic, nonvolatile integral objects with
no attributes; unsupported storage, types, calls, multi-element lists and
implicit operand conversions remain loud.

The frontend adapter must attach these scopes to the retained control
boundaries:
a `for` initializer scope encloses its condition, step and body; each execution
of a compound body has its own nested scope. `IntegralObjectStatement` also has
a first-class loop shape, but it does not allocate or bind locals. Its
preallocated-object API is not itself a source-declaration executor.

Declaration-bearing conditions and `if`/`switch` init-statements also need
scoped control nodes before their source forms can be admitted. Their child
lists must not be reinterpreted as ordinary expression conditions. Keep those
existing refusals until their construction/exit points are represented.

Ordinary completion, return, break and continue unwind exactly the scopes they
exit. Record the return value before ending the frame's local lifetimes. An
inner loop owns its transfers; a switch consumes its own break and passes an
outer-loop continue through. A `for` step runs once **after** body-scope exit,
then its condition is tested. Reverse-order lifetime ending leaves tombstones
and restores outer bindings without reviving an ended inner object.

Retain the frame on all interpreter outcomes. Fuel exhaustion, a refused
initializer or a reported undefined operation is not a successful scope exit:
do not fabricate cleanup for an execution whose continuation is unknown.
Initialization failure must not publish an initialized local or roll back the
earlier declarators' state. The existing public integral-return API may project
a completed value, but stateful specifications must observe the retained frame.

## Frontend evidence needed before admission

The probe already projects `VarDecl` types. Add versioned variable-shape
witnesses for local/parameter status, storage duration, TLS status and the
initializer kind/identity, using the pinned Clang getters. Cross-check the
`DeclStmt` children, declaration identity, structured type, initializer and
`DeclRefExpr` target against the same AST. Missing storage fields or a missing
type row must not manufacture an automatic int declaration.

The initializer boundary also needs structured source/converted expression
types, including non-binary expressions; the current binary-only supplement
is not sufficient evidence for every initializer conversion.

Initialization expressions then use the admitted expression rules and
destination conversion. Preserve initializer-list boundaries; do not infer
value initialization from an absent child. The existing binary-expression
source-type checker expects bare builtin types, so qualified local reads need
an explicit cv/value-conversion bridge rather than erasing qualifiers globally.
Structural fuel recursion and kernel-reducible state operations are required
before the proof surface promises definitional execution of these bodies.

## Measured opportunity, not a coverage forecast

`extractors/cpp/price_local_declarations.py` consumes the archived
`ls-cpp-r0-census-1` body-inventory format. It separates reported source
ownership, implicit bodies, methods and ordinary `FunctionDecl` occurrences.
These are occurrence counts, including instantiation copies, not distinct
source functions. Ownership is inherited from the inventory's recorded
sticky-location method, not re-established by this tool.

| Pinned public inventory | Nonimplicit target bodies | Bodies containing `DeclStmt` | Ordinary bodies | Ordinary bodies containing `DeclStmt` | Raw-kind-only candidates after adding locals |
| --- | ---: | ---: | ---: | ---: | ---: |
| TinyXML-2 `321ea883b7190d4e85cae5512a12e5eaa8f8731f` | 202 | 127 | 2 | 2 | 0 |
| nlohmann/json `9cca280a4d0ccf0c08f47a99aa71d1b0e52f8d03` | 926 | 286 | 191 | 43 | 1 |

The two XML ordinary bodies also contain `CallExpr`. Forty of JSON's 43
ordinary declaration-containing bodies contain `CallExpr`; other remaining
kinds include member access, class construction and casts. The sole JSON
raw-kind candidate still needs signature, template and typed-expression
admission. No new admitted function is established by this inventory.

`DeclStmt` presence does not prove an integral variable: aliases and nested
definitions can contribute it too. `<missing>` includes legitimate empty
`for` placeholders, so it is reported as context-dependent, not automatically
counted as a rejection. Kind-only candidates are deliberately permissive;
they do not discharge node shape, conversions, declaration scope or type.
Full remaining kind sets are retained rather than ranking only the first wall.

A separate recovered 34,496,558-byte XML schema-0.3 probe has 764 expression
rows, eight of whose occurrence handles are absent from the raw AST. It remains
a useful negative control: the strict global expression-evidence validator must
refuse that unchanged artifact rather than silently repair it. The live probe
now observes the same-process JSON dump before publishing rows, so fresh runs
move such occurrences to the `expression_refusals` ledger and validate only
rows with raw AST witnesses. The compiler control
`int buffer[1 + 1]; int identity(int value) { return value; }` produces one
explicit out-of-dump refusal, with no fabricated evidence row; its body needs no
local-declaration support. This is a frontend/join diagnostic, not execution of
that control program.
The JSON full-probe census has a recorded 300-second timeout. Neither result
may be replaced by agreement on a small projection or counted as execution.
Automatic declarations are a necessary language milestone, not a promised
three-corpus flip. Resolve the evidence-join blocker before claiming a new
whole-artifact callable census.

```console
python3 extractors/cpp/test_price_local_declarations.py
python3 extractors/cpp/price_local_declarations.py BODY_INVENTORY.json --out local-pricing.json
```

The input-byte cap is 64 MiB by default. Schema, ownership, function kinds and
positive integer node counts are checked; duplicate object fields, nonfinite
tokens and input/output aliases refuse. Reports pin their input bytes/hash,
publish atomically, and omit source paths, names and corpus labels. They claim
no semantic admission and no execution. Timing and process-memory limits
belong to the external receipt.

## Acceptance obligations for the next executable rung

- Preserve typed declaration and scope nodes from complete real artifacts; keep malformed/unsupported declarations loud.
- Check Clang-emitted copy/direct/list/default initialization, resolved types, multiple declarators and distinct shadow handles.
- Differentially compare defined integral results and mutations at `-O0`/`-O2` under UBSan; do not oracle uninitialized or out-of-lifetime reads as defined runs.
- Prove frame/store coherence, fresh allocation, const enforcement, retained prefix state and scope-ending properties without new axioms.
- Include loop re-entry, nested scopes, nearest-loop/switch transfers and return-before-cleanup in stateful checks.
- Re-run the three-corpus census with source ownership, full wall sets and extraction/time-budget failures separate from execution verdicts.

The current compiler/Lean regression admits the ordinary integral copy,
direct, list and default forms, including multiple declarators, `auto`, const
objects, shadowing, self-initialization and a loop-local declaration. It keeps
static/thread storage, volatile objects, references, arrays and aliases loud.
It checks Clang's distinct shadow handles, self-initializer binding and
preceding-declarator references without executing an undefined
self-initialization. The literal-fixture loader uses an explicit
`maxRecDepth 100000` caller budget; production defaults are unchanged. These
are frontend/refusal controls, not proofs or execution claims about prototype
programs.

The optional [variable-evidence supplement](cpp-variable-evidence.md) records
versioned Clang storage, role, initializer, constexpr and attribute
observations with strict root/`inner` joins and structured source/converted
types. `AutomaticDeclarationsTests.lean` covers literal and default/zero
initialization, multiple declarators, preceding-declarator reads,
self-initialization with retained storage, unsupported storage and missing
joins. This is an admitted source fragment and frame proof surface; broad
callable-body admission, conversions and a three-corpus execution census
remain separate obligations.
