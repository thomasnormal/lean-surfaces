# C++ callable object-frame bridge

2026-10-19. `LeanModels/Cpp/CallableFrame.lean` connects typed callable
parameters to the object-backed automatic-declaration fragment. It is a
stateful boundary for the next callable rung; it does not replace the existing
value-only `CallableEvaluation` or claim that `Translation.execute` runs.

`CallableObjectFrame.start` checks the target profile and arity, converts each
argument to its parameter's profile-resolved integral format, creates one
`IntegralObjectFrame`, enters the outer parameter scope and initializes each
parameter as a fresh automatic object. Unsupported parameter types, invalid
values, undefined conversions and mismatched arity remain typed refusals.
The parameter declaration handles are the same frontend identities retained by
`CallableFunction` and by initializer `DeclRefExpr` nodes.

`executeDeclStmt` accepts an `AdmittedAutomaticDeclStmt` from
`AutomaticDeclarations.lean` and runs its `IntegralObjectFrame.Statement` in
the initialized frame. The frame executor closes successful scope exits and
retains the frame on failures, so a local initializer can observe a parameter,
and a failed declaration leaves the parameter/local prefix and lifetime
tombstones available to a stateful caller. The bridge still takes one admitted
fragment at a time and does not claim complete C++ callable semantics.

`Callable.lean` now supplies that scope-aware admission for the integral
callable fragment. It threads parameter and local declaration handles through
sequential and nested compound statements, admits each `DeclStmt` through the
validated automatic-declaration evidence, and retains the resulting
`CallableStatement.automatic` node. Branch and loop shells parse locals in
their lexical scope; the object evaluator executes the same tree against the
parameter frame, opening and closing block scopes while preserving retained
state on errors. The established value-only evaluator remains deliberately
loud on this node (`unsupportedDeclaration`), so adding object-backed
execution cannot turn an old value-only result into a guessed one.

The object-backed evaluator is a bounded integral callable surface, not a
replacement for `Translation.execute`: unsupported calls, conversions,
non-integral declarations, and other frontend forms continue to refuse.

## Checks

`CallableFrameTests.lean` checks parameter initialization, a frontend-admitted
local read against that parameter, invalid argument values and unsupported
parameter types. `CallableObjectEvaluationTests.lean` additionally checks
local assignment, local increment and repeated loop-body declaration
allocation: each iteration gets a fresh object and the completed frame retains
the expected object history. The aggregate `LeanModels.Cpp.Tests` target
includes these guards together with the declaration-admission and object-frame
suites.
