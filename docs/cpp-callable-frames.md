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
tombstones available to a stateful caller. The bridge deliberately takes one
admitted fragment rather than silently changing the existing callable body
admission: complete callable statements still need a scope-aware frontend
tree, return handling and control-shell integration.

## Checks

`CallableFrameTests.lean` checks parameter initialization, a frontend-admitted
local read against that parameter, invalid argument values and unsupported
parameter types. The aggregate `LeanModels.Cpp.Tests` target includes these
guards together with the declaration-admission and object-frame suites.
