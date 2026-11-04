# C++ integral reference parameters

The callable signature admits nonvolatile integral lvalue-reference parameters,
including const referents. Their declared structured reference types remain in
`CallableFunction.parameters` and its signature. Only body expression bindings
use the referent type, as required for a named reference expression. The exact
parameter/type-evidence and expression-type checks remain in force.

`CallableArgument.value` supplies an evaluated integral prvalue;
`CallableArgument.lvalue` supplies an existing object identity and type view.
`CallableObjectFrame.startInStore` starts fresh callee scopes over the explicit
caller store. `CallableObjectEvaluation.evaluateCallableObjectInStore` executes
the selected body and returns the frame and store on success or failure.
Neither API imports the caller's declaration scopes or resolves call syntax.
All lvalue identities and views are checked against the entry store before
parameter allocation. A later argument cannot designate an object that only
an earlier parameter's initialization will create.

A reference parameter binds the existing live object without reading its value
or allocating storage. Both the source view and the actual object's type must
permit the binding: integral kinds agree, volatile types refuse, and const may
be added but never dropped. Multiple parameters can designate the same object.
An uninitialized live object may bind and later be initialized through a mutable
reference. A const-reference parameter still observes mutation through another
mutable alias; it does not own a snapshot.

The differential witness exercises two reference parameters bound to the same
caller object. The first write is visible through the second binding, and the
returned value and caller store both observe the final write.

A value parameter receives its own initialized automatic object. When the
argument is an lvalue, the model reads the supplied view and then converts and
copies the value. Normal-return cleanup ends owned parameter/local lifetimes
and removes all callee bindings; reference parameters never end caller-owned
objects. Setup failures retain the completed parameter prefix and execution
failures retain the current frame under the existing interpreter convention.

The legacy `start`, `evaluateCallableObject`, and value-only `evaluateCallable`
interfaces accept values and continue to refuse reference signatures. No value
is silently treated as an object identity. Reference results, rvalue references,
temporary binding/lifetime extension, volatile referents, subobjects and pointer
or class arguments remain loud. This is an existing-object call boundary, not
an implementation of `CallExpr` or general interprocedural evaluation.

`IntegralObjectFrame.bindReferenceParameter_store` states that binding leaves
the entire store unchanged for every outcome. Kernel controls additionally pin
alias/distinct results, value copies, caller-scope isolation, const and stale
lifetime refusals, uninitialized binding and retained setup state. The native
battery uses Clang's actual reference signatures, checking return values,
post-call caller objects and callee-owned object cleanup.

## Measured boundary

The new native battery has **320 defined rows** at `-O0`/`-O2` under UBSan,
covering all **12** integral kinds, alias/distinct arguments, const caller
objects, immediate/value-copy arguments, local references to reference
parameters, loop/compound assignment and static methods. Four compiled
signatures pin the rvalue-reference, volatile, pointer-reference and
reference-result refusals. The store-preservation theorem and combined kernel
regressions print only `propext`; they introduce no new axiom.

The complete original XML probe still has **one admitted / 471 refused**
explicit source bodies, with a byte-identical census report. Re-exporting its
previously admitted header helper and rebuilding its theorem are regression
checks, separate from these reference controls. No new original-artifact
reference theorem, call-expression execution, completed rung or three-corpus
execution result is established by this boundary.
