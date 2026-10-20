# Direct calls on existing integral receivers

2026-10-20. N4950 [expr.call] and [class.mfct.non.static] permit a narrow
source bridge over the existing integral member getter and class receiver
projection surfaces. `IntegralMemberCallSyntax.admit` accepts a
`CXXMemberCallExpr` with exactly one `MemberExpr` child, an arrow receiver, a
validated identifier name, a `referencedMemberDecl` handle, and one direct
receiver `DeclRefExpr` with its own handle and qualified type spelling. A second
child is an argument and refuses as `unsupportedArguments`; the call result's
qualified type spelling is also retained. Missing or computed receiver/result
evidence stays loud, and the referenced declaration must explicitly be a
`CXXMethodDecl`.

`IntegralMemberCall.bind` takes the expected receiver handle, an already
admitted `IntegralMemberGetter`, and a caller-supplied
`ClassReceiverProjection`. It checks the method handle and source name, checks
the receiver handle, derives the selected class name from the projection's
receiver path, and compares its pointer spelling to the retained receiver
type. It then checks the projection with the getter and matches the result
spelling against the admitted integral result, including represented builtin
aliases. Invocation
delegates to `ClassReceiverProjection.invoke`, so the existing object identity,
constness, lifetime, field ownership, conversion and memory-preservation
rules remain authoritative. The retained syntax is provenance only.

The AST method id is an occurrence handle; declaration probes may map that
occurrence to a different canonical method handle. `IntegralMemberCallSyntax`
starts with the occurrence as its canonical placeholder, and
`resolveCanonical` accepts exactly one distinct `CXXMethodDecl` canonical handle
from the probe, and that handle must also have an explicit self-canonical
`CXXMethodDecl` row (duplicate identical rows are harmless). Missing, non-method,
target-less, name-mismatched, or conflicting rows refuse loudly. Binding compares the resolved handle with the
canonical handle retained by `IntegralMemberGetter`, so a call cannot silently
cross a redeclaration or overload identity boundary.

This is not overload resolution or a general method-call evaluator. Arguments,
temporaries, lvalue/rvalue receiver conversions, member pointers, virtual or
qualified dispatch, construction, writes and calls whose target body is not an
admitted getter remain refusals. No method is selected from a name, and the
receiver handle never manufactures an object or an ABI address.

Kernel controls cover a successful call and result **7**, canonical resolution
and invocation through a noncanonical occurrence, missing or malformed call
children, argument refusal, non-arrow receivers, missing method handles, missing
receiver/result types, bad names, non-method targets, method/canonical/name/
receiver-handle mismatches, receiver-type mismatch and result-type mismatch.
The controls use the existing projection's exact object state; no native
differential claim is made by this source bridge. Native getter and
class-subobject batteries remain the separate oracle for the underlying
already-admitted body and object projection.
