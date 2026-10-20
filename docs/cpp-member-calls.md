# Direct calls on existing integral receivers

2026-10-20. N4950 [expr.call] and [class.mfct.non.static] permit a narrow
source bridge over the existing integral member getter and class receiver
projection surfaces. `IntegralMemberCallSyntax.admit` accepts a
`CXXMemberCallExpr` with exactly one `MemberExpr` child, an arrow receiver, a
validated identifier name, a `referencedMemberDecl` handle, and one direct
receiver `DeclRefExpr` with its own handle and qualified type spelling. A second child is an argument and
refuses as `unsupportedArguments`; missing or computed receiver evidence stays
loud.

`IntegralMemberCall.bind` takes the expected receiver handle and type, an
already admitted `IntegralMemberGetter`, and a caller-supplied
`ClassReceiverProjection`. It checks the method handle, source name, receiver
handle and receiver type exactly, then checks the projection with the getter. Invocation
delegates to `ClassReceiverProjection.invoke`, so the existing object identity,
constness, lifetime, field ownership, conversion and memory-preservation
rules remain authoritative. The retained syntax is provenance only.

This is not overload resolution or a general method-call evaluator. Arguments,
temporaries, lvalue/rvalue receiver conversions, member pointers, virtual or
qualified dispatch, construction, writes and calls whose target body is not an
admitted getter remain refusals. No method is selected from a name, and the
receiver handle never manufactures an object or an ABI address.

Kernel controls cover a successful call and result **7**, missing or malformed
call children, argument refusal, non-arrow receivers, missing method handles,
missing receiver types, bad names, method/name/receiver-handle mismatches and
receiver-type mismatch.
The controls use the existing projection's exact object state; no native
differential claim is made by this source bridge. Native getter and
class-subobject batteries remain the separate oracle for the underlying
already-admitted body and object projection.
