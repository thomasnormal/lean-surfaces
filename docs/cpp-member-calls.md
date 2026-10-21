# Direct calls on existing integral receivers

2026-10-20. N4950 [expr.call] and [class.mfct.non.static] permit a narrow
source bridge over the existing integral member getter and class receiver
projection surfaces. `IntegralMemberCallSyntax.admit` accepts a
`CXXMemberCallExpr` with exactly one `MemberExpr` child, an arrow or direct-dot
receiver, a
validated identifier name, a `referencedMemberDecl` handle, and one direct
receiver `DeclRefExpr` with its own handle and qualified type spelling. A second
child is an argument and refuses as `unsupportedArguments`; the call result's
qualified type spelling is also retained. Missing or computed receiver/result
evidence stays loud, and the referenced declaration must explicitly be a
`CXXMethodDecl` when resolved through probe metadata. Clang's raw JSON may carry
that method reference as either an object with `kind`/`id` or a string id;
`admitResolved` validates the latter against the complete probe. The callee
`MemberExpr` is retained at its Clang `prvalue` category.

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
Arrow calls compare the retained receiver type with `<class name> *`; direct-dot
calls compare it with `<class name>`. Both forms still require the caller's
explicit existing-object projection and receiver declaration handle. A single
`LValueToRValue` `ImplicitCastExpr` around a direct pointer `DeclRefExpr` is
retained as receiver evidence, and a nested `NoOp` wrapper is retained as well;
other casts and computed bases remain loud.
`CXXThisExpr` bases refuse as `missing-this-owner` because the call node does
not carry a receiver declaration handle; an enclosing method context is not
guessed from a raw call fragment.
Callers that start from raw AST are expected to use `admitResolved`, which
performs both syntax admission and this canonical resolution in one operation.
`extractors/cpp/census_member_calls.lean` applies that operation to every
retained `CXXMemberCallExpr` in a complete probe and emits an auditable JSON
admission/refusal census. It is bounded and read-only: no receiver, object
state, body execution, overload lookup or native agreement is inferred.
For argument refusals it also reports the retained child-kind shape, so a
future argument tier can be priced against source evidence before evaluation
semantics are added.
Receiver refusals likewise retain the member kind, arrow/dot spelling, value
category, and base child kinds for a future receiver tier.
The census preserves nested base trees and cast kinds, including
`UncheckedDerivedToBase(CXXThisExpr)` and `LValueToRValue(MemberExpr(...))`, so
`this` and derived-base work can be priced independently.
The census also groups the remaining generic refusals into disjoint families:
nested member bases and nested member-call bases.

On the 542-call TinyXML2 probe, the current census admits 66 calls. The 5
remaining generic receiver refusals are 4 nested member bases and 1 nested
member-call base. Their exact leading shapes are:

| family | retained receiver base |
| --- | --- |
| nested member (4) | `ImplicitCastExpr:LValueToRValue(MemberExpr(ImplicitCastExpr:LValueToRValue(DeclRefExpr)))` on an arrow call |
| member-call (1) | `CXXMemberCallExpr(MemberExpr(ImplicitCastExpr:UncheckedDerivedToBase(DeclRefExpr)))` on an arrow call |

The other 471 refusals in that run are 314 unsupported argument lists, 155
missing `this` owners, and 2 malformed names. This is source pricing only:
the census still performs no receiver conversion, object lookup, or call.

This is not overload resolution or a general method-call evaluator. Arguments,
temporaries, lvalue/rvalue receiver conversions, member pointers, virtual or
qualified dispatch, construction, writes and calls whose target body is not an
admitted getter remain refusals. No method is selected from a name, and the
receiver handle never manufactures an object or an ABI address.

Kernel controls cover successful arrow and direct-dot calls with result **7**, canonical resolution
and invocation through a noncanonical occurrence, missing or malformed call
children, argument refusal, non-arrow receivers, missing method handles, missing
receiver/result types, bad names, non-method targets, method/canonical/name/
receiver-handle mismatches, receiver-type mismatch and result-type mismatch.
The controls use the existing projection's exact object state; no native
differential claim is made by this source bridge. Native getter and
class-subobject batteries remain the separate oracle for the underlying
already-admitted body and object projection.
