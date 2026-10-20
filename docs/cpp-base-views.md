# Nonvirtual base views on existing objects

2026-10-21. N4950 [class.derived], [class.access.base] and [expr.static.cast]
distinguish an existing complete object from each nonvirtual base-subobject
occurrence. A repeated base in a nonvirtual diamond has a different identity on
each path. A virtual base requires shared-subobject rules and is outside this
slice.

`ClassBaseView` is an explicit state projection. The caller supplies the closed
class hierarchy, one object ID for every expanded occurrence, a source path and
a target path. The source path must be a strict prefix of the target path, so a
view can move from a complete object to a base or from a base occurrence to one
of its bases. Every object is checked against the concrete root's declaration,
constness, storage duration, live initialized phase and empty scalar payload.
The target result is the existing object ID at the selected path and the exact
same `IntegralObjectStore`.

Each admitted base edge retains both Clang's effective access and the source's
written access spelling. With no context, the view policy admits only paths
whose traversed effective edges are `public`; a protected or private edge
returns `inaccessibleBase`. An optional declaring-class context admits a
protected edge when that context is the declaring class or a derived class,
and a private edge only in its declaring class. This is the narrow source-backed
context rule; friend lookup, access through unrelated contexts and full
source-level cast lookup remain loud. The written label remains provenance data.

Complete class descriptions also retain canonical friend handles from
class-type and direct function or method `FriendDecl`s. A listed friend can
supply the access context for a protected or private edge. The function form
requires one direct declaration (or a direct reference) whose occurrence maps
to one canonical probe handle; missing and ambiguous targets refuse. The
handle only authorizes this existing-object access policy. Friend-function
execution, overload lookup and general access-control search remain loud.

This operation does not parse or execute a C++ cast expression. It does not
infer ABI offsets, allocate a pointer, resolve a virtual base, search for a
unique target by class name, or perform virtual dispatch. Its explicit context
check is a state policy, not a source cast-expression evaluator.
The explicit path is the identity witness; repeated occurrences therefore stay
distinct and ambiguous name-only conversions are never silently guessed.

`ClassBaseCast.execute` is the typed source/target boundary over that witness:
it checks that both supplied declarations are exactly the declarations at the
selected paths before returning the existing target identity. This executes a
resolved nonvirtual cast in the state model; it does not parse an AST cast or
infer a path from class names.

`ClassBaseCastSyntax.admit` is the deliberately narrow source-backed AST gate
for this operation. It accepts only a `CXXStaticCastExpr` with `castKind:
NoOp`, whose single child is an `ImplicitCastExpr` with
`castKind: DerivedToBase` and a nonempty base path, followed by one
`LValueToRValue` child and a direct `DeclRefExpr` operand. The outer and inner
qualified pointer spellings must agree with the supplied source and target
spellings, and the operand must carry a valid frontend `referencedDecl` handle.
Reverse `BaseToDerived` casts, member or computed operands, missing handles or
paths and all other cast forms remain explicit refusals. `bind` attaches this
validated syntax evidence in an already-resolved `ClassBaseCast`; declaration
handles and path witnesses still come from the typed state boundary, and
execution continues to use those typed witnesses rather than spelling alone.

The kernel controls cover complete-root and nested-base views, const roots,
diamond identity, prefix failures, same-subobject and missing-path refusals,
duplicate IDs, malformed value stores, non-public-edge refusals, and permitted
or unrelated protected/private contexts. The generic theorem proves that a
successful view preserves caller memory. Native
class-subobject controls already
compile and observe the same concrete-root/base identities at O0/O2 with UBSan;
they remain the differential oracle for pointer identity while this state API
keeps source conversion outside its trust boundary.
