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
guessed from a raw call fragment. A pointer-valued data-member receiver is now
retained when its outer `LValueToRValue` and inner `MemberExpr` are explicitly
typed, arrow-based, and backed by a `FieldDecl` handle. The evidence keeps the
field handle, its base declaration handle, field spelling, and conversion chain.
It remains provenance only: binding and invocation still require an independently
supplied projection for the resulting receiver, and no member offset or pointer
value is inferred.
Callers that start from raw AST are expected to use `admitResolved`, which
performs both syntax admission and this canonical resolution in one operation.
`extractors/cpp/census_member_calls.lean` applies that operation to every
retained `CXXMemberCallExpr` in a complete probe and emits an auditable JSON
admission/refusal census. It is bounded and read-only: no receiver, object
state, body execution, overload lookup or native agreement is inferred.
For argument refusals it reports both the retained child-kind shape and the
recursive child tree, so a future argument tier can be priced against source
evidence before evaluation semantics are added. The recursive tree preserves
conversion kinds such as `IntegralCast` and `NullToPointer`; a top-level kind
alone would merge those into one unsupported bucket.
Receiver refusals likewise retain the member kind, arrow/dot spelling, value
category, and base child kinds for a future receiver tier.
The census preserves nested base trees and cast kinds, including
`UncheckedDerivedToBase(CXXThisExpr)` and `LValueToRValue(MemberExpr(...))`, so
`this` and derived-base work can be priced independently.
The census also groups the remaining generic refusals into disjoint families:
nested member-call bases.

On the 542-call TinyXML2 probe, the current census admits 70 calls. The 1
remaining generic receiver refusal is a nested member-call base. The four newly
admitted member-field bases have the exact leading shape
`ImplicitCastExpr:LValueToRValue(MemberExpr(ImplicitCastExpr:LValueToRValue(DeclRefExpr)))`
on an arrow call. The remaining generic shape is:

| family | retained receiver base |
| --- | --- |
| member-call (1) | `CXXMemberCallExpr(MemberExpr(ImplicitCastExpr:UncheckedDerivedToBase(DeclRefExpr)))` on an arrow call |

The other 472 refusals in that run are 314 unsupported argument lists, 155
missing `this` owners, and 2 malformed names. This is source pricing only:
the census still performs no receiver conversion, object lookup, or call.
The kernel battery includes a matching nested-call witness and checks that it
refuses as `unsupportedReceiver`; admitting it would require a typed result
object, a second call's body and state/effect sequencing, so it is priced as a
separate call-chain tier.

The argument census gives the next narrow candidate a concrete price. Twelve
refused calls pass a direct `IntegerLiteral` (`int`) as their only argument;
two more use the distinct tree `ImplicitCastExpr:IntegralCast(IntegerLiteral)`.
The direct literals are all the value `0` in the pinned source. They are still
refused: the current member-call bridge has no method-parameter evidence and
its invocation path is the zero-argument integral getter. A future integer
argument tier must retain the literal occurrence, source type, converted type,
and the selected method's parameter declaration before it can evaluate a call;
it must not treat a literal's presence as proof of overload selection or
conversion safety.

`IntegralMemberIntegerArgument.admit` now captures that direct slice as typed
evidence: the artifact-local literal handle, source spelling (`int`), normalized
`CppTypeEvidence.builtin .int`, and nonnegative value. Its separate `bind`
operation requires an explicit parameter handle and independently supplied
exact-`int` parameter type. It performs no lookup, overload resolution,
conversion, object mutation, or execution; wrappers and other literal types
remain loud. This keeps the parameter-binding boundary visible while the
zero-argument getter remains the only executable member-call path.

`IntegralMemberIntegerArgument.parameter` closes the remaining evidence gap for
this slice. Given a canonical `CXXMethodDecl` handle and ordinal, it requires a
self-canonical method metadata row, a matching structured parameter-type list,
and the corresponding `ParmVarDecl` child in the retained AST. It returns the
parameter handle, ordinal, name, source spelling, and normalized type.
`bindTo` accepts only matching argument/parameter evidence. Missing, repeated,
misordered, or non-`int` parameter witnesses refuse; no parameter is inferred
from a method name or from the argument's position alone.

The census applies this witness to the real probe as a pricing check. All 12
direct `int` literal arguments bind to a retained parameter (`Set` once at
ordinal 2 and `SetError` eleven times at ordinal 1). The stricter canonical
method profile passes for `Set` once and refuses the 11 `SetError` rows: its
canonical declaration is declaration-only and variadic, while the defining
occurrence is also variadic. This is a deliberate loud boundary rather than a
fallback to a redeclaration's body. The callable census additionally classifies
that defining `SetError` body as an instance method requiring object semantics,
with `CXXConstructExpr`, allocation/deletion, member calls, and control flow in
its body. Successful argument bindings therefore do not count as runtime
admissions; they identify both the canonical-signature wall and the next
object-backed method-body tier precisely.

The same census walks every retained member-call occurrence whose selected
method metadata has an enumeration result type, including calls that still
refuse on arguments or receivers. The pinned TinyXML2 artifact contains **43**
such calls: `XMLError` **38**, `ElementClosingType` **3**, and `Whitespace` **2**.
Their raw result spellings agree with the witnessed enum names in all 43 cases;
unknown or inconsistent method-result metadata remains a named census refusal.
This is real-artifact source telemetry, not a native execution or differential
claim: the calls still require their own object, argument, and enum-value
admission before execution.

`IntegralMemberMethodBody.admit` then resolves the body relation independently
of the profile. The real census finds exactly one definition for each involved
canonical method: `Set → Set` once and `SetError →` its distinct defining
occurrence eleven times. Duplicate identical rows are accepted, while a second
defining handle or conflicting body ownership refuses. This relation is still
provenance only; selecting a body does not execute it or waive the variadic and
object-semantics walls above.

The next object-state price is now measured by a source-order body walk. The
first object event is `member-call` for `Set` and
`this-member:_errorID` for all 11 `SetError` definitions. Thus `SetError`
requires a live receiver and a readable `_errorID` subobject before its first
statement can be evaluated; this is an object-frame precondition, not a
default value. The walk is telemetry only and does not lower member offsets,
constructors, allocation, or destruction.

`IntegralMemberThisFieldAccess.admit` turns that first direct receiver access
into a typed precondition: it checks the defining method's parent, the field's
`FieldDecl` handle and parent, arrow/lvalue category, receiver spelling, and
field spelling. The probe admits `_errorID:XMLError:XMLError` for all 11
`SetError` bodies. The one `Set` body has no direct `this->field` witness and
refuses this narrower precondition, as expected from its first `member-call`
event.

`IntegralMemberEnumProfile.admit` follows the field's structured type evidence
to its enum declaration and retains the enum handle, constant count, explicit
value count, and any fixed-underlying-type spelling. The probe reports
`XMLError:20:1:<absent>` for all 11 `SetError` accesses: one explicit zero and
19 implicitly sequenced constants, with no fixed underlying type retained.
Reading the field therefore still needs an enum representation decision; the
profile refuses to manufacture an `int` layout from the spelling alone.

`IntegralMemberEnumRepresentation.withOracle` makes that decision explicit at
the caller boundary. The census currently supplies `.unsignedInt` as a
pricing oracle for this probe; this is harness input, not a representation fact
recovered from Clang. A retained fixed-underlying spelling must agree with the
oracle, and `bool` is rejected as outside this integral field tier. Unknown or
unsupported representations therefore remain loud instead of acquiring a
guessed ABI layout.

`IntegralMemberEnumValue.evaluate` is the corresponding state boundary. It
requires the field handle from the typed access witness, a valid target
profile, and a caller-supplied stored `IntegralValue` whose format exactly
matches the chosen underlying type. It preserves the enum representation tag;
it does not convert the value to an unrelated builtin, read an offset, or
derive a value from the enumerator list. A field mismatch, invalid target,
format mismatch, or invalid stored value refuses.

`IntegralMemberEnumValue.read` composes this value check with the existing
`ClassReceiverProjection.invoke` path. The projection remains the sole source
of object identity, member ownership, lifetime, and stored-cell validation; the
enum layer supplies only the field witness and representation oracle. A stale,
wrong-owner, malformed, or otherwise unbound snapshot therefore refuses at the
projection/getter boundary rather than producing an enum result.

`IntegralMemberEnumCall` exposes that read as a call result without widening
the ordinary integral getter. It requires the already selected method and
receiver handles, the typed field witness, the oracle-backed enum profile, and
an existing projection. The retained result spelling must be the enum name (or
its `enum`/qualified spelling); an ordinary builtin result, mismatched method,
receiver, or result type refuses. Invocation then delegates to
`IntegralMemberEnumValue.read`, so the object-state and storage checks are
unchanged.

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
