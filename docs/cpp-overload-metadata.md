# C++ overload and operator metadata

The rung-8 boundary retains Clang's selected overload identity without
performing overload resolution in Lean. `admitResolvedCXXOperatorCallExpression`
requires a `CXXOperatorCallExpr` at the supplied AST path, follows its direct
callee through one-child `ImplicitCastExpr` wrappers, and returns the retained
`FunctionDecl` or `CXXMethodDecl` handle from the callee's `referencedDecl`.

The operation does not use the operator's printed name to select a declaration,
does not infer conversions, and does not execute the selected body. Missing or
non-callable handles refuse. The existing kind-only metadata gate remains for
grammar census rows; this handle-producing gate is the source-shaped identity
boundary for later overload work.

The same handle contract is available for ordinary `CallExpr` nodes through
`admitResolvedCallExpression`; direct function and method references retain
their Clang declaration identity while name lookup and invocation remain loud.

`admitResolvedCXXConstructExpression` applies the same contract to
`CXXConstructExpr` only when the AST carries a selected
`CXXConstructorDecl` handle in its structured `ctor` field. The pinned Clang
21.1.8 JSON for an ordinary `S value(1)` construction carries `ctorType` but
no `ctor` handle, so that source shape is recorded as a loud refusal rather
than treating the type spelling as overload identity. Construction,
conversion, and lifetime execution remain outside this metadata gate.

A structured `ctor` object missing its declaration `id` is separately refused;
constructor identity requires a complete frontend handle, not just a
constructor kind tag.

A structured `ctor` object whose `id` is numeric is also refused; artifact
handles retain Clang's string identity and are never coerced from numbers.

A structured `ctor` object whose declared kind disagrees with the retained
constructor declaration is also refused; both pieces of frontend evidence must
agree.

A structured `ctor` object that omits `kind` is also refused; constructor
metadata does not infer a missing evidence field from the declaration table.

A structured constructor handle with malformed string `id` is also refused;
the artifact-local handle parser validates object and string forms uniformly.

A string-valued `ctor` field with malformed frontend-handle syntax is also a
recorded refusal; constructor handles must use the artifact-local format.

A string-valued constructor handle resolving to a retained non-constructor
declaration is also refused; string handles receive the same declaration-kind
check as structured handles.

A string constructor handle occurring in multiple retained declaration rows is
also refused; string handles do not bypass the ambiguity check.

A `ctor` handle whose declaration row has a non-constructor kind is also a
recorded refusal; constructor identity does not trust the handle alone.

A scalar-valued `ctor` field is also a recorded refusal; selected constructor
evidence must be an object or a valid handle string.

A syntactically valid constructor handle absent from the artifact declaration
table is also a recorded refusal; the handle must resolve to retained evidence.

If the same constructor handle occurs in more than one retained declaration
row, the metadata gate refuses because the artifact does not identify one
declaration occurrence unambiguously.

The positive kernel witness and differential row use a structured `ctor`
object with a retained `CXXConstructorDecl` handle. They demonstrate the
accepted evidence shape without claiming that constructor overload resolution
or object construction has been executed.

A positive witness also covers Clang's artifact-local string handle form. The
string is parsed as a handle and checked against the retained declaration row;
it is never treated as a constructor name for lookup.

Ordinary `CallExpr` identity has the corresponding negative control: a
retained declaration handle whose structured kind is `VarDecl` is refused even
when the separate native source witness is well-formed. The gate never turns a
non-callable declaration into a callable by name.

The positive ordinary-call corpus also covers the one-child implicit-cast path,
confirming that the retained function handle survives the frontend wrapper
without string lookup or conversion inference.

The cast path also validates structured declaration kind recursively; a
contradictory kind below a one-child `ImplicitCastExpr` is a recorded refusal.

A positive ordinary-call witness also retains a `CXXMethodDecl` handle, covering
the method branch without executing the receiver or method body.

A string ordinary-call handle resolving to a retained non-callable declaration
is a recorded refusal; string handles cannot bypass the call kind check.

A syntactically valid string ordinary-call handle absent from declaration
evidence is also refused; the string must resolve to one retained declaration.

A string ordinary-call handle occurring in multiple retained declaration rows is
also refused; string handles do not bypass the ambiguity check.

A syntactically valid string operator handle absent from declaration evidence is
also refused; operator identity requires one retained declaration row.

A structured operator `referencedDecl` object missing `id` is also refused; the
operator gate requires a complete retained frontend handle.

A string operator handle occurring in multiple retained declaration rows is also
refused; string handles do not bypass the ambiguity check.

A positive ordinary-call witness also covers the artifact-local string
`referencedDecl` form. The string is parsed as a handle and matched against one
retained declaration row; it is not used for name lookup.

A malformed string `referencedDecl` handle is a recorded refusal; call metadata
does not normalize arbitrary text into an artifact identity.

A parenthesized ordinary-call callee is retained through Clang's
`ImplicitCastExpr` and one-child `ParenExpr` wrappers. The gate follows those
source AST nodes to the same `FunctionDecl` handle; it does not strip the
parentheses by reparsing source text.

A parenthesis wrapper with more than one child is refused; the metadata gate
never chooses one child from a malformed frontend node.

An empty parenthesis wrapper is also refused; the call gate does not manufacture
a selected declaration when the frontend supplies no child.

A null-valued ordinary-call `referencedDecl` is also refused; declaration
identity requires object or string handle evidence.

A non-object, non-string ordinary-call `referencedDecl` array is also refused;
declaration identity is never reconstructed from an arbitrary JSON container.

A Boolean-valued ordinary-call `referencedDecl` is also refused; declaration
identity is never coerced from scalar data.

A structured ordinary-call `referencedDecl` object missing `id` is also refused;
the call gate requires a complete retained handle.

A structured ordinary-call handle with malformed string `id` is also refused;
the artifact-local handle parser validates object and string forms uniformly.

A structured ordinary-call handle whose `id` is Boolean is also refused; the
artifact-local identity remains string-typed and is never scalar-coerced.

A structured ordinary-call handle whose `id` is null is also refused; a
frontend handle must carry a string identity.

A structured ordinary-call handle whose `id` is an array is also refused; a
frontend handle must carry a string identity.

A structured ordinary-call handle whose `id` is an object is also refused; a
frontend handle must carry a string identity.

A structured ordinary-call declaration evidence whose `kind` is scalar is also
refused; declaration kind evidence must be frontend text.

A structured ordinary-call declaration evidence whose `kind` is Boolean is also
refused; declaration kind evidence must be frontend text.

A scalar ordinary-call `referencedDecl` value is also refused; declaration
identity is never coerced from a number or Boolean.

A positive overloaded-operator witness covers the same artifact-local string
`referencedDecl` form. Operator metadata parses and validates the handle without
using the printed operator name.

A parenthesized overloaded-operator callee is also followed through its
one-child `ParenExpr` wrapper. The selected `FunctionDecl` identity remains the
structured frontend handle.

A parenthesis wrapper with more than one child is refused; operator metadata
never chooses one child from malformed frontend data.

An empty parenthesis wrapper is also refused; the gate does not manufacture a
selected declaration when the frontend supplies no child.

A null-valued overloaded-operator `referencedDecl` is also refused; operator
identity requires object or string handle evidence.

A non-object, non-string overloaded-operator `referencedDecl` array is also
refused; operator identity is never reconstructed from an arbitrary JSON
container.

A structured overloaded-operator handle whose `id` is Boolean is also refused;
the artifact-local identity remains string-typed and is never scalar-coerced.

A malformed string operator handle is a recorded refusal; operator metadata does
not normalize arbitrary text into an artifact identity.

A second positive witness combines that string form with a retained
`CXXMethodDecl`, covering method identity without executing the operator body.

The cast path also validates structured operator declaration kind recursively; a
contradictory kind below a one-child `ImplicitCastExpr` is a recorded refusal.

A string operator handle resolving to a retained non-callable declaration is a
recorded refusal; string handles cannot bypass the callable-kind check.

A malformed cast wrapper with two children is a recorded refusal; the gate
requires the exact one-child frontend shape and does not choose one child by
position.

An empty `CallExpr` child list is likewise a recorded refusal; a selected
callee cannot be manufactured when the frontend supplies no callee occurrence.

A callee handle absent from the artifact declaration table is also a recorded
refusal; retained AST identity must be backed by corresponding declaration
evidence.

An ordinary call handle duplicated in declaration evidence is also refused;
the call gate requires one unambiguous retained function or method row.

An ordinary call whose structured `referencedDecl.id` is numeric is also
refused; declaration identity remains the artifact's string-typed handle.

An ordinary call whose structured `referencedDecl.kind` contradicts the
retained function or method declaration is also refused; the two evidence
records must agree.

An ordinary call whose structured `referencedDecl` omits `kind` is also
refused; the call gate does not infer a missing evidence field from the
declaration table.

An empty overloaded-operator child list is also a recorded refusal; the
operator gate does not manufacture a selected callee.

A multi-child implicit-cast wrapper around an operator callee is likewise a
recorded refusal; the gate requires one unambiguous child.

An operator callee with an unexpected AST node kind is also a recorded refusal;
the gate accepts only declaration references or the supported one-child cast.

The overloaded-operator gate has the matching negative control: a retained
operator callee whose declaration kind is `VarDecl` is refused before any
operator identity can be accepted.

An operator callee handle absent from the artifact declaration table is also a
recorded refusal; overload metadata requires retained declaration evidence.

An overloaded-operator handle duplicated in declaration evidence is also
refused; operator identity requires one unambiguous retained function or method
row.

An overloaded-operator call whose structured `referencedDecl.id` is numeric is
also refused; operator identity remains the artifact's string-typed handle.

A structured overloaded-operator `referencedDecl` whose value is a scalar is
also refused; operator identity is never coerced from a number or Boolean.

A structured overloaded-operator handle whose `id` is null is also refused; a
frontend handle must carry a string identity.

A structured overloaded-operator handle whose `id` is an array is also refused;
a frontend handle must carry a string identity.

A structured overloaded-operator handle whose `id` is an object is also refused;
a frontend handle must carry a string identity.

A structured overloaded-operator declaration evidence whose `kind` is scalar is
also refused; declaration kind evidence must be frontend text.

A structured overloaded-operator declaration evidence whose `kind` is Boolean
is also refused; declaration kind evidence must be frontend text.

A structured operator handle with malformed string `id` is also refused; the
artifact-local handle parser validates object and string forms uniformly.

An overloaded-operator call whose structured `referencedDecl.kind` contradicts
the retained function or method declaration is also refused; both evidence
records must agree.

An overloaded-operator call whose structured `referencedDecl` omits `kind` is
also refused; operator metadata does not infer a missing evidence field from
the declaration table.
