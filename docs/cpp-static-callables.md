# C++ static member function execution

The next callable extension follows N4950 §11.4.9 `[class.static]`,
§11.4.9.1 `[class.static.mfct]` and §9.3.4.6 `[dcl.fct]`.
A static member function has no `this` parameter. Executing an already-selected
static integral body therefore uses the ordinary integral callable frame;
record identity establishes its scope, without allocating an instance.
Void results use the [void callable result API](cpp-void-callables.md),
including bare returns and normal fallthrough.

Admission requires an exact `CXXMethodDecl`, a witnessed
`CXXMethodDecl.isStatic()` result, ordinary nondependent named record/namespace
contexts and the existing definition/body/type/effect checks. Canonical
redeclaration evidence must reach a retained static declaration. Instance,
virtual, constructor/destructor/conversion, template, dependent and module
methods stay loud. This does not add member-call syntax or overload resolution:
the input selects a declaration occurrence already resolved by Clang.

Nonvolatile const integral value parameters keep their const object/access
view, while lvalue-to-rvalue conversion supplies the unqualified value.
Existing-object integral lvalue-reference parameters use the
[shared caller store](cpp-reference-parameters.md). Temporary/rvalue bindings,
pointers, volatile types and unsupported expressions keep their existing
boundaries. In particular no unknown call is replaced by a library
name or a guessed value.

The real-artifact obligation is TinyXML-2 10.0.0's unchanged
`XMLUtil::IsUTF8Continuation(const char)`. Validate its complete original probe,
export its admitted typed body as a Lean literal, compare every 8-bit char input
against calls to the original declaration at `-O0`/`-O2` under UBSan, and
kernel-check the complete input domain. Generated literals must record the
source revision/hash and full probe hash; a handwritten twin is not evidence.
The typed export is part of the trusted source-to-AST/lowering boundary, and
the kernel theorem concerns the exported artifact. Neither native differential
agreement nor this one helper completes a C++ rung or class semantics.

## Executed original artifact

The unchanged TinyXML-2 helper admits from a complete **34,887,480-byte**
probe (SHA-256 `e8859af93e6c79994d80d09551ec694795132815d80639bf4981ba2527c74233`).
The generic exporter validates the whole declaration/type/binary/expression
boundary before selecting an occurrence and prints the admitted `CallableFunction`
as a Lean source literal. It refuses an unrelated malformed binary row rather
than accepting a selected body from a partially validated probe. Input bytes
are bounded before reading, UTF-8 is strict, and failure emits no literal.

The generated literal and provenance are in
[`Examples/cpp/tinyxml2`](../Examples/cpp/tinyxml2/README.md). The total
`returns_high_bit` theorem covers every valid signed 8-bit char and states an
actual successful boolean result. The finite kernel check uses `decide`, with
only `propext`; the pointwise arithmetic proof additionally uses the standard
Lean axioms `Classical.choice` and `Quot.sound`. No native decision axiom or new
axiom declaration is introduced. Clang/probe correspondence, the metadata
validators, lowering and representation printer remain the trusted boundary;
the theorem does not authenticate a compiler invocation or prove its lowering
correct. Native calls to the original header match both evaluators on all
**256** inputs at `-O0`/`-O2` under UBSan, including object-frame cleanup.

The source change also required the general nonvolatile const-source arithmetic
rule: source qualifiers are removed before promotion, while converted operand
and result types remain strict builtin types. Volatile sources and qualified
converted/results stay loud. The static/const control battery has **85** native
rows, **80** also checked with the value-only evaluator, six compiled refusals
and seven derived-evidence refusals.

Selecting **both** original implementation and header yields **472 explicit
source body occurrences**, with **one admitted / 471 refused**. The report
retains 520 bodies in total: 481 selected-source occurrences (including nine
implicit bodies), and 39 dependency occurrences. The implementation-only
source denominator remains 202 bodies with zero admitted; the newly admitted
body is in the header. First refusals remain diagnostics rather than full
semantic wall sets. The larger JSON input and systems header retain their
separate previously measured resource/frontend boundaries; this is no new
three-corpus execution claim, completed class tier or completed rung.
