# Integral member-read methods on existing objects

2026-10-20. N4950 [class.mfct.non.static], [expr.prim.this], [expr.ref],
[conv.lval] and [conv.integral] govern a nonstatic method that returns an
integral data member of its existing receiver. This tier executes that source
shape through a separate `IntegralMemberGetter` surface.

Admission requires a named, nondependent, nonstatic, nonvirtual method with no
parameters, attributes, exception specification, volatile or ref qualification.
Its exact retained compound body contains one value return: a direct field of
`this`, optionally parenthesized and converted between represented integral
types. Every expression type and conversion comes from the validated probe.
The selected field is named, direct, nonvolatile and non-bit-field, with no
attributes. Const methods add const access to non-mutable fields; mutable and
declared-const field rules retain their ordinary meaning.

Receiver records must be complete named nondependent non-unions without bases.
They may be nonaggregates and have constructors, destructors and unrelated
unsupported fields: invocation does not construct, destroy or inspect those
parts. Only `VisibilityAttr` is allowed on the receiver record; its exact AST
attribute census must agree with the getter metadata. Other attributes remain
loud. Record, method and field identities, context chains, owned body,
redeclarations and source flags are validated before lowering.
The instance declaration entry point discards only attached `FullComment`
metadata before checking parameter/body order (N4950 [lex.comment]); it does not
discard attributes or executable children. Ordinary/static callable admission
retains its existing source-child policy.

`IntegralMemberSnapshot` is an explicit caller-state projection: an existing
receiver-record ID, its selected member ID/declaration, receiver access constness
and an `IntegralObjectStore`. The caller supplies the member ownership relation,
as it supplies the initial object world. The interpreter checks distinct IDs,
record/member types, equal storage durations, initialized live objects, const
qualification, memory shape and value formats. It neither derives this relation
from ABI offsets nor manufactures a class constructor. The projection is not
an `IntegralRecordSchema` and cannot enter aggregate creation as a full schema.
The receiver record may itself be a base subobject. The separate
[class-subobject projection](cpp-class-subobjects.md) validates its enclosing
concrete complete root and every nonvirtual base occurrence; the member snapshot
alone supplies no enclosing hierarchy or dynamic complete-object type.

Invocation validates the receiver, reads the member and performs retained
integral conversions in source order. It returns the original memory alongside
the value. Nonconst methods cannot be invoked through const receivers. Missing,
stale, uninitialized, mismatched and malformed observations fail explicitly;
no dummy value stands for an unavailable member. Getter execution allocates,
writes and ends no object. Constructor/destructor execution, member writes,
calls, virtual dispatch, bases, general pointer expressions and whole-program
execution remain separate tiers.

Validation must include actual compiled getter ASTs, positive scalar/const/
mutable cases, type/identity/lifetime refusals and state preservation. Original
artifact acceptance uses the unchanged TinyXML2 `XMLNode::GetLineNum` and
`XMLAttribute::GetLineNum` bodies, exported from the complete pinned probe.
Kernel theorems must state successful execution on valid supplied member states.
Native differential controls must set/read the member independently of calling
the getter, compile the unchanged original implementation under strict C++23
at both optimization levels with UBSan, and never count a refusal as agreement.
Parsing, construction and destruction of the surrounding library are native
oracle setup, not claimed modeled executions.

The implemented controls use matching Clang/LLVM 21.1.8 in strict C++23 mode
on the pinned LP64 target with signed 8-bit `char`. They pass **104** fixture
rows across twelve integral types and **22** original-source rows at both
`-O0` and `-O2` under UBSan. Thirteen compiled source shapes and fourteen
altered method/record/field evidence cases refuse. Twenty-two kernel controls
cover live/const/mutable receivers, type/identity/storage/lifetime failures,
invalid memory/value observations and ordered boolean/narrowing conversions.
The generic preservation/success theorems and both generated-original
success theorems list only `propext`, `Classical.choice` and `Quot.sound`.

The complete pinned TinyXML2 probe (35,495,732 bytes, SHA-256
`54ea351d3ca79cb612f169df30d0eaef3bff14f49c0ffa968c3437e9a1a69c46`)
has 520 retained bodies and 472 explicit selected-source bodies. The getter
census admits exactly the two exported methods: **2 admitted / 470 refused**.
Ordinary/static admission remains byte-identical at **1 / 471**; the two
separate APIs therefore cover three distinct bodies. These are first-refusal
censuses, not complete wall sets. The previous complete record-schema census
remains **0 / 29**; this getter tier does not broaden aggregate admission.
The existing complete capture was reused after rechecking source/plugin hashes;
a fresh recapture attempt timed out. Other corpora retain their separately
measured input-size and strict-frontend barriers. This is neither completion
of a language rung nor three-corpus execution.
