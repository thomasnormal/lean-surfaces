# Nonvirtual class subobjects on existing receivers

2026-10-20. N4950 [class.derived], [class.abstract], [class.base.init],
[basic.life] and [expr.ref] distinguish a complete object from each of its
base subobjects. An abstract class can be a base subobject, even though it
cannot be the type of a complete object. Nonvirtual repeated bases have
distinct identities; neither class names nor byte offsets identify them.

This item admits source-backed class hierarchy descriptions and interprets
explicit projections of already existing objects. It does not execute
construction, destruction, base conversions in source expressions or virtual
dispatch. Virtual bases refuse: duplicating them would invent distinct objects
where C++ requires sharing. Unsupported/dependent class contexts and class
attributes other than visibility also remain loud.

The canonical probe must retain each complete class's abstractness and ordered
direct base specifiers through Clang getters: structured canonical type,
virtualness, effective/written access and source type spelling. Lean validates
these against the complete retained class source, context/redeclaration chains,
field census and all recursively reached class definitions. No base edge is
reconstructed by parsing a printed class name. A closed finite hierarchy has
unique class descriptions, coherent field ownership and no cycle or unused
description. Abstract descriptions are permitted internally, but a complete
root must be concrete.

Every base occurrence has an index path from the complete root. Expanding the
nonvirtual graph retains repeated occurrences in diamonds. Caller state supplies
one distinct object ID for every occurrence, including the complete root;
types, constness, initialized live phases, storage durations and absent scalar
payloads must agree. The projection supplies a selected receiver path and the
existing member snapshot. Its receiver ID must equal that path's object, the
field must belong to that class, and its member ID must differ from every class
object ID. Existing getter checks still enforce selected field type, access
qualification, value validity and source declaration identity.

Invocation returns the getter result and identical caller memory. A base view
does not allocate, copy, adjust an invented address, change dynamic type or
erase the complete root's lifetime. Access labels describe the hierarchy;
this state API does not authorize a source conversion that Clang would reject.
The supplied field ownership relation is explicit input, not a full class
value or a claim that unsupported members were constructed.

Acceptance requires compiled multiple-inheritance and nonvirtual-diamond
fixtures, abstract-base/concrete-root controls, const/mutable and stale/malformed
world refusals, source/evidence disagreement controls, and generic memory
preservation. Original-source validation must use actual TinyXML2 hierarchies
and unchanged getter bodies from the same complete probe. Native tests must
independently observe base/member identity and compile unchanged original
implementation at O0/O2 with UBSan. Proofs must include successful execution and
non-vacuity, not implications whose only successful case is absent.

## Measured acceptance

Strict matching Clang/LLVM 21.1.8 C++23 controls pass **55** fixture rows and
**22** original-source rows at O0/O2 under UBSan. Eight compiled source shapes
and eleven altered-evidence cases refuse. Twenty-five kernel controls cover
distinct diamond occurrences, const/mutable access, abstract complete roots,
malformed graphs/worlds, identity/type/storage/lifetime mismatches and selected
receiver paths. Generic preservation/success theorems and both original
hierarchy/getter theorems list only the standard Lean axioms.

The fresh complete TinyXML2 capture is **35,509,721 bytes**, SHA-256
`ce2b760fec4f5eae42bae76753a3d54a3611ecf792b1ed9af62455d55ce7f2c0`.
Source hashes remain unchanged. Of **72** complete class occurrences, **43**
are dependencies and **29** belong explicitly to the selected header/source.
Hierarchy admission is **15 admitted / 14 refused**: ten template scopes, two
implicit/dependent/module declarations and two abstract complete roots refuse
first. This counts class relationships, not construction or method execution.

Ordinary/static and member-getter body admissions remain **1/472** and
**2/472**, a disjoint union of three bodies. Every body path, ownership and
first-refusal result agrees with the preceding capture; canonical handles and
whole-report hashes change across captures. These are first refusals, not full
wall sets. The separate integral aggregate-schema census remains **0/29**;
hierarchy admission does not construct or initialize those records. The other
corpora retain their separately measured input-size and
strict-frontend barriers. This item completes neither a language rung nor
three-corpus execution.
