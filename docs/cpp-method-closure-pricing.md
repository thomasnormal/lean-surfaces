# Instance-method dependency closure pricing

2026-10-20. Before extending N4950 [class.mfct.non.static], [expr.ref] and
[expr.call], measure the original bodies that extension would need to execute.
The callable admission census reports its first refusal. This instrument reports
all observed walls under a named pricing contract; it never admits or executes
a function, and an empty wall set is not a correctness claim.

Input is a complete schema-0.3 canonical probe. Walk only retained `inner` AST
occurrences, preserving duplicate source sites and instantiations. Join methods,
receiver records, direct fields, structured types and selected call declarations
by handles and canonical identity. A selected declaration without a retained
body is an external target, never an implicit native contract. Missing or
conflicting evidence stays a wall. Call closure follows every retained target
body, propagates all reachable walls, and records recursion separately.

Record physical expansion/spelling origins select source ownership; both files
must belong to the supplied source set. Dependencies and implicit bodies remain
visible and separately counted. Reports retain occurrence paths and handles;
input/tool hashes, source hashes, frontend identity and process bounds accompany
the external launch receipt. No source is imported or executed to resolve a call.

The baseline is the current integral callable grammar and complete integral
aggregate record profile. Distinguish signature, scope/declaration, record shape,
field type/access, operator/cast, unsupported node, and call-target walls. Member
access inspects the selected field and base, not merely the presence of
`MemberExpr`. Method const/volatile, virtual/pure status and ref-qualification
come from explicit Clang getters, not parsing a printed function type.
Signature fragments retain result/parameter types independently because the
ordinary function-type projection deliberately omits cv/ref-qualified methods.
An unrepresented fragment remains distinct from an observed nonintegral type;
this additional supplement does not relax the Lean type parser.

The CLI seals this dated profile to SHA-256 hashes of `Callable.lean`,
`LocalFunction.lean`, `AutomaticDeclarations.lean` and `RecordEvidence.lean`.
Source drift refuses until the pricing contract is reviewed. Context-chain
costs cover templates, dependent/implicit/module scopes, unsupported contexts,
inline/anonymous namespaces and cycles. Ordinary unsequenced binary operands
with effects retain a separate cost; short-circuit and comma expressions do not.

Price these hypothetical changes separately: direct `this`/integral-member
execution on the current aggregate profile; integral-member projections on an
already-constructed nonaggregate receiver; and resolved direct calls with their
transitive body requirements. These are cost scenarios, not tiers or admission
predictions. In particular a receiver snapshot is not constructor execution,
unused unsupported fields are not modeled values, and removing a call wall does
not establish sequencing, argument binding, dispatch or termination.
The projection scenario removes whole-record construction/destruction and
unused-field type-evidence costs; used-field evidence, bases, bit-fields,
attributes and other record restrictions remain. Visibility is an additional
explicit scenario removing only `record:attribute:VisibilityAttr`.

Rank wall presence beside `sole` counts and full wall-set intersections. A wall
appearing in many methods may unlock none alone. Preserve direct and closure
sets separately so callers do not hide an unsupported callee. Controls must
include clean candidates, independent simultaneous walls, unresolved/external
calls, redeclarations, duplicate occurrences, recursion, const/mutable fields,
non-`this` receivers, missing/conflicting evidence and source/dependency splits.

This is an inventory under the stated contract, not a duplicate semantic
validator. Source/metadata ancestry and redeclaration coherence, exact expression
typing/promotions/arity/context, local binding and initialization, alias/lifetime
effects, call binding/dispatch and defined behavior still require Lean admission
and execution. Constructor initializer lists and implicit construction or
destruction are not recursively priced as calls; constructors/destructors retain
their declaration-family wall. The report lists these unpriced checks explicitly.

## Measured original artifact

Strict Clang/LLVM 21.1.8, C++23, TinyXML2 revision
`321ea883b7190d4e85cae5512a12e5eaa8f8731f`, header and implementation selected.
The fresh complete probe is **35,495,732 bytes**, SHA-256
`54ea351d3ca79cb612f169df30d0eaef3bff14f49c0ffa968c3437e9a1a69c46`.
Source hashes match the preceding capture. Every retained body path, handle,
kind, implicit flag and ownership classification independently agrees with the
Lean callable census: **520** bodies, **472** explicit selected-source bodies,
still **1 admitted / 471 refused**, and no first-refusal changes. Structured
declaration/expression type counts remain **2399 / 10082**. Record-schema
admission remains **0/29** selected-source complete records.

Of the selected bodies, **384** are nonstatic `CXXMethodDecl` occurrences:
**159 const / 225 nonconst**. The first-error census's **361** instance-method
refusals misses 23 methods blocked earlier. Constructors, destructors and
conversion declarations stay separate families; no body is deduplicated.

| Hypothetical cost removals | Direct sets clear | Closure sets clear |
| --- | ---: | ---: |
| None | 0 | 0 |
| `this` and members on current aggregate profile | 0 | 0 |
| Integral projection of existing receiver | 0 | 0 |
| Projection plus visibility attribute | 2 | 2 |
| Projection, visibility and resolved direct calls | 2 | 2 |

The two clear observed sets belong to `XMLNode::GetLineNum` at occurrence path
`[122,15,24]` and `XMLAttribute::GetLineNum` at `[122,20,7]`. Both read an integral
field through a const receiver. They require an existing-object projection that
does not construct their nonaggregate, nontrivially destructible classes, plus
an explicit visibility-attribute policy. They are **not admitted or executed**
by this instrument. Seven additional closure sets have bases as their sole
remaining observed wall after projection/visibility; other semantic checks above
still apply.

**267/384** methods contain calls; **256** reach retained target bodies and **12**
reach recursion. Baseline closure presence includes nonintegral member accesses
**311**, direct calls **263**, and external retained-body gaps **229**, each with
**zero sole** baseline cost. These closure counts can include a callee's walls
even when the caller lacks that construct. Removing direct calls alone adds no
clear set. The nearest measured next step is existing-receiver projection with
a precise source/evidence policy.

The final report is **3,765,068 bytes**, SHA-256
`b0e28f39e90f36e1a2a956975e460dc6b4dbc499ce14ce02687f1537171b8958`;
pricing took **2.670 seconds**, peak child RSS **171,008 KiB**, under a
**17179869184-byte** address-space limit. Controls pass **25/25**, including
compiled positive and negative methods; canonical getter controls pass **54/54**.
No new original-method theorem, semantic coverage, rung completion or
three-corpus execution is claimed. The other corpora retain their separately
measured input-size and strict-frontend barriers.
