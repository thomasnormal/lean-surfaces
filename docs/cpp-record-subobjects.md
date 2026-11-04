# Integral record member subobjects

2026-10-20. N4950 [intro.object], [basic.life], [class.mem.general],
[dcl.init.aggr] and [dcl.stc] give a non-static data member its own object
identity, nested within a complete object whose storage duration it shares.
Ending the complete object's lifetime also ends its member lifetimes.

This layer admits named, complete, nondependent, non-union aggregates without
bases, attributes, user-declared destructors or nontrivial destruction. Every direct field must be a
named, nonvolatile integral object, with no bit-field, attribute or in-class
initializer. The probe records the record/field getters and complete field
order; admission joins them to retained AST occurrences and structured types.
Field identity is its declaration handle, rather than its spelling or offset.

`IntegralRecordStore` adds complete-record/member ownership to the existing
integral value store. Creation takes already evaluated, correctly typed values
for every field. It does not evaluate a C++ aggregate expression or a constructor.
Root objects and fields have distinct stable IDs. Member projection preserves
identity and allocates nothing. Distinct records never share a member ID.

An actual const complete object makes its non-mutable members actually const;
a const view of a mutable complete object only adds an access restriction.
`mutable` fields remain writable through either const receiver. A field's own
const qualification still applies. Returned integral member references work
with the existing callable reference-parameter API. Importing the resulting
memory back checks the complete ownership/lifetime invariant, preserves the
same target profile and requires existing record metadata to stay unchanged.
Only values and the callee's additional scalar cells may change at that boundary.
A declaration handle has one consistent schema throughout a record store.

Ending a record ends every member and clears its value; releasing dynamic
storage releases the complete object and every member. Stale integral aliases
therefore fail even through the ordinary integral API. Malformed ownership,
member types, object identities, lifetimes and value-store lengths refuse.

This is a state and member-access layer. Instance-method AST execution,
`this`, constructors, aggregate-expression lowering, default initialization,
record copies, arrays, bases, unions, layout, pointers and nontrivial destruction
remain separate obligations. Record-schema admission is not function execution
or a correctness theorem about an original corpus method.
