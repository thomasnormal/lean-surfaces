# Two-state declarations: the retained boundary

IEEE 1800's two-state conversion is already part of the legacy value tier for
scalar and packed integral variables. `bit`, `byte`, `shortint`, `int`, and
`longint` declarations carry their state count into `Decl.twoState`; startup
uses zero, and assigning a four-state value maps every `x`/`z` bit to zero
through the existing `Squash2` expression. One-dimensional packed vectors and
untagged packed structs and unions use the same fixed-vector representation.
The extractor and focused tests cover both declarations and selected reads and
writes, including signed forms.

The current `VariableSymbol:2state` census tag names the shapes outside that
value tier. The 2026-10-23 corpus snapshot has 3,989 files containing the tag;
it is the sole refusal in 8 files. The previous snapshot had 4,132 files and
9 sole refusals. Its current frequent companions are assignment targets
(3,913 files), statement calls (3,784), expression calls (3,290),
`NamedValueExpression:2state` (1,481), classes (1,327), member access (1,023),
real literals (705), and element-select source types (591). The remaining
sole-tag examples include
dynamic and queue arrays, events, real and string variables, handles, and
other declaration forms with no common bit-vector meaning.

Bounded fixed-size unpacked arrays with two or more dimensions are now an
explicit exception. Ingestion expands the finite Cartesian product into
independent vector cells, preserving ordinary two-state zero startup and
x/z-to-zero assignment conversion. Exact positional and recursively replicated
assignment patterns are flattened into those cells in declared range order;
the `fixed_array_pattern_2state` fixture exercises nested replication. Dynamic
or nonconstant selections, effectful or shape-mismatched patterns, and every
nonintegral leaf remain loud. A multidimensional packed integral leaf is kept
as one vector cell, preserving packed bit order; the
`fixed_array_packed_leaf_2state` fixture exercises that form.

The same flattening applies to an untagged unpacked struct tree whose leaves
are integral scalars or packed fields: each leaf is an independent vector cell,
so field reads, writes, and compound assignments preserve the scalar two-state
rules. Nested member paths are part of the cell name (`value.inner.flag`).
Whole-struct values, nonintegral fields, arrays, tagged structs, and struct
initializers remain outside the representation. Complete positional and
keyed/default assignment patterns are lowered field by field for the admitted
non-nested shape, using the same width conversion and `Squash2` boundary;
partial or effectful patterns remain loud. The
`unpacked_struct_integral_fields` and `unpacked_struct_initializers` fixtures
exercise the direct field-level forms.

Finite unpacked-array declaration concatenations receive the same cellwise
treatment when every operand is a pure constant array, exact typed pattern, or
integral scalar. The `unpacked_concat_initializer` fixture covers this
composition; runtime array sources and self-aliasing remain outside the
representation.

Fixed unpacked arrays of untagged unpacked integral struct trees are also
flattened by position and field. A declaration such as `item values[0:1]`
produces cells `values[0].bits`, `values[0].meta.count`, and so on; direct
constant member access retains the existing field semantics. Aggregate array
initializers, nonintegral fields, and dynamic selections remain loud. The
`unpacked_struct_array` fixture covers this leaf composition.

A module-scope named `event` declaration is admitted as inert metadata on the
time-zero self-check path when no event operation uses it. It is omitted from
the flat vector state; waits, triggers, and event-driven processes remain
unsupported because they require the scheduler's event object and queue.
`event_decl` exercises this declaration-only slice.

A module-scope `real` or `shortreal` declaration is likewise admitted as inert
metadata when no procedural operation uses it. It is omitted from the flat
vector state; floating-point reads, writes, arithmetic, and formatting remain
unsupported because the representation has no floating-point value. The
`real_decl` fixture covers this declaration-only slice.

Module-scope and declaration-only local `chandle` variables are likewise
admitted as inert metadata. They are omitted from the flat vector state;
handle reads, writes, and cross-type assignments remain unsupported because
the representation has no handle value. The `chandle_decl` fixture covers
both scopes.

A module-scope virtual-interface variable initialized to `null` is also
admitted as inert metadata. It is omitted from the flat vector state;
non-null interface handles and all interface operations remain unsupported
because the representation has no interface object. The
`virtual_interface_decl` fixture covers this declaration-only slice.

Module-scope and declaration-only local `string` variables are likewise
admitted as inert metadata. They are omitted from the flat vector state;
string reads, writes, concatenation, and formatting remain unsupported because
the representation has no string value. The `string_decl` fixture covers both
scopes.

Complete assignment patterns for unpacked struct trees now flatten recursively
into leaf cells. Positional, keyed, and default values preserve each leaf's
width and two-state squash; partial, effectful, nonintegral, and aggregate
array forms remain unsupported. The `nested_struct_initializers` fixture
covers this initializer slice.

Large one-dimensional fixed unpacked arrays use a sparse exception to the
ordinary 1024-cell expansion bound. If the array's integral cells are observed
only through constant indices, ingestion emits one vector declaration per
observed index and preserves the existing two-state startup and x/z squash
rules. A dynamic index, whole-array read or write, aggregate initializer, or
nonintegral leaf remains unsupported because the flat state has no compact
array object. `large_fixed_array` exercises the two endpoint cells of the
IEEE-required 2^24-element extent.

Declaration-only `string` variables may also carry a pure string-literal
initializer when no operation observes the value. Ingestion omits that opaque
value from the flat state; nonliteral initializers and all string reads or
writes remain unsupported. `string_literal_decl` exercises module and local
forms.

Procedural `real` and `shortreal` declarations may likewise carry a pure
literal initializer when the value is not represented in the flat state. The
declaration is omitted just like an uninitialized floating declaration;
effectful initializers and every floating-point read or operation remain
unsupported. `literal_real_decl` covers positive and negative real literals.

An unchanged pure string literal also exposes its exact `.len()` as an
integral scalar. The extractor lowers that query to a literal while retaining
the opaque string boundary; writes, dynamic initializers, non-ASCII contents,
and every other string method remain unsupported. `literal_string_len` covers
both a nonempty and an empty literal.

An unchanged pure ASCII string literal also exposes `.getc(index)` as an
integral byte fact. The extractor lowers an in-range literal index to its ASCII
byte and follows IEEE's zero result for negative or out-of-range indices.
Dynamic indices, writes, dynamic initializers, non-ASCII strings, and other
string methods remain unsupported because no mutable string representation is
present in the self-check state. `literal_string_getc` exercises these bounds.

The public representation has no aggregate heap, queue, object, string, real,
handle, or event scheduler. The symbolic `PDecl`/`PType` representation also
does not carry a two-state bit, and symbolic `Squash2` is intentionally loud.
Adding a boolean to the declaration record would therefore accept programs
whose storage and operations still have no semantics, or would silently erase
an event/object boundary. The tier keeps those declarations and every use that
depends on them as `Unsupported`; the scalar/packed behavior and the bounded
fixed-array cell slice above are the complete admitted forms for this census
item.

This is a scope decision, not a claim that the language lacks those types.
Any future aggregate, object, string/real, handle, or event rung must introduce
its own representation, operations, lifetime rules, and differential fixtures.

The same inert treatment applies to a procedural pure string-literal write:
the assignment is lowered to `Empty` because the opaque string has no flat state
slot. Nonliteral writes and all subsequent string operations remain unsupported;
`do_while_string_literal` covers the write alongside an admitted loop.
