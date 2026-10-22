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
value tier. The 2026-10-22 corpus snapshot has 5,556 files containing the tag;
it is the sole refusal in 20 files. The previous snapshot had 5,650 files and
28 sole refusals. Its current frequent companions are assignment targets
(3,176 files), statement calls (2,234), expression calls (2,103),
`NamedValueExpression:2state` (1,409), classes (1,147), member access (1,120),
real literals (639), and element-select source types (536). The remaining
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

The same flattening applies to a shallow untagged unpacked struct with integral
scalar or packed fields: each direct field is an independent vector cell, so
field reads, writes, and compound assignments preserve the scalar two-state
rules. Whole-struct values, nested or nonintegral fields, tagged structs, and
struct initializers remain outside the representation. Complete positional and
keyed/default assignment patterns are now lowered field by field, using the
same width conversion and `Squash2` boundary; partial or effectful patterns
remain loud. The `unpacked_struct_integral_fields` and
`unpacked_struct_initializers` fixtures exercise these two field-level forms.

Finite unpacked-array declaration concatenations receive the same cellwise
treatment when every operand is a pure constant array, exact typed pattern, or
integral scalar. The `unpacked_concat_initializer` fixture covers this
composition; runtime array sources and self-aliasing remain outside the
representation.

Fixed unpacked arrays of shallow untagged unpacked integral structs are also
flattened by position and field. A declaration such as `item values[0:1]`
produces cells `values[0].bits`, `values[0].count`, and so on; direct constant
member access retains the existing field semantics. Aggregate array
initializers, nested/nonintegral structs, and dynamic selections remain loud.
The `unpacked_struct_array` fixture covers this leaf composition.

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
