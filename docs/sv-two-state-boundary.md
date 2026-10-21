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
value tier. The 2026-10-21 corpus snapshot has 5,743 files containing the tag,
but only 28 files where it is the sole refusal and 490 where it is one of at
most two refusal kinds. Its frequent companions are assignment targets (3,215
files), calls (2,243), `NamedValueExpression:2state` (1,409), classes (1,146),
member access (1,120), real literals (639), and element-select source types
(575). The sole-tag examples include unpacked arrays, events, real and string
variables, handles, and other declaration forms with no common bit-vector
meaning.

The public representation has no aggregate heap, queue, object, string, real,
handle, or event scheduler. The symbolic `PDecl`/`PType` representation also
does not carry a two-state bit, and symbolic `Squash2` is intentionally loud.
Adding a boolean to the declaration record would therefore accept programs
whose storage and operations still have no semantics, or would silently erase
an event/object boundary. The tier keeps those declarations and every use that
depends on them as `Unsupported`; the existing integral two-state behavior is
the complete admitted slice for this census item.

This is a scope decision, not a claim that the language lacks those types.
Any future aggregate, object, string/real, handle, or event rung must introduce
its own representation, operations, lifetime rules, and differential fixtures.
