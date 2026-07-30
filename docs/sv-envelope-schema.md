# Standardized AST envelope — schema sv-0.1 (SystemVerilog payload)

One JSON document per source file, written by
`python3.12 extractors/sv/extract.py <file.sv> [more.sv ...]` (run from the
repo root) as `<file>.sv.json` next to each source. This document is the
normative contract for the Lean ingester (`LeanModels/Sv/**`): every node kind,
field name, and invariant the ingester may rely on is listed here.

The envelope is language-neutral and mirrors `docs/envelope-schema.md` (the
Python payload); the node vocabulary inside `design` is the SV M0 tier of
`docs/sv-design-m0.md`. Widths are **elaborated** widths from pyslang's
compilation (parse + elaboration), not raw syntax — e.g. the unbased unsized
literal `'0` in an 8-bit context is emitted as an 8-bit `Literal`.

Guarantees:

* The extractor **never fails on valid SystemVerilog**. Anything outside the
  vocabulary below becomes `{"kind": "Unsupported", ...}` at the closest
  enclosing node that can no longer be represented; surrounding structure is
  preserved (e.g. a supported assignment whose RHS contains a function call
  keeps its `BlockingAssign` shape with an `Unsupported` value).
* **Deterministic**: same input bytes (and same pyslang version) ⇒ same output
  bytes. `json.dump(..., indent=2)` + one trailing newline, ASCII-escaped
  strings, and fixed key order: `kind` first, then `span`, then the node's
  remaining fields in exactly the order of the tables below. A parsed envelope
  re-serialized with `json.dumps(obj, indent=2) + "\n"` reproduces the file
  byte-for-byte.

## Envelope

```json
{
  "schema_version": "sv-0.1",
  "language": "systemverilog",
  "frontend": {"name": "pyslang", "version": "11.0.0"},
  "source_file": "Examples/system-verilog/adder/adder.sv",
  "source_sha256": "<hex sha256 of the source bytes>",
  "design": {"kind": "Design", "modules": [<module>...], "others": [<Unsupported>...]},
  "lean_blocks": []
}
```

Top-level key order: `schema_version`, `language`, `frontend`, `source_file`,
`source_sha256`, `design`, `lean_blocks`. `source_file` is the (normalized,
`/`-separated) path exactly as passed on the command line. `lean_blocks` is
reserved and always `[]` in M0 (companion blocks are not scanned).

`design.modules` holds one `Module` per **top-level** module instance, in
elaboration (source) order. M0 is single-module; module instantiations inside a
module appear as `Unsupported` members, and `$unit`-scope compilation-unit
members (imports, unit variables, ...) appear as `Unsupported` nodes in
`design.others` (normally `[]`).

## Spans

Every node carries `"span"`: `{"line": L, "col": C, "end_line": EL,
"end_col": EC}` — slang's numbers: **1-based** lines and columns, end
**exclusive**. `span` may be `null` when no source range is available (only on
synthesized/degenerate nodes; never on the M0 examples).

## `Unsupported`

```json
{"kind": "Unsupported", "span": {...}, "sv_kind": "<tag>", "text": "<source text, <= 200 chars>"}
```

May appear anywhere a module member, port, decl, process, statement, or
expression is expected. `text` is the exact source slice of the offending
construct (whitespace-stripped, truncated to 200 chars, possibly `""`).
`sv_kind` is the slang AST class name, optionally qualified with `:detail`
(mirroring the Python lane's `"BinOp:Div"` convention). Tags the extractor
emits:

| tag | meaning |
|---|---|
| `<SlangClass>` | node class outside the vocabulary, e.g. `ForLoopStatement`, `CallExpression`, `ElementSelectExpression`, `RangeSelectExpression`, `ReplicationExpression`, `StringLiteral`, `RealLiteral`, `EmptyStatement`, `VariableDeclStatement`, `CaseStatement`, `InvalidStatement`, `InvalidExpression` |
| `InstanceSymbol:Instance`, `SubroutineSymbol:Subroutine`, `ParameterSymbol:Parameter`, ... | module member kinds outside M0 (class name `:` symbol kind) — routed to the module's `others` list |
| `ProceduralBlockSymbol:Initial` / `:Final` / `:AlwaysLatch` | process kinds outside M0 |
| `ProceduralBlockSymbol:NoEventControl` | `always` / `always_ff` whose body is not an event-controlled statement |
| `TimedStatement:<TimingClass>` | timing control other than a plain signal event — `TimedStatement:DelayControl` for `#10`, `TimedStatement:EventListControl` for `@(a or b)`, `TimedStatement:ImplicitEventControl` for `@*`; also any *nested* timed statement inside a process body |
| `SignalEventControl:NegEdge` / `:BothEdges` / `:None_` | edge other than `posedge` |
| `SignalEventControl:iff` | `@(posedge clk iff ...)` |
| `SignalEventControl:clock` | posedge expression that is not a 1-bit identifier |
| `AssignmentExpression:compound` | `+=`-style compound assignment |
| `AssignmentExpression:timing` | intra-assignment timing (`a <= #3 b`) |
| `AssignmentExpression:target` | assignment LHS that is not a plain identifier (bit/part-select, concat LHS, ...) |
| `ExpressionStatement:<Class>` | expression statement that is not an assignment (`i++;`, void call, ...) |
| `ContinuousAssignSymbol:delay` / `:form` | `assign #5 ...` / malformed continuous assign |
| `ConditionalStatement:Unique` / `:Unique0` / `:Priority` / `:multi` / `:pattern` | `unique`/`priority` if, multiple `&&&` conditions, `matches` pattern |
| `ConditionalExpression:multi` / `:pattern` | same, for `?:` |
| `BlockStatement:JoinAll` / `:JoinAny` / `:JoinNone` | `fork ... join*` |
| `BinaryExpression:<Op>` / `UnaryExpression:<Op>` | operator outside the M0 set, slang enum name (e.g. `BinaryExpression:Multiply`, `BinaryExpression:CaseEquality`, `UnaryExpression:Plus`) |
| `ConversionExpression:width` | **width mismatch in source**: an implicit conversion that changes bit width (M0 has no implicit extension/truncation rules) |
| `ConversionExpression:Explicit` / `:BitstreamCast` / `:StreamingConcat` | explicit casts |
| `NamedValueExpression:<SymbolKind>` | identifier that does not name a variable/net (e.g. `:Parameter`) |
| `PortSymbol:InOut` / `:Ref` | port directions outside in/out |
| `PortSymbol:...`, `VariableSymbol:...`, `NetSymbol:...` with `:2state` / `:signed` / `:range` / `:type` | unsupported declared type: 2-state (`bit`/`int`), `signed`, packed range other than `[W-1:0]` (e.g. `[0:7]`, multi-dim), or a non-vector type (enum, struct, real, ...) |
| `NetSymbol:<NetKind>` / `:delay` | net kinds other than `wire` (`Tri0`, `WAnd`, ...), net delays |
| `ExtractorInternal:<PyException>` | defensive catch-all: the extractor itself failed on this node (should not occur; `span` is `null`, `text` is the Python error) |

The tag list may grow with the tier; ingesters must treat **any** unknown
`sv_kind` as simply "unsupported" (the interpreter returns `.unsupported` when
an `Unsupported` node is reached).

## Module

Key order: `kind`, `span`, `name`, `ports`, `decls`, `processes`, `others`.

```json
{"kind": "Module", "span": {...}, "name": "adder",
 "ports": [<port>...], "decls": [<decl>...], "processes": [<process>...], "others": [...]}
```

Members are routed by category, each list in source order: `ports` (port list
entries), `decls` (module-level variables and nets, **excluding** the internal
symbols that back ANSI ports — a port appears only in `ports`), `processes`
(procedural blocks and continuous assigns), `others` (everything else —
functions, parameters, instances, generate blocks, ... — as `Unsupported`;
`[]` on M0-clean sources). Statement-level `begin/end` scope symbols are
elaboration artifacts and are silently skipped (their statements appear inside
the owning process body).

### Port

Key order: `kind`, `span`, `name`, `dir`, `width`.

```json
{"kind": "Port", "span": {...}, "name": "a", "dir": "in", "width": 8}
```

`dir` ∈ `"in" | "out"`. `width` is the elaborated bit width (scalar `logic` ⇒
`1`). The port's declared type must be an unsigned 4-state scalar or `[W-1:0]`
vector, else the port is `Unsupported`. Whether the port binds to a variable
or a net internally is not recorded (irrelevant at M0).

### Declarations

Key order: `kind`, `span`, `name`, `width`, `init`.

```json
{"kind": "Var", "span": {...}, "name": "a", "width": 8, "init": <expr> | null}
{"kind": "Net", "span": {...}, "name": "w", "width": 8, "init": <expr> | null}
```

`Var` = `logic`/`reg` variable; `Net` = `wire`. Same type restrictions as
ports (4-state, unsigned, scalar or `[W-1:0]`; other net kinds, delays,
signed/2-state/reversed-range/multi-dim types ⇒ `Unsupported`). `init` is the
declaration initializer, already width-resolved. LRM note: a **Var** initializer
is a time-0 assignment (the M0 examples use exactly this); a **Net** initializer
is per LRM an implicit *continuous assign* driver — no M0 example uses one, and
the ingester may treat a `Net` with non-null `init` as it treats `Assign`.

## Processes (`processes` list entries)

| kind | key order / fields |
|---|---|
| `AlwaysPosedge` | `kind`, `span`, `style` (`"always_ff"` \| `"always"`), `clock` (string: the 1-bit clock identifier), `body` (stmt) |
| `AlwaysComb` | `kind`, `span`, `body` (stmt) |
| `Assign` | `kind`, `span`, `target` (expr, always an `Ident`), `value` (expr) — continuous `assign` |

`AlwaysPosedge` covers exactly `always_ff @(posedge clk) ...` and
`always @(posedge clk) ...`; `style` records which keyword the source used —
**M0 cycle semantics treats both identically** (edge-phase processes). Any
other sensitivity (negedge, event lists, `@*`, `iff`, delays, always_latch,
initial, final) makes the whole process `Unsupported`. `body` is a single
statement node (often `Block` or `If`).

## Statements

| kind | key order / fields |
|---|---|
| `Block` | `kind`, `span`, `stmts`: [stmt...] — `begin ... end` (a single-statement body still nests one level: `"stmts": [<stmt>]`) |
| `BlockingAssign` | `kind`, `span`, `target` (expr, always `Ident`), `value` (expr) — `=` |
| `NonblockingAssign` | `kind`, `span`, `target` (expr, always `Ident`), `value` (expr) — `<=` |
| `If` | `kind`, `span`, `cond` (expr), `then` (stmt), `else` (stmt \| `null`) — `else if` chains nest as `If` inside `else` |
| `Unsupported` | see above |

Assignment targets are whole-signal identifiers only; a bit-select, part-select
or concatenation LHS makes the *statement* `Unsupported`
(`AssignmentExpression:target`). `If` conditions may be any width (truthiness
per LRM: true iff some bit is `1`).

## Expressions

Every supported expression node carries `width`: its **elaborated result width
in bits**. (`Unsupported` expression nodes have no `width`.)

| kind | key order / fields | width invariant |
|---|---|---|
| `Ident` | `kind`, `span`, `width`, `name` (string) | declared width of the named var/net/port |
| `Literal` | `kind`, `span`, `width`, `bits` (string) | `len(bits) == width` |
| `Unary` | `kind`, `span`, `width`, `op` (`"~"` \| `"!"` \| `"-"`), `operand` (expr) | `~`,`-`: `width == operand.width`; `!`: `width == 1` |
| `Binary` | `kind`, `span`, `width`, `op` (see below), `left`, `right` (exprs) | `+ - & \| ^`: `width == left.width == right.width`; comparisons: `width == 1` and `left.width == right.width` |
| `Ternary` | `kind`, `span`, `width`, `cond`, `then`, `else` (exprs) | `width == then.width == else.width`; `cond` any width |
| `Concat` | `kind`, `span`, `width`, `parts`: [expr...] | `width == sum(part.width)` |
| `Unsupported` | see above | — |

`Binary` `op` ∈ `"+" "-" "&" "|" "^" "==" "!=" "<" "<=" ">" ">="` (the M0 set;
`==`/`!=` are *logical* equality — case equality `===` is
`BinaryExpression:CaseEquality` → Unsupported). The width invariants hold
whenever the children are supported nodes — the extractor enforces them and
demotes violators to `Unsupported`; if a child is itself `Unsupported` its
width is unknown and the parent keeps its structure (the interpreter goes
`.unsupported` on reaching the child).

The extractor transparently unwraps slang's **same-width implicit/propagated
conversions** (elaboration artifacts: 2-state literal into a 4-state context,
sign reinterpretation) — they never appear in the envelope. *Width-changing*
implicit conversions are the M0 "width mismatch in source" case ⇒
`ConversionExpression:width`.

### `Literal` — 4-state constants

```json
{"kind": "Literal", "span": {...}, "width": 8, "bits": "1x0z1010"}
```

`bits` is a string over `{'0','1','x','z'}` (lowercase), length exactly
`width`, written **MSB-first** — the same order as SV source and `$display %b`
output: `8'b1x0z_1010` ⇒ `"1x0z1010"`, `8'd2` ⇒ `"00000010"`, `'0` in an 8-bit
context ⇒ `"00000000"`, `'1` ⇒ `"11111111"`, `'x` ⇒ `"xxxxxxxx"`.

> **Ingester warning — bit order.** `LeanModels.Sv.LVec` is **LSB-first**
> (`bits[0]` is bit 0). `bits` here is MSB-first, so the ingester must
> **reverse the string**: `LVec.bits[i] = bits[width - 1 - i]`. This is the
> one place the envelope and the Lean value core differ in orientation.

x/z digits are preserved exactly as written (after slang's per-digit
expansion, e.g. `8'bx` ⇒ `"xxxxxxxx"` per the LRM's leading-digit extension
rule). Unsized bare integers (`1`, which is a signed 32-bit `int`) only occur
behind width-changing conversions in M0 code and therefore surface as
`Unsupported` unless the context is exactly 32 bits wide.

## Worked example

`Examples/system-verilog/adder/adder.sv`:

```systemverilog
module adder (input  logic [7:0] a, b,
              output logic [7:0] s);
  assign s = a + b;
endmodule
```

`Examples/system-verilog/adder/adder.sv.json` (exact extractor output):

```json
{
  "schema_version": "sv-0.1",
  "language": "systemverilog",
  "frontend": {
    "name": "pyslang",
    "version": "11.0.0"
  },
  "source_file": "Examples/system-verilog/adder/adder.sv",
  "source_sha256": "d078ae546305d852af83e963c991cbc0f81f6a7f647f9598c675e836ea138c09",
  "design": {
    "kind": "Design",
    "modules": [
      {
        "kind": "Module",
        "span": {
          "line": 1,
          "col": 1,
          "end_line": 4,
          "end_col": 10
        },
        "name": "adder",
        "ports": [
          {
            "kind": "Port",
            "span": {
              "line": 1,
              "col": 34,
              "end_line": 1,
              "end_col": 35
            },
            "name": "a",
            "dir": "in",
            "width": 8
          },
          {
            "kind": "Port",
            "span": {
              "line": 1,
              "col": 37,
              "end_line": 1,
              "end_col": 38
            },
            "name": "b",
            "dir": "in",
            "width": 8
          },
          {
            "kind": "Port",
            "span": {
              "line": 2,
              "col": 34,
              "end_line": 2,
              "end_col": 35
            },
            "name": "s",
            "dir": "out",
            "width": 8
          }
        ],
        "decls": [],
        "processes": [
          {
            "kind": "Assign",
            "span": {
              "line": 3,
              "col": 10,
              "end_line": 3,
              "end_col": 19
            },
            "target": {
              "kind": "Ident",
              "span": {
                "line": 3,
                "col": 10,
                "end_line": 3,
                "end_col": 11
              },
              "width": 8,
              "name": "s"
            },
            "value": {
              "kind": "Binary",
              "span": {
                "line": 3,
                "col": 14,
                "end_line": 3,
                "end_col": 19
              },
              "width": 8,
              "op": "+",
              "left": {
                "kind": "Ident",
                "span": {
                  "line": 3,
                  "col": 14,
                  "end_line": 3,
                  "end_col": 15
                },
                "width": 8,
                "name": "a"
              },
              "right": {
                "kind": "Ident",
                "span": {
                  "line": 3,
                  "col": 18,
                  "end_line": 3,
                  "end_col": 19
                },
                "width": 8,
                "name": "b"
              }
            }
          }
        ],
        "others": []
      }
    ],
    "others": []
  },
  "lean_blocks": []
}
```

Shape cheat-sheet for the other four examples: `counter` = one `AlwaysPosedge`
(`style: "always_ff"`, `clock: "clk"`) whose body is an `If` with two
`NonblockingAssign`s (`'0` ⇒ `Literal "00000000"`, `count + 8'd1` ⇒ `Binary +`
with `Literal "00000001"`); `race_blk` / `swap_nba` = two `Var` decls with
`Literal` inits (`"00000001"`, `"00000010"`) and two `AlwaysPosedge`
(`style: "always"`) processes each containing a single `BlockingAssign` /
`NonblockingAssign`; `xsel` = one `AlwaysComb` whose body is an `If` with two
`BlockingAssign`s.

---

# Symbolic mode — schema sv-0.2 (additive; `--top`)

Phase 1 of the CV32E40P program adds a second extraction mode:

```
python3.12 extractors/sv/extract.py --top <module> <files...> [-I <incdir>] [-o out.json]
```

All sources are compiled as **one** slang compilation (multi-file is for
**name resolution only**: package imports, typedefs, enum types) and exactly
the named top module is emitted, as one envelope (default output path: next
to the file that defines the top module, `<file>.sv.json`). Everything in
this section is **additive**: single-file mode (`--top` absent) is untouched
and remains byte-identical at schema `sv-0.1`.

Two design laws govern this mode (they are the point of the program):

1. **Parameters stay symbolic.** Parameter *values* are never folded into
   the envelope's primary form. A parameter reference in any expression
   position is a `ParamRef` node; declared widths are the source's symbolic
   range expressions. On the Lean side (phase 2) a parameterized module
   becomes a Design-valued *function* of its parameters, enabling ∀-width
   theorems.
2. **Generate stays structural.** A generate-for is ONE `GenerateFor` node
   (genvar, symbolic header expressions, body template) — an indexed family
   the prover handles by induction; a generate-if is ONE `GenerateIf` with a
   symbolic condition. Nothing is unrolled.

**Symbolic-primary / resolved-secondary convention.** Wherever slang only
exposes post-elaboration integers, the envelope carries the recovered
symbolic form as the primary field and the defaults-elaborated integer in a
`resolved`-family field beside it, for phase-2 cross-checks only:
`resolved` = elaborated *value* (on `ParameterDecl`/`LocalParam`/`SysCall`),
or elaborated *bit width* (on `PackedType`/`TypeRef`); `resolved_width` =
elaborated context width (on `Int`/`Fill`); `resolved_count` = number of
elaborated instances (on `GenerateFor`). Ingesters MUST treat these as
metadata, never as the contract.

**Recovery method and honest limits.** (a) Bound expressions are used
wherever slang retains them — parameter/localparam initializers
(`ParameterSymbol.initializer`), generate-for headers
(`initialExpression`/`stopExpression`/`iterExpression`), generate-if
conditions (`conditionExpression`), and every process/assign expression;
in these trees parameter references are still symbol references, emitted as
`ParamRef`/`GenvarRef`/`EnumRef`. (b) The one place slang folds without
keeping a bound expression is the packed **dimensions of declared types**
(resolved to integer ranges); those are recovered from the declaration's
*syntax tree* and identifiers in them are classified via `lookupName` on the
top module's body scope. Limits: syntax-recovered nodes carry `"width":
null` (they are not re-type-checked); a dimension identifier not visible
from the top module's scope (e.g. a package-private name never imported)
degrades to an `Unsupported` node with the `resolved` width still present
(`"packed": null` when a whole dimension list is unrecoverable); genvar
references are recognized *by name* against the enclosing generate stack;
`width` fields on ordinary expression nodes inside processes are elaborated
under **default** parameter values (cross-check only — the binding symbolic
widths are on the declarations); the body template of a `GenerateFor` is
bound from its first elaborated instance (a loop with zero instances under
defaults keeps its body as one `Unsupported` node with the source text);
untaken generate-if branches ARE emitted (slang binds them in
uninstantiated mode).

## Envelope (symbolic)

Top-level key order: `schema_version` (`"sv-0.2"`), `language`, `frontend`,
`mode` (`"symbolic"`), `top`, `source_files` (list of `{path, sha256}` in
CLI order), `packages` (sorted names of packages the top module actually
references), `design`, `lean_blocks`. `design.modules` holds exactly one
`Module`; `design.others` is `[]` (packages are name-resolution inputs, not
`$unit` noise).

## Module (symbolic)

Key order: `kind`, `span`, `name`, `imports`, `params`, `types`, `ports`,
`decls`, `processes`, `generates`, `others`. New lists:

| list | contents |
|---|---|
| `imports` | `{"kind": "Import", "span", "package", "name"}` — `name` is `"*"` for wildcard imports |
| `params` | `ParameterDecl` / `LocalParam`, source order |
| `types` | `EnumType`, first-reference order |
| `generates` | `GenerateFor` / `GenerateIf`, source order |

## New node kinds

| kind | key order / fields |
|---|---|
| `ParameterDecl` | `kind`, `span`, `name`, `type` (`PackedType` \| `TypeRef` \| `null` for implicit), `default` (symbolic expr \| `null`), `resolved` |
| `LocalParam` | `kind`, `span`, `name`, `type`, `expr` (symbolic), `resolved` |
| `ParamRef` | `kind`, `span`, `name` (+ `from_package` only when package-scoped) — a parameter/localparam reference in ANY expression position |
| `GenvarRef` | `kind`, `span`, `name` — reference to an enclosing generate-for's loop variable |
| `GenerateFor` | `kind`, `span`, `label`, `genvar`, `init`, `bound`, `step` (symbolic exprs; `step` uses `Unary` op `"++"`/`"--"`), `resolved_count`, `body` (member list, source order) |
| `GenerateIf` | `kind`, `span`, `label`, `else_label`, `cond` (symbolic), `then` (member list), `else` (member list \| `[GenerateIf]` for else-if chains \| `null`) |
| `EnumType` | `kind`, `span`, `name` (typedef name, or slang's deterministic `e$N` for anonymous enums), `from_package` (`null` for local), `base_width` (`PackedType`), `members` (`[{name, value}]`, `value` an int or an x/z bits string — metadata) |
| `EnumRef` | `kind`, `span`, `type`, `member`, `from_package` — an enum member used in an expression |
| `TypeRef` | `kind`, `name`, `from_package`, `resolved` — a declaration's type given by (enum) type name |
| `PackedType` | `kind`, `packed` (`[{msb, lsb}]` symbolic bounds per packed dimension, `[]` scalar, `null` unrecoverable), `resolved` (total bit width) |
| `SysCall` (expression position) | `kind`, `span`, `name` (`"$clog2" \| "$bits" \| "$high" \| "$size"`), `args`, `resolved` — distinct from the statement-position `SysCall` (`$display`/..., which has `format`/`args`/`arg_signed`) |
| `Int` | `kind`, `span`, `value` (int), `resolved_width` — an *unsized* integer literal (sized literals stay `Literal`) |
| `Fill` | `kind`, `span`, `bit` (`"0" \| "1" \| "x" \| "z"`), `resolved_width` — an unbased-unsized literal (`'0`/`'1`/`'x`/`'z`); its width is context-propagated, i.e. potentially parameter-dependent, so it is never emitted as a folded `Literal` in this mode |
| `Import` | see above |

Symbolic-mode changes to existing nodes: `Port`/`Var`/`Net` carry their
declared type object (`PackedType` or `TypeRef`) in the `width` field
(instead of an integer); enum-typed ports/vars/idents are in-vocabulary;
multi-dimensional packed vectors of 4-state unsigned scalars are
in-vocabulary (`packed` lists one `{msb, lsb}` per dimension, outermost
first). In **symbolic expression positions only** (parameter defaults,
localparam exprs, generate headers and conditions, dimension bounds) the
operator set additionally admits `* / % ** << >> <<< >>>`; in ordinary
process/assign positions the M0/self-check operator set is unchanged and
everything else remains `Unsupported` (selects, case, event lists,
instantiations, 2-state types, ... — phase 2+ tiers). A width-changing
implicit conversion whose operand contains symbolic references is emitted
as `Resize` around the symbolic operand (unsigned operands; signed →
`Unsupported`) instead of being constant-folded.

New `Unsupported` tags of this mode: `Syntax:<SyntaxKind>` /
`Syntax:Identifier:unresolved` / `Syntax:Identifier:<SymbolClass>`
(dimension-syntax recovery), `GenerateBlockSymbol:unconditional` (bare
`begin`/`end` generate block), `GenerateFor:no-template` (zero-instance
loop body), `TransparentMemberSymbol:<Class>`.
