# Standardized AST envelope — schema spice-0.1 (SPICE netlist payload)

One JSON document per source file, written by
`python3 extractors/spice/extract.py <file.cir> [more.cir ...]` (run from the
repo root) as `<file>.json` next to each source (final extension replaced —
`divider.cir` → `divider.json`, matching the Python lane's `tri.py` →
`tri.json`). This document is the normative contract for the Lean ingester
(`LeanModels/Spice/**`): every card kind, field name, and invariant the
ingester may rely on is listed here.

The envelope is language-neutral and mirrors `docs/envelope-schema.md`
(Python) and `docs/sv-envelope-schema.md` (SystemVerilog); the card
vocabulary inside `netlist` is the spice M0 tier of `docs/spice-design-m0.md`.
The frontend is a hand-written line-based parser in the extractor itself
(SPICE decks are card-per-line and the M0 grammar is regular — no third-party
frontend), so `frontend` is `{"name": "spice-extract", "version": "0.1"}`.

Guarantees:

* The extractor **never fails on valid SPICE**. Anything outside the
  vocabulary below becomes `{"kind": "Unsupported", ...}` — always at card
  granularity (a SPICE card is one logical line; there are no supported
  sub-expressions to preserve around a bad token, so a card is either fully
  supported or fully `Unsupported`).
* **Deterministic**: same input bytes ⇒ same output bytes.
  `json.dump(..., indent=2)` + one trailing newline, ASCII-escaped strings,
  and fixed key order: `kind` first, then `span`, then the card's remaining
  fields in exactly the order of the tables below. A parsed envelope
  re-serialized with `json.dumps(obj, indent=2) + "\n"` reproduces the file
  byte-for-byte.
* **Every numeric value is an exact rational** `{"num": int, "den": int}` in
  lowest terms with `den > 0`. Decimal notation and SPICE scale suffixes are
  parsed exactly, never through floating point (see the value grammar below).
* Hard errors (non-zero exit, no output): unreadable file / not UTF-8.

## Envelope

```json
{
  "schema_version": "spice-0.1",
  "language": "spice",
  "frontend": {"name": "spice-extract", "version": "0.1"},
  "source_file": "Examples/spice/divider/divider.cir",
  "source_sha256": "<hex sha256 of the source bytes>",
  "netlist": {"kind": "Netlist", "title": "...", "subckts": [<Subckt>...], "cards": [<card>...]},
  "lean_blocks": []
}
```

Top-level key order: `schema_version`, `language`, `frontend`, `source_file`,
`source_sha256`, `netlist`, `lean_blocks`. `source_file` is the (normalized,
`/`-separated) path exactly as passed on the command line. `lean_blocks` is
reserved and always `[]` in M0.

## Lexical layer (what the parser does before cards exist)

* **Title.** The FIRST line of a SPICE deck is ALWAYS the title, never a card
  (the classic SPICE gotcha: an element card on line 1 is silently swallowed
  as the title — ngspice does the same). Emitted verbatim (stripped) as
  `netlist.title`; it is the only string not lowercased.
* **Comments.** A line whose first non-blank character is `*` is a comment.
  Inline comments: `;` anywhere, and `$` when at line start or preceded by
  whitespace, cut the rest of the line (ngspice conventions).
* **Continuations.** A line whose first non-blank character is `+` continues
  the previous card. A `+` line with no previous card is
  `Unsupported`/`Continuation:stray`.
* **`.end`** stops parsing; everything after it is ignored. `.end` itself is
  not emitted as a card.
* **Case-insensitivity.** SPICE is case-insensitive: every identifier
  (device names, node names, subckt names, keywords) is lowercased in the
  envelope. `Unsupported.text` keeps original case.
* Blank lines are skipped. Tokens are whitespace-separated. Parenthesized
  MOS model parameters remain in the source for ngspice but are intentionally
  outside the structured polarity-only model node.

## Spans

Every card carries `"span": {"line": L, "end_line": EL}` — **1-based**,
**inclusive** line numbers covering the card's logical lines including `+`
continuations. (Line-granular by design: SPICE is a card format; there is no
column structure worth preserving. This differs from the SV lane's
column-precise, end-exclusive spans.) `Netlist` itself carries no span (it is
the whole file).

## Exact value grammar

A value token is `[+-]? mantissa [eE [+-]? digits]? letters*` where mantissa
is a decimal (`5`, `1.5`, `.5`, `5.`). Parsing is exact over ℚ:

1. the decimal mantissa (e.g. `2.2` = 11/5),
2. times 10^exponent if an exponent is present,
3. times the scale suffix if the leading letters match one (longest-match,
   case-insensitive),
4. any remaining letters are units and are **ignored** (`1kohm`, `5V`,
   `100nF`); a bare `e` with no digits is a unit letter, not an exponent
   (`1e` = 1, ngspice behavior).

| suffix | scale (exact) | | suffix | scale (exact) |
|---|---|---|---|---|
| `t` | 10^12 | | `m` | 1/1000 |
| `g` | 10^9 | | `u` | 1/10^6 |
| `meg` | 10^6 | | `n` | 1/10^9 |
| `k` | 10^3 | | `p` | 1/10^12 |
| `mil` | 127/5000000 (= 25.4·10⁻⁶) | | `f` | 1/10^15 |

**`M` is milli and `MEG` is mega regardless of case** (the classic SPICE
gotcha; unit-tested). Normative examples (all unit-tested in
`extractors/spice/test_extract.py`): `1k` = 1000, `1m` = 1/1000,
`2.2meg` = 2200000, `470u` = 47/100000, `1.5` = 3/2, `1.5e-2` = 3/200,
`2e3k` = 2·10^6. Non-numbers (`1k3`, `abc`, `1..2`) make the containing card
`Unsupported` with a `:value` tag.

## `Unsupported`

```json
{"kind": "Unsupported", "span": {...}, "spice_kind": "<tag>", "text": "<source text, <= 200 chars>"}
```

May appear anywhere a card is expected (top-level `cards`, a subckt `body`,
or — for a demoted definition — the `subckts` list itself). `text` is the
logical card's source text (continuations joined by single spaces, original
case, truncated to 200 chars). Tags the extractor emits:

| tag | meaning |
|---|---|
| `D`, `Q`, `E`, `G`, `F`, `H`, `B`, `K`, ... (uppercase element letter) | element kind outside the structured vocabulary: diodes, BJTs, controlled sources, coupled inductors, ... |
| `.tran`, `.ac`, `.dc`, `.param`, `.include`, `.control`, `.endc`, ... (the dot word) | dot-card outside the structured vocabulary (a `.control` block is NOT swallowed: each of its lines surfaces as its own card, most of them `Unsupported` — loud) |
| `M:form` | MOS card not exactly `Mxxx drain gate source bulk model` |
| `Model:form` | `.model` missing a name or using a type other than `nmos`/`pmos` |
| `R:form` / `C:form` / `L:form` / `V:form` / `I:form` | wrong token count for the M0 grammar — extra parameters (`tc=`), source transients (`PULSE`, `SIN`, `AC`), ... |
| `R:value` / `C:value` / `L:value` / `V:value` / `I:value` | value token is not a number |
| `X:form` | X card with fewer than 2 tokens after the name, or containing `=` (instance parameters) |
| `Subckt:form` / `Subckt:params` | `.subckt` with no name / with `PARAMS:` or `=` tokens — the WHOLE definition (header through `.ends`) is demoted to one `Unsupported` |
| `Subckt:ends-mismatch` | `.ends <name>` naming a different subckt than the open one — whole definition demoted |
| `Subckt:unterminated` | `.subckt` never closed before `.end`/EOF — whole definition demoted |
| `Ends:stray` | `.ends` with no open `.subckt` |
| `Op:form` | `.op` with arguments |
| `Continuation:stray` | `+` line with no card to continue |

The tag list may grow with the tier; ingesters must treat **any** unknown
`spice_kind` as simply "unsupported" (`flatten`/solving reports the netlist
as unsupported when an `Unsupported` card is reachable).

## `Netlist`

Key order: `kind`, `title`, `subckts`, `cards`.

* `subckts`: the **top-level** `.subckt` definitions, in source order.
  (A demoted definition appears here as `Unsupported`.)
* `cards`: all other top-level cards (elements, MOS transistors/models,
  `X` instances, `Op`, `Unsupported`), in source order. SPICE card order
  carries no semantics; the split into two lists is for the ingester's
  convenience (subckt lookup by name).

## `Subckt`

Key order: `kind`, `span`, `name`, `ports`, `body`.

```json
{"kind": "Subckt", "span": {...}, "name": "attn", "ports": ["a", "b"], "body": [<card>...]}
```

`ports` are the formal port node names, in header order (may be empty).
`body` holds the definition's cards in source order and may contain element
cards, `X` instances, `Op`, `Unsupported` — and nested `Subckt` nodes:
`.subckt` definitions **nest syntactically** and the extractor preserves the
nesting verbatim, but M0 `flatten` supports only top-level definitions and
reports a `.nestedSubckt` error on meeting a nested one (see
`docs/spice-design-m0.md`). Port names and `"0"` inside the body follow the
flatten semantics of the design doc (ports substituted, `"0"` global ground,
other nodes instance-local).

## Element cards — `R`, `C`, `L`, `V`, `I`

Key order: `kind`, `span`, `name`, `nodes`, `value`.

```json
{"kind": "R", "span": {...}, "name": "r1", "nodes": ["in", "out"], "value": {"num": 1000, "den": 1}}
```

| kind | card | grammar | value unit |
|---|---|---|---|
| `R` | resistor | `Rxxx n1 n2 value` | ohms |
| `C` | capacitor | `Cxxx n1 n2 value` | farads (DC: open — see design doc) |
| `L` | inductor | `Lxxx n1 n2 value` | henries (DC: short, carries a branch current) |
| `V` | independent voltage source | `Vxxx n+ n- [DC] value` | volts |
| `I` | independent current source | `Ixxx n+ n- [DC] value` | amps |

The optional `DC` keyword on sources is accepted and not recorded (the value
is the DC value either way). Source orientation is the SPICE convention and
is normative for the device laws in the design doc: for `V`, `nodes[0]` is
the `+` terminal; for `I`, a positive value drives current **from `nodes[0]`
through the source into `nodes[1]`** (it removes current from the `nodes[0]`
node and injects it at `nodes[1]`). Anything beyond the M0 grammar (extra
parameters, `AC`/`PULSE`/`SIN` transients) demotes the card to
`Unsupported`. Element names keep their full (lowercased) spelling,
including the kind letter: `R1` → `"r1"`. The extractor does not check name
uniqueness or value sign/zero — those are `WellPosed` obligations in Lean.

## MOS cards — `M` and `Model`

The transistor switch tier structures four-terminal MOS cards and the
polarity of their model declarations:

```json
{"kind": "M", "span": {...}, "name": "m1", "nodes": ["d", "g", "s", "b"], "model": "nmod"}
{"kind": "Model", "span": {...}, "name": "nmod", "polarity": "nmos"}
```

`Mxxx drain gate source bulk model` must have exactly those six tokens.
`.model name nmos|pmos ...` records only `name` and `polarity`; remaining
model parameters stay in the original `.cir` deck for ngspice. This is
intentional: `LeanModels.Spice.Switch` proves gates against an ideal
on/off connectivity abstraction, while ngspice validates the full analog
deck. The exact linear-DC `flatten`/MNA path rejects both structured card
kinds loudly instead of pretending they are linear elements.

## `X` — subcircuit instance

Key order: `kind`, `span`, `name`, `subckt`, `connections`.

```json
{"kind": "X", "span": {...}, "name": "x1", "subckt": "attn", "connections": ["in", "out1"]}
```

Grammar `Xxxx node1 ... nodeN subcktname` (the last token is the subckt
name, everything between is the connection list, length ≥ 1). Arity against
the definition's `ports` is NOT checked by the extractor — `flatten` reports
a `.portArity` error (the definition may not even be in this file at M0's
level of generality; in the committed examples it always is).

## `Op`

```json
{"kind": "Op", "span": {...}}
```

The `.op` card: the DC operating-point analysis — the ONLY analysis M0
models, and exactly the relation `Satisfies` defines. Supported so that the
committed netlists are simultaneously Unsupported-free AND directly runnable
under `ngspice -b`. Semantically a no-op for the Lean ingester.

## Worked example

`Examples/spice/divider/divider.cir` (comment lines elided here; the committed
file carries the ngspice prevalidation results as comments):

```spice
divider -- 5V into a 1k/2k resistive divider (spice lane leaf example)
v1 in 0 dc 5
r1 in out 1k
r2 out 0 2k
.op
.end
```

`Examples/spice/divider/divider.json` (exact extractor output):

```json
{
  "schema_version": "spice-0.1",
  "language": "spice",
  "frontend": {
    "name": "spice-extract",
    "version": "0.1"
  },
  "source_file": "Examples/spice/divider/divider.cir",
  "source_sha256": "f609f5aa0e7de88a891177983fa6b6495a520fe1387d2c2931c5dcdd11f74577",
  "netlist": {
    "kind": "Netlist",
    "title": "divider -- 5V into a 1k/2k resistive divider (spice lane leaf example)",
    "subckts": [],
    "cards": [
      {
        "kind": "V",
        "span": {
          "line": 12,
          "end_line": 12
        },
        "name": "v1",
        "nodes": [
          "in",
          "0"
        ],
        "value": {
          "num": 5,
          "den": 1
        }
      },
      {
        "kind": "R",
        "span": {
          "line": 13,
          "end_line": 13
        },
        "name": "r1",
        "nodes": [
          "in",
          "out"
        ],
        "value": {
          "num": 1000,
          "den": 1
        }
      },
      {
        "kind": "R",
        "span": {
          "line": 14,
          "end_line": 14
        },
        "name": "r2",
        "nodes": [
          "out",
          "0"
        ],
        "value": {
          "num": 2000,
          "den": 1
        }
      },
      {
        "kind": "Op",
        "span": {
          "line": 15,
          "end_line": 15
        }
      }
    ]
  },
  "lean_blocks": []
}
```

Shape cheat-sheet for the other two examples: `chain` = one `Subckt`
(`attn`, ports `["a","b"]`, body two `R`s) + a 5V `V`, nine `X` instances
(chains of 1, 2, 3 sections), three 3k termination `R`s, and `Op`; `r2r` =
one `Subckt` (`r2r`, ports `["b3","b2","b1","b0","out"]`, body eight `R`s) +
four bit-driver `V`s, one `X`, and `Op`.
