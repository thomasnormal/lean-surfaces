# Standardized AST envelope — schema v0.1 (Python payload)

One JSON document per source file. The **envelope** is language-neutral; the node
vocabulary inside `module` is per-language and mirrors the language's own frontend
(here: CPython `ast`, field names preserved exactly). Extractors must emit
**deterministic** output: `json.dump(..., indent=2)` with natural (insertion) key
order as specified below; same input bytes ⇒ same output bytes.

## Envelope

```json
{
  "schema_version": "0.1",
  "language": "python",
  "frontend": {"name": "cpython-ast", "version": "3.9.25"},
  "source_file": "Examples/python/sum_to.py",
  "source_sha256": "<hex sha256 of source bytes>",
  "module": { "kind": "Module", "body": [ <stmt>... ] },
  "lean_blocks": [ {"first_line": 9, "last_line": 14, "text": "theorem ...\n..."} ]
}
```

`lean_blocks[i].text` is the joined inner lines (comment markers stripped per
DESIGN.md), no trailing newline; `first_line`/`last_line` are the 1-based lines of
the `# lean[` and `# ]` markers.

## Spans

Every stmt/expr node carries `"span": {"lineno": L, "col_offset": C,
"end_lineno": EL, "end_col_offset": EC}` — CPython's own numbers (1-based lines,
0-based cols, exclusive ends).

## Statement nodes (`kind` + fields, in this key order: kind, span, then fields)

| kind | fields |
|---|---|
| `FunctionDef` | `name`: str, `args`: [param…], `args_unsupported`: str \| null, `locals_unsupported`: str \| null (set when the body *calls* a name it also assigns — CPython's static-locals rule makes that name an initially-unbound local, which the dynamic-env interpreter refuses loudly), `body`: [stmt…] |
| `Return` | `value`: expr \| null |
| `Assign` | `targets`: [expr…] (length 1 in the supported tier; chained `a=b=1` gives length > 1), `value`: expr |
| `AugAssign` | `target`: expr, `op`: binop-name, `value`: expr |
| `While` | `test`: expr, `body`: [stmt…], `orelse`: [stmt…] |
| `If` | `test`: expr, `body`: [stmt…], `orelse`: [stmt…] (elif = nested If in orelse, as CPython does) |
| `Expr` | `value`: expr |
| `Pass`, `Break`, `Continue` | — |
| `Unsupported` | `py_kind`: str (CPython class name, e.g. `"For"`, `"Try"`), `text`: str (`ast.unparse`, truncated to ≤200 chars) |

`param` = `{"arg": "n", "span": {…}}`. If the function uses defaults, `*args`,
keyword-only args, `**kwargs`, or decorators, set `args_unsupported` to a short
reason string (else `null`) and still list the plain positional params.

Any statement kind not in this table is emitted as `Unsupported` (the extractor
never fails on syntactically valid Python).

## Expression nodes

| kind | fields |
|---|---|
| `Constant` | `value`: const (below) |
| `Name` | `id`: str |
| `BinOp` | `left`: expr, `op`: one of `Add Sub Mult FloorDiv Mod Pow`, `right`: expr |
| `UnaryOp` | `op`: one of `USub Not`, `operand`: expr |
| `BoolOp` | `op`: one of `And Or`, `values`: [expr…] (≥2) |
| `Compare` | `left`: expr, `ops`: [one of `Eq NotEq Lt LtE Gt GtE`…], `comparators`: [expr…] (same length as ops) |
| `Call` | `func`: expr, `args`: [expr…], `call_unsupported`: str \| null (set when keywords/starargs present) |
| `List` / `Tuple` | `elts`: [expr…] |
| `Subscript` | `value`: expr, `index`: expr (CPython ≥3.9 `slice` field when it is a plain expr; `Slice`/`ExtSlice` nodes → whole Subscript becomes `Unsupported`) |
| `Unsupported` | `py_kind`: str, `text`: str (≤200 chars) |

Operator names are CPython's class names verbatim (`Mult` not `Mul`, `LtE` not `Le`).
Unlisted operator (e.g. `Div`, `BitOr`, `Is`, `In`) ⇒ the *containing* node is
emitted as `Unsupported` with that operator's name included in `py_kind`
(e.g. `"BinOp:Div"`).

## Constants

`{"type":"int","repr":"123"}` (decimal string, non-negative — CPython parses `-5`
as `USub(Constant 5)`) | `{"type":"bool","value":true}` | `{"type":"str","value":"…"}`
| `{"type":"none"}`. Float/bytes/complex/Ellipsis constants ⇒ the `Constant` node is
`Unsupported` (`py_kind`: `"Constant:float"` etc.).

## Worked example

`add.py`:
```python
# Examples/python/add.py (function only)
def add(a, b):
    return a + b
```

```json
{
  "schema_version": "0.1",
  "language": "python",
  "frontend": {"name": "cpython-ast", "version": "3.9.25"},
  "source_file": "Examples/python/add.py",
  "source_sha256": "…",
  "module": {
    "kind": "Module",
    "body": [
      {
        "kind": "FunctionDef",
        "span": {"lineno": 1, "col_offset": 0, "end_lineno": 2, "end_col_offset": 16},
        "name": "add",
        "args": [
          {"arg": "a", "span": {"lineno": 1, "col_offset": 8, "end_lineno": 1, "end_col_offset": 9}},
          {"arg": "b", "span": {"lineno": 1, "col_offset": 11, "end_lineno": 1, "end_col_offset": 12}}
        ],
        "args_unsupported": null,
        "body": [
          {
            "kind": "Return",
            "span": {"lineno": 2, "col_offset": 4, "end_lineno": 2, "end_col_offset": 16},
            "value": {
              "kind": "BinOp",
              "span": {"lineno": 2, "col_offset": 11, "end_lineno": 2, "end_col_offset": 16},
              "left": {"kind": "Name", "span": {"lineno": 2, "col_offset": 11, "end_lineno": 2, "end_col_offset": 12}, "id": "a"},
              "op": "Add",
              "right": {"kind": "Name", "span": {"lineno": 2, "col_offset": 15, "end_lineno": 2, "end_col_offset": 16}, "id": "b"}
            }
          }
        ]
      }
    ]
  },
  "lean_blocks": []
}
```

(Span values above are illustrative; emit whatever CPython reports.)
