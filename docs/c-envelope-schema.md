# Standardized AST envelope — schema c-0.1 (C payload)

One JSON document per translation unit. The **envelope** is
language-neutral and mirrors `docs/envelope-schema.md` (Python) and
`docs/sv-envelope-schema.md` (SystemVerilog); the node vocabulary inside
`translation_unit` mirrors the language's own frontend — here clang's
JSON AST, `kind` names preserved exactly. Extractors must emit
**deterministic** output: same input bytes ⇒ same output bytes.

**Status: the C-tier charter's inch 4 (`docs/c-tier-charter.md` §4.4).
The schema is fixed; `extractors/c/extract.py` is inch 5 and does not
exist yet.** Every vocabulary table below is DERIVED from
`docs/c-construct-census.json` rather than chosen, so "what the ingester
accepts" and "what the corpus contains" cannot silently drift apart.

## 0 What is different about the C envelope, in one place

Three things this schema has that the other two do not, each because the
census or the profile forced it:

1. **`profile_id` is a first-class field**, because the profile is an
   INPUT to the AST and not a stamp on the side of it. Measured
   (`docs/c-tier-architecture.md` §4.3): under Apple's default headers
   `_FORTIFY_SOURCE` rewrites `memcpy`/`strcpy`/`sprintf`/`snprintf` into
   `__builtin___*_chk` and injects 10 `__builtin_object_size` nodes that
   are in nobody's source; with `-D_FORTIFY_SOURCE=0`, zero of each.
   **Same source, different profile, different program.** The ingester
   REFUSES a profile mismatch loudly.
2. **Spans carry BOTH spelling and expansion location**, because 6
   function-like macros produce corpus constructs (`YIELD`, `YIELD_PAWN`,
   `PACK_VM`, `VM_VAL`, `VM_MOVE`, `PROCESS`) and a refusal that cannot
   name the macro is a refusal a human cannot act on.
3. **`externals` is a list, not an ingested subtree.** The preprocessed
   TU is 3335 lines of which the corpus's own content is 58 functions and
   71 objects. The extractor filters by clang's sticky `loc.file` and
   records the referenced external declarations as names + prototypes
   rather than ingesting the headers' bodies. Measured: exactly **27
   libc names** over 146 call sites.

## 1 Envelope

```json
{
  "schema_version": "c-0.1",
  "language": "c",
  "frontend": {"name": "clang-ast-json", "version": "apple-clang-17"},
  "profile_id": "c-profile-0.1",
  "profile_flags": ["-std=c23", "-D_FORTIFY_SOURCE=0"],
  "source_file": "tools/ctwin/sunfish.c",
  "source_sha256": "<hex sha256 of source bytes>",
  "translation_unit": {"kind": "TranslationUnit", "decls": [ <decl>... ]},
  "externals": [ {"name": "memcpy", "type": "void *(void *, const void *, unsigned long)"} ],
  "lean_blocks": []
}
```

`frontend.version` is the compiler **FAMILY**, never the point release.
That correction is recorded twice in `docs/backlog.md` (3.9.19 ↔ 3.9.25
envelope churn, 53 files the second time) and reproducing it in a new
lane, having read the entry, would be inexcusable.

`profile_id` names the schema in `docs/c-profile.json` — the ABSTRACT
profile, a set of facts every host must satisfy, not a machine
(`docs/c-profile.md`). Two hosts that both satisfy it and run the same
`profile_flags` produce the same envelope, and that is a checked property
(`harness/c_profile_probe.py --check`).

**Cache key**: `<stem>-<sha256(source)[:16]>-<sha256(extract.py)[:8]>-<profile_id>`
— the existing `extractor_digest()` discipline plus the profile, because
a C envelope is a function of (source, extractor, PROFILE).

`lean_blocks` is `[]` for C and exists so the envelope stays
language-neutral; the inline-spec convention has no C form yet.

## 2 Spans

Every node carries

```json
"span": {"line": 160, "col": 1, "end_line": 164, "end_col": 2,
         "macro": {"name": "YIELD", "line": 302, "col": 9}}
```

`line`/`col` are the EXPANSION location (where the construct is, as a
reader sees it). `macro` is emitted **only** when the node's spelling
location differs from its expansion location — i.e. the node came out of
a macro body — and names the macro plus its spelling site. A node written
directly in the source carries no `macro` key, so macro-free sources
produce byte-identical envelopes to a schema without the field.

## 3 The node vocabulary — 45 kinds, and where they come from

**The ingester REFUSES any `kind` outside this table**, emitting an
`Unsupported` leaf (§4). The list is exactly the census's measured
vocabulary, which is stable: across the 11.3% corpus growth measured in
`docs/backlog.md` §L35, `node kinds 45 → 45, added none, dropped none`.
Counts are today's corpus and are informative, not normative.

### 3.1 Declarations (8)

| kind | count | fields |
| --- | ---: | --- |
| `FunctionDecl` | 59 | `name`, `type`, `storage` (`static` \| null), `params`: [`ParmVarDecl`…], `body`: `CompoundStmt` \| null (null = a prototype) |
| `VarDecl` | 321 | `name`, `type`, `storage`, `init`: expr \| null |
| `ParmVarDecl` | 113 | `name`, `type` |
| `FieldDecl` | 62 | `name`, `type` |
| `RecordDecl` | 13 | `name` \| null (anonymous), `fields`: [`FieldDecl`…] |
| `TypedefDecl` | 7 | `name`, `type` |
| `EnumDecl` | 3 | `name` \| null, `constants`: [`EnumConstantDecl`…] |
| `EnumConstantDecl` | 11 | `name`, `value`: int |

### 3.2 Statements (11)

| kind | count | fields |
| --- | ---: | --- |
| `CompoundStmt` | 224 | `body`: [stmt…] |
| `DeclStmt` | 228 | `decls`: [`VarDecl`…] |
| `IfStmt` | 253 | `cond`: expr, `then`: stmt, `else`: stmt \| null |
| `ForStmt` | 50 | `init`: stmt \| null, `cond`: expr \| null, `inc`: expr \| null, `body`: stmt |
| `WhileStmt` | 5 | `cond`: expr, `body`: stmt |
| `DoStmt` | 29 | `body`: stmt, `cond`: expr |
| `ReturnStmt` | 103 | `value`: expr \| null |
| `BreakStmt` | 8 | — |
| `ContinueStmt` | 6 | — |
| `GotoStmt` | 7 | `label`: str |
| `LabelStmt` | 3 | `label`: str, `body`: stmt |

**`SwitchStmt`/`CaseStmt`/`DefaultStmt` are deliberately absent** —
measured 0 in the corpus (the one `switch` in the file is the word, in a
comment at L283). They are rung R1, and their absence is what makes R1 a
rung rather than a v0 hole.

### 3.3 Expressions (19)

| kind | count | fields |
| --- | ---: | --- |
| `IntegerLiteral` | 779 | `value`: str (decimal, exact), `type` |
| `CharacterLiteral` | 95 | `value`: int, `type` |
| `StringLiteral` | 126 | `value`: str, `type` |
| `FloatingLiteral` | 15 | `value`: str (exact decimal spelling), `type` |
| `DeclRefExpr` | 2444 | `name`, `decl_kind`, `type` |
| `MemberExpr` | 410 | `base`: expr, `member`: str, `arrow`: bool, `type` |
| `ArraySubscriptExpr` | 328 | `base`: expr, `index`: expr, `type` |
| `CallExpr` | 320 | `callee`: expr, `args`: [expr…], `type` |
| `BinaryOperator` | 1007 | `op` (§3.5), `lhs`, `rhs`, `type` |
| `CompoundAssignOperator` | 24 | `op` (§3.5), `lhs`, `rhs`, `type` |
| `UnaryOperator` | 311 | `op` (§3.5), `sub`, `postfix`: bool, `type` |
| `ConditionalOperator` | 42 | `cond`, `then`, `else`, `type` |
| `ParenExpr` | 237 | `sub`, `type` |
| `ImplicitCastExpr` | 3123 | `cast` (§3.6), `sub`, `type` |
| `CStyleCastExpr` | 95 | `cast` (§3.6), `sub`, `type` |
| `InitListExpr` | 75 | `inits`: [expr…], `type` |
| `CompoundLiteralExpr` | 1 | `init`: `InitListExpr`, `type` |
| `UnaryExprOrTypeTraitExpr` | 12 | `trait`: `"sizeof"` \| `"alignof"`, `arg_type` \| `sub`, `type` |
| `ConstantExpr` | 11 | `value`: str, `sub`, `type` |

### 3.4 Types (7)

`BuiltinType`, `PointerType`, `RecordType`, `TypedefType`,
`ElaboratedType`, `ParenType`, `FunctionProtoType`. Emitted as a `type`
object wherever a node carries one:
`{"kind": "PointerType", "pointee": {...}}`, with `BuiltinType` carrying
`{"name": "int"}`. Qualifiers ride the type as `"const": true` /
`"volatile": true` / `"restrict": true` — **`restrict` is INGESTED and
NEVER EXPLOITED** (the memo's §2.5 non-claim, recorded here so nobody
later reads it from the AST and assumes the model checked it).

The scalar type vocabulary the corpus actually uses, by node count:
`int` 4733, `long` 340, `char` 254, `unsigned char` 173, `uint64_t` 153,
`double` 117, `unsigned long` 33, `unsigned long long` 15,
`unsigned int` 6, `uint32_t` 5, `uint8_t` 1.

### 3.5 Operators

**Binary (20)**: `!= % & && * + , - / < << <= = == > >= >> ^ | ||`
**Compound assignment (5)**: `*= += -= ^= |=`
**Unary (6)**: `! & * ++ - --`

Note `=` is a `BinaryOperator` in clang's vocabulary, not a statement
form, and `,` appears once. The ingester preserves clang's spelling
exactly rather than re-grouping, so an operator table drift is a schema
change and not a silent re-interpretation.

### 3.6 The conversion lattice — 8 castKinds, arriving PRE-SOLVED

| castKind | count | what it is |
| --- | ---: | --- |
| `LValueToRValue` | 1837 | the load — where the memory model's `load ty p` fires |
| `ArrayToPointerDecay` | 405 | array → pointer-to-first-element |
| `FunctionToPointerDecay` | 307 | function designator → pointer |
| `IntegralCast` | 239 | integer conversion, incl. the profile's C23-mandated out-of-range cases |
| `NoOp` | 217 | qualification conversion; no value change |
| `NullToPointer` | 53 | the `NULL` macro |
| `BitCast` | 52 | `void*` ↔ `T*`, all around the allocator and `memcpy` |
| `IntegralToFloating` | 13 | the deadline path only |

Explicit `CStyleCastExpr` splits 57 `NullToPointer` + 38 `IntegralCast`
— **no `T*`→`U*` cast between incompatible object types anywhere, and no
union.** The effective-type wall (memo §2.3) therefore fires on nothing
in this corpus, which is exactly the condition under which it is cheap to
install correctly and expensive to install later.

**This is the reason the frontend is clang and not a hand parser.** C's
usual arithmetic conversions, integer promotions, and the two decays are
where a hand parser goes wrong, and clang MATERIALIZES every one of them
as an explicit node. The ingester never re-derives a conversion; it reads
one off.

## 4 `Unsupported`

Anything outside §3 becomes

```json
{"kind": "Unsupported", "c_kind": "SwitchStmt", "text": "switch (x) { ... }",
 "span": {...}}
```

`c_kind` is clang's own node class; `text` is the source slice truncated
to ≤200 characters. This mirrors both sibling schemas exactly.

**The extractor NEVER fails on valid C.** Hard errors — unreadable file,
a clang DIAGNOSTIC, a profile mismatch — exit non-zero and say why. The
distinction is load-bearing and was already paid for once:
`harness/c_construct_census.py` originally censused a program that does
not compile and exited 0, because clang emits a PARTIAL AST alongside its
diagnostic. A partial AST is not a smaller program, it is a different
one. The extractor inherits that refusal.

## 5 Determinism

* `json.dump(..., indent=2)` with the key order specified above.
* A double run on the same input is byte-identical (the census
  instrument's contract, and the same test applies here).
* No absolute paths in the payload: `source_file` is repo-relative, and
  `span` carries line/column only.
* `externals` is sorted by name.

## 6 What the ingester will check, and why the census is its oracle

`LeanModels/C/Json.lean` (inch 6) ingests this envelope into a Lean AST
literal. Its `#guard` asserts structural facts **the census independently
knows** about `tools/ctwin/sunfish.c`:

| assertion | value |
| --- | ---: |
| function definitions | 58 |
| file-scope objects | 71 |
| indirect call sites | 19 |
| `SwitchStmt` nodes | 0 |
| distinct external names | 27 |

Two instruments, two paths, one answer — the ingester is checked against
a measurement rather than against itself. That is why
`harness/c_construct_census.py` landed first, as an instrument, and not
as prose.

## 7 Honest limits

* **The vocabulary is a corpus fact, not a C fact.** 45 kinds is what
  `sunfish.c` uses. A second C corpus will add kinds; whether it adds
  many is the measurement the charter's endgame (c) proposes as its
  second inch, and it has not been taken.
* **The type encoding here is the SHAPE, not the full C23 type grammar.**
  Arrays, function-pointer types and qualifier placement are specified by
  §3.4's recursive form; bit-fields, flexible array members and VLA types
  have no encoding, are 0 sites, and belong to rungs R2/R5.
* **`externals` records prototypes, not semantics.** What each of the 27
  libc names MEANS is the interpreter's libc slice (inch/milestone M4),
  not this schema's business. The list exists so the ingester can tell a
  declared-elsewhere name from an undeclared one.
* **No envelope has been produced yet.** This document fixes the target
  for inch 5; the first real envelope is what will prove the shape
  survives contact with clang's actual JSON.
