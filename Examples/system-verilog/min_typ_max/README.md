# Min typ max

IEEE 1800-2023 §11.11/§10.8: one global elaboration choice selects one bound
expression. The default is typical. See [the contract](../../../docs/sv-min-typ-max.md).

`proof.lean` proves live selected reads, independence from unselected values,
blocking storage preserving pending NBA work/output, NBA capture and capture
stability after a later source change. Its receipt checks the actual parsed
blocking/NBA statements in `runtime.sv`, all eight successful default-choice
transcripts under both region oracles, six time-zero runs, two loud fixtures
and malformed wrapper rejection. These theorems describe the selected parsed
program; they do not prove the frontend's choice algorithm.

| Source | Coverage | min stdout | typ stdout | max stdout |
|---|---|---|---|---|
| `choices.sv` | Positional choice, widths, narrowing, sign extension and type queries | `choices 33 1 -128 / widths 4 32` | `choices 22 2 -127 / widths 8 8` | `choices 11 3 -126 / widths 16 16` |
| `composition.sv` | Nested/binary/shift/condition, selected compound store, concat, pattern, replication | `composition 1123 2 40 1 / relations 1 concat 1a / patterns 14 00000002` | `composition 1142 4 20 5 / relations 0 concat 2b / patterns 25 0000000a` | `composition 1422 8 60 9 / relations 0 concat 3c / patterns 36 0000002a` |
| `runtime.sv` | Live reads, blocking and NBA capture across source changes and delay | `before 11 / captured 11 live 44` | `before 22 / captured 22 live 55` | `before 33 / captured 33 live 66` |
| `elaboration.sv` | Localparam widths and generate selection | `outer 4 f` | `typical 8 ff` | `outer 12 fff` |
| `timing.sv` | Selected delay 2/5/8 versus markers at 3/7 | `selected` | `marker3 / selected` | `marker3 / marker7 / selected` |
| `unknown.sv` | Four-state X/Z and two-state squash | `states xz 10001010` | `states zz 01000101` | `states xx 00000011` |
| `unselected.sv` | Unselected increments ignored; selected increments refuse | `unselected 0 1` | `unselected 7 0` | `unselected 0 1` |
| `unselected_math.sv` | Unselected unknown numeric calls ignored; selected calls refuse | `unselected-math 8` | `unselected-math 7` | `unselected-math 8` |
| `effects.sv` | Selected increment refuses in every mode | `effects 0 1` | `effects 0 1` | `effects 0 1` |
| `argument_context.sv` | Frontend rejects direct min/typ/max display argument; model refuses | `before 11 / captured 11 live 44` | `before 22 / captured 22 live 55` | `before 33 / captured 33 live 66` |

All reference runs exit zero. Model refusals are not agreements. Across thirty
mode/source pairs, twenty complete transcripts match both region oracles and
ten retain explicit refusals. In particular, `argument_context.sv` preserves
the exact original direct-argument form accepted by the reference and rejected
by the frontend; runnable fixtures assign the choice before displaying it.

Widths and signedness come from the bound selected subtree: `choices` checks
four-bit narrowing, signed eight-to-sixteen-bit extension and selected `$bits`
arms. `unknown` prints eight-bit four-state vectors and the corresponding
two-state conversion. `composition` prints full packed values and replication
results. `runtime` observes old NBA data and new live data after one tick.
`timing` observes only markers preceding the selected delay; `$finish` ends
the complete transcript. No output filtering, rescaling or numeric projection
is used. Unselected effects and numeric calls execute only if their arm is
chosen; the reference observations in loud modes are retained below.

Regenerate typical envelopes and check:

```sh
python3 extractors/sv/extract.py Examples/system-verilog/min_typ_max/*.sv
LEAN_NUM_THREADS=2 prlimit --as=17179869184 lake env lean -j2 Examples/system-verilog/min_typ_max/proof.lean
```

Use `--min-typ-max min` or `--min-typ-max max` to choose another mode. Only
default envelopes are committed. Nondefault envelopes record `min_typ_max`;
regeneration must replay this field. The CI-owned roundtrip harness update
has been requested; exact same-mode CLI regeneration is independently tested.

The following source-bound receipts authenticate all observations above:
version `24.03-s004`, 2026-10-20, top `top`, arguments `-ii_val` followed by
`-mindelays`, `-typdelays` or `-maxdelays`, respectively. Keys bind exact source
bytes, top and arguments. Status, stdout and provenance were checked.

| Source | SHA-256 | min receipt | typ receipt | max receipt |
|---|---|---|---|---|
| `choices.sv` | `a85302083f858d586ac7d39e2def9dba807dfbd9b97dfcddff76635eccd062f6` | `29c155322993572653288b2d` | `0728d2d4a990a029ee44f6e1` | `f8ecbddd33f9bc55c32c8243` |
| `composition.sv` | `33946782fb97af254d492cfc3e0a0a44386197a41fd7768f8cba9c7d376a849b` | `834437ae09e608cf4e3f516a` | `49c6fa3ca4f3d7e47f7dcc3b` | `92c23f461ca4ffa7833eda9c` |
| `runtime.sv` | `ccca4ce35fb7861fbe1747dfbdd8034c76d569419a600e4eec430f3ec859cb4f` | `e56338eb02d0b85ca07cbf88` | `38303d599b21911c77aab27e` | `dfbb965f73d4b4009c4a4ebe` |
| `elaboration.sv` | `1cbf484159215aafc8bcaf39fb399660dbb7c08453385e15eacb1c19a9bd6194` | `d9cd6a5899ebd26b6c53fd32` | `927a5566cea80ee8ccb9a225` | `e0d62d4a6a44ac7ca6a3e177` |
| `timing.sv` | `d5aad3f19c9ab96a87f9b901af987a5b8237892c45e208c3718b8170787e167b` | `258f925bcc219068b0fe34fc` | `4bdb569966f9172d6fd69af9` | `84c258a8c685497122270e56` |
| `unknown.sv` | `0e495a69a067340b5cf7d60d8a36aee9e4d48d21fa69ab4331fd2c0acd2ebc0e` | `d2a2a2c229d07f42ce570ff2` | `7852196ee4fbb3f239912613` | `19aadc0a96a5ff169ec1e0f3` |
| `unselected.sv` | `1b0b86e6f0dc54a2f3406ad1efd3039f810fd7722573886ef55f71d40d05c27a` | `ebb9fc95c24533527f702fe7` | `8f9dab996795162b9f1c4293` | `a9ba026a4038509a75c38516` |
| `unselected_math.sv` | `bede42e2ee0f5be2e9e80d917687aba0b532ca0afa3034bdd76c8b481f13ba0b` | `27bc1d6d1ff6423c36cf725e` | `ff52df8c8ba81fa91d0a3a78` | `b16ef82a143367f58901cac8` |
| `effects.sv` | `91dbf53d197088535f4a965c0597f873c0f274c47178054b54f8ae9861fb0d5c` | `b846aa3b0c672df23bef41ce` | `c878ad77f567fd6033c055d1` | `f657de29f809e7e78960f79e` |
| `argument_context.sv` | `a22a1fe86b7de8adcd491f88612589517c712432d020458a46c6db1313f1c5a2` | `b6b87fe63a7389a61fc12dd7` | `cf25df2003a11d9b08aed26c` | `e22d65455f2a3dfac9b4a415` |
