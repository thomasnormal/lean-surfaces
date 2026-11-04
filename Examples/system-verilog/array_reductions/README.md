# Fixed-array reduction methods

IEEE 1800-2023 §7.12/§7.12.3. See [the contract](../../../docs/sv-array-reductions.md).

Six sources match complete independent transcripts under both tested region
oracles. `effect` and `iterator_index` retain explicit model refusals; their
successful independent runs are not agreements. No transcript filtering,
projection or time rescaling is used.

| Source | Complete independent stdout |
|---|---|
| `automatic.sv` | `automatic 5 -6` |
| `certificate.sv` | `certificate 1` |
| `effect.sv` | `effect 9 3` |
| `iterator_index.sv` | `index 20` |
| `nested.sv` | `nested 20 100 200 / live-with 23` |
| `rules.sv` | `sum 4 20 50 / product 10 90 / signed -6 -6 / bits 0x0x 1111 0x0x / map 2 3` |
| `structure.sv` | `instances 11 8 / fields 6 80` |
| `timing.sv` | `snapshot 9 26 9 / live 34 24` |

`rules` covers all five methods, intrinsic overflow, widened `with` expressions,
signed negatives, named iterators, surrounding variables and X/Z propagation.
`structure` covers independent instance arrays and packed fields. `automatic`
retains a local array through a delay. `nested` binds two iterators independently
and observes live surrounding storage. `timing` covers array copies and NBA
capture followed by later writes. `certificate` binds the four kernel theorems
to actual parsed source and copyback.

The theorems establish current-cell reads, four-bit modular addition for all
`BitVec 4` inputs, result copyback preserving pending work/output and unchanged
source cells. The proof receipt also executes all six successful programs under
both orders and checks the two refusal boundaries.

Every independent invocation uses top `top`, version `24.03-s004`, date
2026-10-20, arguments
`["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"]`.
Source bytes, key, status, complete stdout and provenance were authenticated.

| Source | SHA-256 | Receipt |
|---|---|---|
| `automatic.sv` | `0a84696634115fb9899678a93e4b0b1fa0aad2bb09d43e7c804c74a4a4e15d2f` | `20342820699402559b0932d2` |
| `certificate.sv` | `2a712f2333e66dde2a1f17f0adc36cf244cab94b273564c85ff2cc389c7d2397` | `27f88ac7e35aa6420a9a16cc` |
| `effect.sv` | `49d0492c529634c3636ea44e8a499623994c947aa977dc5b32b85f23113165e5` | `358a4cf082915bd4bd384e91` |
| `iterator_index.sv` | `48e2c7d3c948b0a0a622930ac5048ccf17d094c833bc484ef9a7306ae2529e4c` | `1bcd6d321b3b28a57409497c` |
| `nested.sv` | `a9755dd4e0b09ea7a29a0c9aedf91444e42681a4791970e20e605366eeeeab57` | `19fe8d2083e458b2a9c0abe2` |
| `rules.sv` | `6fa2f5b8b605ba88d7424382532150b6edc04ad8ce80e63f83277149b05f0477` | `d98ddf292ef8f4197be1b0bd` |
| `structure.sv` | `7e29e2cf3e0decae5679f41ba0cec29525b6e3b44b40a502fbc5e1fbde6ce557` | `bf01345e37e9a61d5be348c4` |
| `timing.sv` | `b8e49ae2b87e6ea172fe13f2d3f219ae83a6695cb0d61dc244c1b390b4f44cf0` | `5560a8c58d2746d40128c5b3` |

Regenerate and check:

```sh
python3 extractors/sv/extract.py Examples/system-verilog/array_reductions/*.sv
LEAN_NUM_THREADS=2 prlimit --as=17179869184 lake env lean -j2 Examples/system-verilog/array_reductions/proof.lean
```
