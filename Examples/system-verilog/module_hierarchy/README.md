# Static module hierarchy

IEEE 1800-2023 clauses 6/23/27: independently stored concrete portless module
instances, elaborated before ordinary process execution. See
[the contract](../../../docs/sv-module-hierarchy.md).

`proof.lean` certifies the actual parsed distinct declarations and blocking/NBA
statements in `isolation.sv`: live reads, blocking storage preserving pending
work/output, sibling preservation, cross-instance NBA capture and stability
after a source change. Its receipt executes every successful new fixture to
completion under both region oracles and checks the four explicit boundaries.
The unchanged earlier `elaborated_generate/hierarchy.sv` also becomes runnable;
its own receipt now checks both oracles and time-zero execution.

| Source | Coverage | Complete independent stdout |
|---|---|---|
| `isolation.sv` | Same-definition siblings, live stores, cross-instance NBA capture | `before 11 11 / blocking 21 11 / captured 33 21` |
| `nested.sv` | Upward shared writes, deep paths, generate child and sibling read | `nested 5 02 12` |
| `arrays.sv` | Negative/descending instance bounds and independent elements | `array 11 3 3 22 / grid 3 3 3 33` |
| `locals_timing.sv` | Distinct procedural locals retained across delays and NBAs | `locals 6 6 9` |
| `shared_package.sv` | Three instances use one original package variable | `shared 3` |
| `parameters.sv` | Per-instance override widths, generated instances and fixed type queries | `parameters 4 f 8 ff 12 fff` |
| `ports.sv` | Explicit connected-port refusal | `ports 1` |
| `program_kind.sv` | Explicit module-kind refusal | `program` |
| `initializer.sv` | Explicit static-initializer order refusal | `initializer 7` |
| `timescale.sv` | Explicit differing-timescale refusal | `early / late` |
| `storage.sv` | Fixed unpacked cells, dynamic selection, compounds and packed member stores | `storage 32 32 32 13 / separate 33 22` |

All reference rows exit zero. The seven runnable sources match complete
transcripts under both execution orders. The four boundary sources remain
model refusals; their reference outputs are not agreements. The earlier
hierarchy fixture prints `instance 5` and matches both orders and time-zero
execution. No output filtering, numeric projection or time rescaling is used.

`isolation` prints eight-bit values before/after a blocking write and after
NBA commit. `nested` prints the signed 32-bit upward sum and eight-bit child
values at tick two. `arrays` prints signed 32-bit independent element values
at tick one. `locals_timing` prints locals and results at tick three.
`parameters` prints exact 4/8/12-bit widths and values. `storage` prints
eight-bit fixed cells and packed vectors, including unchanged sibling cells.
`shared_package` observes the three accumulated increments after one tick.

An initial multidimensional instance-array source was rejected by the
reference compiler as unimplemented. The exact source and failed receipt are
retained in the qualification evidence; it is not an agreement. The structural
walker has a binding-only unit for nested frontend arrays with no claimed
runtime transcript. The final runnable array fixture uses two independent
one-dimensional instance arrays.

Regenerate and check:

```sh
python3 extractors/sv/extract.py Examples/system-verilog/module_hierarchy/*.sv
LEAN_NUM_THREADS=2 prlimit --as=17179869184 lake env lean -j2 Examples/system-verilog/module_hierarchy/proof.lean
```

The following final-source independent receipts use top `top`, arguments
`["-ii_val"]`, version `24.03-s004`, 2026-10-20. Keys bind exact bytes/top/args;
status, stdout and provenance were authenticated. The last row is the unchanged
earlier source, checked again for its newly admitted behavior.

| Source | SHA-256 | Receipt |
|---|---|---|
| `isolation.sv` | `58f1de79feab7c676401bdd7ca41bf17c57efd0f772733286ba4fb545ea15f02` | `b05b086e84da0718bb4efd59` |
| `nested.sv` | `7599f454d9166acc336c927061835a147224c6799967485caabff896ae5f310d` | `2baf3fa00845f0d6726cf5e2` |
| `arrays.sv` | `2f4664d266dc515662fb9a843cfcef3d837e8c4cd3b4d2b3b07f7b3cbf0cca65` | `75385d02e64d838f328846a4` |
| `locals_timing.sv` | `88f8dd387784b7a6504f5aa8c5774bd6898ec17ed1aacb57b25b2b95810990c5` | `6056c5d8241d48f9d912f18d` |
| `shared_package.sv` | `fbefc7ee9d232cdc73f2114f0b5ba00a4d016adc92e110126f92bc5fdf7605e8` | `dc2f06ab607035ca9459bb25` |
| `parameters.sv` | `ca6bfad08382fdfd73fda6e712c4296155ea59268b7c7ed7e95fa4861a1b0350` | `c26913132f0e3cb1ae8a4313` |
| `ports.sv` | `2a3714921a7c2714392c5402a6c299262e6f2a16bed19a99cfe0762187745dad` | `f554919f814b768c951ce265` |
| `program_kind.sv` | `d1d3d64558ecc4dafe7734dcb2e0e5a0e0c307fbd59a441286dab7766d70eaa4` | `c5c847a2dc72bfe3d1b5cc96` |
| `initializer.sv` | `b2c565aa68bb9c8609deb4055fd892f7933f0b479f6318b0ee3a6ba0e7d69b9c` | `ee8714f2a4cf6e37caa01906` |
| `timescale.sv` | `23ee1928880921ed2b076a5571c852053a347937ae4d1ec9de3e0a78678c8bb3` | `0963959003dff2b501ae4b57` |
| `storage.sv` | `8cb77f64a1b76e6d308f8a65da3358ab2764afc20bbc7a4873ac8641aa0c78e7` | `9f39189729f25f270a2890d3` |
| `../elaborated_generate/hierarchy.sv` | `d66d2003bc747d98520d1f95ee3a638df1f375862085570e409bdc0bfae0badb` | `d5eafc43f849efb620a0d48c` |
