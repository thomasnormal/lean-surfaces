# Selected compound assignments

IEEE 1800-2023 §10.4.1/§11.4.1: one blocking read/modify/write, preserving the
complete bound expression and capturing dynamic addresses once. See
[the contract](../../../docs/sv-compound-assignments.md).

`selected_proof.lean` proves address capture, live selected reads, blocking
storage preserving the pending NBA queue and output, unknown no-store, and
partial-range refusal against the actual parsed delayed assignment in
`runtime.sv`. Its receipt checks all seven successful sources under both
region oracles, six through the time-zero runner, and the four loud sources.
The earlier `proof.lean` and `updates.sv.json` retain the scalar-update theorem.

| Source | Coverage | Reference stdout |
|---|---|---|
| `scalars.sv` | All 12 operators, wider RHS narrowing, signed division/remainder/shift | `wide 8 / signed -42 -1 / operators 13` |
| `arrays.sv` | Descending unpacked cells, live selectors, signed shifts | `arrays 3 42 22 15 e0 48` |
| `windows.sv` | Packed bits and windows, unknown/wholly-invalid selectors | `windows d2cc / invalid d2cc` |
| `members.sv` | Nested packed union/struct member bounds and copyback | `members 36e2 / invalid 36e2` |
| `two_state.sv` | X/Z conversion and nonrepresentable array labels | `two-state 3ae2 a b` |
| `indices.sv` | Negative array bounds, signed one-bit selector, X selector | `indices 10 23` |
| `runtime.sv` | Live selection, prior NBA, delayed blocking update | `before a3 / after 30` |
| `effects.sv` | Selector/RHS effects; model refuses | `effects 01 3` |
| `dynamic_rhs.sv` | Invalid target still evaluates unresolved RHS; model refuses | `unresolved 10 20` |
| `partial_windows.sv` | Partial packed range; model refuses disputed copyback | `windows d2cc / clipped d2cc` |
| `partial_members.sv` | Partial member range; model refuses disputed copyback | `members 36e2 / upper-clip 36e2 / lower-clip 36e2 / invalid 36e2` |

Reference status is zero for every row. Reference success on a loud source
is not model agreement. The partial-range sources originally differed under
both model scheduling orders: clipped windows gave `12cf` instead of reference
`d2cc`; member updates gave `3622`, then `3722`, instead of reference `36e2`.
Those exact sources remain in this directory, and now exercise the explicit
partial-range refusal. Ordinary selected-assignment clipping is unchanged.

Regenerate and check from the repository root (use the project's resource
limits when invoking Lean):

```sh
python3 extractors/sv/extract.py Examples/system-verilog/compound_assignments/*.sv
lake env lean Examples/system-verilog/compound_assignments/selected_proof.lean
```

The following source-bound independent receipts produced the observations
above; top `top`, arguments `["-ii_val"]`, simulator version `24.03-s004`,
2026-10-20. Keys are derived from exact source bytes, top and arguments.

| Source | SHA-256 | Receipt |
|---|---|---|
| `scalars.sv` | `6c8e2f06a4e96bc58f30a5ad7afa88f914626715d15987bebc30aa22d54508a1` | `3b0da8567885b6e7b1c9d487` |
| `arrays.sv` | `82132abad52f7ceec8fe2e1dac8d13e053b63df7c1bf1d89e332c7049f9d1164` | `54d45c124aece58b6e11c5b6` |
| `windows.sv` | `1bf58671eff37bd902e564a4289f17b588059bb99704f722a7305457d1c89d83` | `6056c0c43fe579703fb21158` |
| `members.sv` | `849dd5b286e59718fa065ce0192826d8928c2a71a158c3ddc484de8cdd58611f` | `5100bbc95f5e99e41e34cdb1` |
| `two_state.sv` | `17728831da41182dc30a11e5297aa87f5c4a92d2520348ec1bfd5f76e77df2e4` | `03628779cd44cd176d4fac09` |
| `indices.sv` | `eb7b2c9ae131bd1f86bd7d2f96dbd32c51de77804ae777a595895554e919cee9` | `e34fc1a81396d088b6247fab` |
| `runtime.sv` | `d97828a9ff0515f62728763d9d6590bbd64ca113688b61f6e339b90206c6f172` | `bd25eca831cc5c3fcf21bdce` |
| `effects.sv` | `9eface904611c385631bb770add88214e30f90b309dd9613b736d2d55907aea1` | `325bc16153eb77200def554d` |
| `dynamic_rhs.sv` | `33d40cc91f06a0b150bf920437bcd24174aa7bb224deeb11868c13f0659308ec` | `4e23194c885816e1b7f1c595` |
| `partial_windows.sv` | `4c856d59fe8efb532ebf8e35877a16ab23dd9d1a24f478661739930681ec7c4d` | `c46010c8c83d0580650545ec` |
| `partial_members.sv` | `6cb037dae4a6f1cadba9a4a3d2196e877b9fb61efeb116150faf1160d0e736f5` | `8f68759e3e29235e636695f0` |
