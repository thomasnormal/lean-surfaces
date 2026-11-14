# Generate-if unpacked declaration

The approved Slang envelope retains the `GenerateIf` and its parser-shaped
unpacked declaration. Canonical ingestion now admits that envelope and
retains the declaration in the active generate branch. Canonical E collects
it as one source-shaped `MemState` memory; an inactive branch contributes no
declaration.

Icarus Verilog 13.0 and Xcelium 24.03-s004 execute the two source rows
(`y=00000000`, then `y=10100101`), matching canonical E.
