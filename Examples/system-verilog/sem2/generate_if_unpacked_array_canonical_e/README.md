# Generate-if unpacked declaration wall

The approved Slang envelope retains the `GenerateIf` and its parser-shaped
unpacked declaration.  Canonical ingestion refuses the envelope with:
`GenerateIf: UnpackedDecl: unknown generate member kind "UnpackedDecl"`.

Icarus Verilog 13.0 and Xcelium 24.03-s004 execute the two source rows
(`y=00000000`, then `y=10100101`), so this is a measured loader refusal rather
than a simulator mismatch.
