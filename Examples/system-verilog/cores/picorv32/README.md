# PicoRV32 R2 integration status

PicoRV32 is the first R2 candidate selected by the admission census.  The
source is YosysHQ's `picorv32` repository at commit
[`ef203c2b0a3fb793280f5114941416c425c5b461`](https://github.com/YosysHQ/picorv32/commit/ef203c2b0a3fb793280f5114941416c425c5b461),
under the ISC license (`COPYING`).  The pinned source tree was cloned
read-only; no RTL adaptation was made.

The current symbolic envelope was generated from the single upstream
`picorv32.v` source with:

```text
python3 extractors/sv/extract.py --top picorv32 \
  -o /tmp/picorv32-ls-current.sv.json /tmp/picorv32-ls/picorv32.v
```

Its SHA-256 is
`009cc39591b3fcb1c88403ca44f822cb1854d2ebc0b5c728c7cade06a2e47b1b` and its
size is 3,178,052 bytes.  The envelope has one module, 26 parameters, 216
declarations after parsing, 43 process entries and three generate entries.

At the pinned default parameter point, the loader declaration succeeds, but
the semantic family is loud:

```text
picorv32_current.sem defaults: hasUnsupported = true
unsupported "Instantiate"
  "decl 'cpuregs': unpacked array storage outside E (UnpackedDecl:memory)"
```

The default argument list, in source order, is
`[1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
4294967295, 0, 16, 4294967295]`.  The source envelope contains 70 static
unsupported nodes; the most common classes are unsized/XZ parametric literals
(16), call expressions (13), width conversions (11), net-z ports (8), and
assignment targets (6).  These counts are telemetry, not admitted semantics.

The existing one-rank memory adapter can inspect the same `PDesign`, but its
current source-shaped route reports the next generic wall before constructing a
memory design:

```text
memory cycle route does not yet admit generate members
```

This packet therefore does not claim an R1 refinement theorem for PicoRV32.
The exact memory wall is already requested from the owner lane in
`/var/tmp/thomas-ahle/fleet2/inbox/ls-sv.md` (the 2026-11-05 R2 request and
the parameter-sized-array follow-up).  Once that generic route is integrated,
the generated members and the remaining source-shaped process forms must be
re-measured before core-specific proof glue is added.

