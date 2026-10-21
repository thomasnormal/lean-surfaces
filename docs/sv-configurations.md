# Configurations — repricing boundary

`ConfigBlockSymbol` represents an IEEE configuration declaration. A
configuration is elaboration-time design selection and binding information,
not a procedural statement. Its `design` clause selects one or more top cells;
`default`, `cell` and `instance` clauses then choose libraries, replacement
cells or sub-configurations. `use` bindings, hierarchical instance paths and
configuration localparams all affect the design before simulation starts.

## Why configurations remain a boundary

The `sv-0.1` envelope has a single-file, single-top-module loader. It has no
library namespace, multi-file cell registry, configuration-rule precedence,
sub-configuration resolution or elaboration-time parameter environment. A
configuration cannot be represented by dropping its declaration or by running
the first module: that can select a different top, bind a different cell, or
leave a rule's parameter and library effects invisible. Compile-error corpus
rows also retain their frontend diagnostics rather than becoming a partial
configuration.

Adding one special case for a default library would still be unsound. IEEE
rule matching is ordered and hierarchical: an instance rule can override a
cell rule, a `use` clause can select a library-qualified cell or configuration,
and localparams can participate in the selected design. The public tier keeps
the whole construct loud until a typed elaboration and library model can call
the existing module loader. No second elaborator or ad-hoc library resolver is
introduced.

## 2026-10-21 census and decision

The fresh 22,043-path census records `ConfigBlockSymbol` in **271** files:
**148** are configuration-only and **123** co-occur with another wall. The
configuration-only files contain **166** config blocks; **17** files contain
more than one block. Their syntax has **159** design clauses naming **168**
top cells, while seven negative/diagnostic blocks have no design clause. The
rules and local storage are:

| clause shape | instances | files |
|---|---:|---:|
| `default liblist` | 145 | 127 |
| `cell liblist` | 16 | 14 |
| `cell use` | 7 | 7 |
| `instance liblist` | 23 | 18 |
| `instance use` | 35 | 33 |
| config `localparam` declarations | 5 | 4 |

The clause rows overlap within a file. No configuration shape is independently
admissible because every shape changes elaboration-time binding or top
selection. Reproduce the table with:

```text
python3.9 extractors/sv/config_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its counts are telemetry for the boundary, not a configuration
evaluator.
