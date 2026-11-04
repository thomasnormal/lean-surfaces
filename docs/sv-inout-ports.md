# Inout port boundary — retained bidirectional connectivity

`PortSymbol:InOut` marks an inout port or a port declaration whose
elaboration depends on inout rules. An inout is a bidirectional net connection;
its value is resolved through the connected hierarchy. ANSI port declarations
also reset or retain type and unpacked-dimension information according to the
preceding port declaration. Generic interface ports require ANSI syntax, and
interconnect ports have their own initializer and type restrictions.

## Why inout ports remain loud

IEEE 1800-2023 §§23.2.2.2–23.2.2.4 and 25.3 require bidirectional aliasing,
net resolution, declaration-order rules and frontend diagnostics. The legacy
envelope has no port map, bidirectional driver set or generic-interface and
interconnect declaration state. A one-way input or output would change the
source, and copying a prior port's dimensions would violate ANSI reset rules.
No port is rewritten, no initializer is accepted on an illegal port, and no
second hierarchy or scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `PortSymbol:InOut` in **10** files; **9**
are sole refusals and one co-occurs. The independent read-only repricer finds
**14** unsupported port spans in the sole files:

| source shape | spans | files |
|---|---:|---:|
| generic-interface non-ANSI diagnostic | 5 | 3 |
| unpacked dimension not inherited | 2 | 1 |
| integer then signed type reset | 2 | 1 |
| packed dimension then wire reset | 2 | 1 |
| inout initializer | 1 | 1 |
| interconnect initializer | 1 | 1 |
| signed interconnect port | 1 | 1 |

Reproduce the table with:

```text
python3.9 extractors/sv/inout_port_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
shapes without resolving bidirectional drivers or inventing port declarations.
