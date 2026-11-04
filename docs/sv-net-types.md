# Net type boundary — retained net storage and struct identity

`NetSymbol:type` marks a net declaration whose data type or storage shape is
outside the legacy net representation. Fixed unpacked net arrays, packed
struct nets and generated multidimensional net arrays need net-level driver
storage distinct from procedural variables. A typedef's struct initializer is
also ignored for a net, while the net remains undriven until a driver acts.

## Why these net types remain loud

IEEE 1800-2023 §§6.7.1, 7.2.2, 27.4 and 37.2 distinguish net drivers from
variable stores, preserve packed-struct field identity and apply special
initialization rules to nets. The legacy envelope has no aggregate net driver
set or multidimensional net array store. No net is flattened to a scalar,
copied into a variable or assigned a typedef default, and no second scheduler
or driver resolver is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NetSymbol:type` in **24** files; **7**
are sole refusals and 17 co-occur. The independent read-only repricer finds
**7** unsupported net spans:

| source shape | spans | files |
|---|---:|---:|
| multidimensional net array | 4 | 4 |
| packed-struct net | 2 | 2 |
| generated net array | 1 | 1 |
| typedef-struct net | 1 | 1 |

The array labels overlap. Reproduce the table with:

```text
python3.9 extractors/sv/net_type_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
shapes without allocating net drivers or flattening struct fields.
