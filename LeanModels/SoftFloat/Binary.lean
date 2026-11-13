import LeanModels.SoftFloat.Binary.Defs
import LeanModels.SoftFloat.Binary.Nat
import LeanModels.SoftFloat.Binary.Round
import LeanModels.SoftFloat.Binary.Fields
import LeanModels.SoftFloat.Binary.Cert
import LeanModels.SoftFloat.Binary.Divide
import LeanModels.SoftFloat.Binary.Characterization
import LeanModels.SoftFloat.Binary.Tests

/-!
# `LeanModels.SoftFloat.Binary`: IEEE 754-2019 binary interchange formats on bit patterns

The bit-level layer of the family's IEEE 754 component (`docs/family-architecture.md` §3.5): formats as
(exponent width, precision) with binary16/32/64/128 as instances; encoding, decoding and classification (§3.4,
§5.7.2); the exact value (§3.3); correct rounding of an exact magnitude under the five rounding-direction
attributes (§4.3), with overflow (§7.4) and gradual underflow (§7.5); division (§5.4.1) with its special cases and
the five characterization theorems; a multiplication-and-comparison certificate for "this pattern is the correctly
rounded `N / D`" and the rounding stage of a datapath, for every format.

* `Defs` — the definitions (no proofs);
* `Nat` — pure `Nat` facts;
* `Round` — correct rounding: nearest, ties to even, the overflow threshold, scale invariance, the interval
  characterization, the declarative attributes `IsRoundedTo`;
* `Fields` — the fields of a pattern and the encoder;
* `Cert` — the certificate `certNF_iff` and the datapath rounding stage `fin_cert_abs`, `ovf_cert_abs`;
* `Divide` — `divide_table`, `certF_bridge`;
* `Characterization` — §4.3.1, §6.3, §7.2 restated for `divide` and proved; `divide_isResult`;
* `Tests` — differential rows at binary16 and binary32 (`harness/softfloat/binary_rows.py`).

It reuses SoftFloat's `RoundingMode` and `Q` and maps its formats to core's `Float.Model.Format` (`Format.toCore`).
Core Lean only (no Mathlib, no lane module). Addition, multiplication, square root and conversions go in files beside
`Divide`: `roundUnits`/`round` take any exact magnitude, and `certNF_iff`/`fin_cert_abs` any exact `N / D`.
-/
