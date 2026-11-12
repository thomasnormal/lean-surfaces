/-!
This is a loud-refusal receipt. `load_design_sv2` intentionally rejects the
source envelope at both the default point and N = 8 with
`Constant:untyped-width`: IEEE 1800-2023 §§6.20.2 and 11.6.1 leave the
self-determined width observable, while Icarus Verilog 13.0 and Xcelium
24.03-s004 disagree on the lossless intermediate width. The differential
rows and exact refusal are checked by `check.py`.
-/
#guard true
