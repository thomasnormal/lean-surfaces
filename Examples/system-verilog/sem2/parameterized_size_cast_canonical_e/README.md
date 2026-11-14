# Parameterized size cast

This clean-room source exercises the IEEE 1800-2023 §§6.24 and 11.8.2
size cast `W'(x)` with a parameter-sized packed result. The ordinary canonical
E route instantiates the same source at `W=2` and `W=12`; the receipt covers
truncation, zero extension, and x/z bits against Icarus Verilog 13.0 and
Xcelium 24.03-s004.
