# Parameter-sized unpacked array port

This clean-room source exercises the IEEE 1800-2023 §23.3.3 connection of a
parameter-sized one-rank unpacked input array across a child instance. The
Slang envelope retains the actual as an empty-index `ArraySel`; canonical E
copies the native `MemState` block after checking the unpacked bounds and
converts each destination element. The receipt drives `N=2` and `N=3`, and
includes known, `x`, and `z` data rows against Icarus Verilog 13.0 and Xcelium
24.03-s004.
