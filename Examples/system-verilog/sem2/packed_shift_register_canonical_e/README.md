# Packed shift register

This clean-room source exercises a parameter-width packed shift register with
an NBA whose concatenation reads a packed part-select. The ordinary canonical
E route runs `N=4` and `N=8`, including the first x state, known bits, x/z clock
and data samples, against Icarus Verilog 13.0 and Xcelium 24.03-s004.
