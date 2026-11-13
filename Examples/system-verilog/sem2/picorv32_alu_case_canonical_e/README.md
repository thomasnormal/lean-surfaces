# Canonical E case body

This clean-room body follows PicoRV32's ALU compare/output process shape:
source-shaped `always_comb`, two `case (1'b1)` statements, parameter-controlled
case items, and unsized x initialization. It is executed through the ordinary
canonical E memory family; no whole-core timing or theorem is claimed.
