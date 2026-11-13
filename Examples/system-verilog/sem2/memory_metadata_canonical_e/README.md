# Canonical-E memory metadata

This clean-room source keeps an empty input-only task and an unsized `1'bx`
assignment beside a parameter-sized one-rank memory.  The task declaration is
inert metadata and its call remains an empty statement.  The x/z marker is
retained on the source expression; the destination width supplies the
32-bit all-x value under IEEE 1800-2023 §5.7.1.

The canonical-E receipt emits two rows, both `q=xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx`.
Icarus Verilog 13.0 (`s20250103-64-gdad78d525`) and Xcelium 24.03-s004 both
match 2/2.  `NetSymbol:net-z` is intentionally still loud because the current
`PDesign` view retains only that marker's name; its structured width and
driver metadata are not yet available to this route.
