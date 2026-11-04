# Unreferenced subroutines

The module declares an effectful task and a function, but never calls either.
Declarations are inert in SystemVerilog, so the self-check surface erases them
and emits `PASS`. Referenced, recursive, DPI, and otherwise callable
subroutines remain loud until callable frames are represented.
