# Unreferenced package subroutines

The package declares an effectful task and a function, but no elaborated call
refers to either one. SystemVerilog declarations do not execute their bodies,
so the self-check surface erases both and emits `PASS`. A package routine that
is called (including through an import) remains at the existing callable
boundary.
