# Unifying E-core-0

E-core-0 has one authority: `LeanModels/Sv/Kernel/Core0E.lean`. It owns the
elaborated store, process-atomic step, startup, sensitivity, and slot closure.
`Core0.lean` must become an import compatibility path and must define no second
`Elab`, `Config`, `step`, or `SlotCloses`. `Obs_E0.lean` is the corresponding
observation entry point; `Core0Obs.lean` is the transport layer for existing
R-COMB proofs, not another E backend.

The migration is staged so each boundary remains checkable:

1. Port `Core0Comb` to the `Core0E` declarations while retaining its equation
   transport imports (`Comb2`, `Comb2Term`, and `Spec2`) only for refinement
   theorems. Its settle invariant must state the startup readiness premise that
   E actually provides. In particular, retained implicit event processes start
   waiting; they cannot be silently included in an assign/`always_comb` settle
   proof. The assign-only profile supplies the premise, and event-controlled
   processes remain outside that profile until their own transport theorem.
2. Port `Core0Proc` and `Core0Obs` on that single kernel. The existing body
   transport continues to use the frozen `Stmt2` lowering, while observations
   use the reducible `Obs_E0` wrapper.
3. Keep `Core0ObsWin`, `Core1Obs`, and the E executors on the same imports, then
   remove the old declarations from the compatibility path and build the full
   SV chain.

The exploratory alias build reached the first boundary: after replacing the
old `Core0` body with an import of `Core0E` plus the legacy transport imports,
`Core0Comb` had only the startup-readiness mismatch and one missing explicit
`Proc0.implicit` case. This note records the design choice so the next patch
does not reintroduce a second kernel or turn a retained event process into a
combinational process.
