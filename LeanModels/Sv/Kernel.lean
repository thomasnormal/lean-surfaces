import LeanModels.Sv.Kernel.Core0ObsWin
import LeanModels.Sv.Kernel.Core1Disc
import LeanModels.Sv.Kernel.Core1Obs
import LeanModels.Sv.Kernel.CoreMem
import LeanModels.Sv.Kernel.MemElab
import LeanModels.Sv.Kernel.MemProc
import LeanModels.Sv.Comb2Fuel

/-!
# E-core: the build root (`LeanModels.Sv.Kernel`)

Imports the leaves of `LeanModels/Sv/Kernel/`, so that one `lake build LeanModels.Sv.Kernel` builds
every module of it:

* `Core0ObsWin` (with `Core0WinTerm`, `Core0Win`, `Core0Obs`, `Core0Proc`, `Core0Comb`, `Core0`);
* `Core1Disc` and `Core1Obs` (with `Core1Edge`);
* `Comb2Fuel` (the `always_comb` statement fuel of D-X1f, not under `Kernel/` but WS1's).

It is imported by no existing module and is listed in `tools/check_sv_chain.sh`'s library group.
-/
