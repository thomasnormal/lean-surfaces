import LeanModels.Core.Basic
import LeanModels.Python
-- The SystemVerilog lane. The specs under `Examples/system-verilog/` already pull the
-- core Sv chain in transitively; these imports make the whole lane (including
-- the interpreter's #guard test suite, the self-check tier, and the toggle
-- walkthrough) an explicit part of `lake build` — and therefore of CI.
import LeanModels.Sv.Tests
import LeanModels.Sv.SelfCheck
import LeanModels.Sv.ToggleExample
