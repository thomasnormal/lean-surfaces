/-
sunfish pin file: the G1 dirty-name census on the shipped file, the
pass-3 module-init capstone (the padding loop's `pst`, `K_MID`/`K_END`)
and `Position.value()` — kernel-evaluated CPython-derived pins.

Part of the pass-7 SPEC-POLE SPLIT (docs/backlog.md §Pass 7): the
program and shared probe defs come from `pins_common.lean` — after an
envelope re-extraction, edit THAT file (the JSON trap note there); this
file rebuilds through the import.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_init

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

/-! ### The G1 dirty-name pass on the shipped file (2026-08-09)

Before it, `import time` on line 12 poisoned EVERY module global and
`Position.gen_moves` refused at `directions[p]`. Poisoning is now
per-name, so the census below is the load-bearing new fact and is pinned
here rather than described: `time` poisoned (bound by CPython, so loud —
never a fake `NameError`); `count` absent, resolving to the model's
`itertools.count`; `piece`/`pst` valued, then the
`for k, table in pst.items()` loop poisoning `pst` (twice — one per
subscript store), `padrow`, `table`, `k`, so the #158 one-liner
`K_MID, K_END = pst["K"], tuple(…)` — ONE tuple-target assign now —
stays statically poisoned (both names; the tuple-target census lists
`K_END` before `K_MID` in the fold's push order); `A1/H1/A8/H8`,
`initial`, `N/E/S/W` and the search constants resolve STATICALLY
(heap-pure literals survive the pass-3 DIVERGED discipline);
`directions` (a dict display — a ref) and `MATE_LOWER/MATE_UPPER`
(heap reads of `piece`) sit AFTER the first exec-attempted statement
(the padding loop, line 78), so pass 3 moves them to the LIVE VIEW —
statically poisoned here, valued in `initWorld`'s globals below, same
values, one heap. `opt_ranges` (a keyword call) and `hist` (a
constructor call) are out-of-tier right-hand sides. (`__version__` is
gone — #158 folded it into the `version` literal.) Reverse order =
source order. -/

#guard ((moduleGlobals sunfish).1.map (fun p => (p.1, p.2.isSome))).reverse ==
  [("time", false), ("version", true),
   ("piece", true), ("pst", true), ("pst", false), ("pst", false),
   ("padrow", false), ("table", false), ("k", false),
   ("K_END", false), ("K_MID", false),
   ("A1", true), ("H1", true), ("A8", true), ("H8", true),
   ("initial", true), ("N", true), ("E", true), ("S", true), ("W", true),
   ("directions", false), ("MATE_LOWER", false), ("MATE_UPPER", false),
   ("QS", true), ("QS_A", true), ("EVAL_ROUGHNESS", true),
   ("TABLE_SIZE", true), ("opt_ranges", false), ("hist", false)]

/-! The live view serves what the static table ceded (same values — the
fold step runs on the live state, so `directions` is the same dict shape
at a live address and the MATE window the same ints). -/

#guard (Env.lookup (initWorld sunfish).globals "MATE_LOWER") ==
  some (RVal.int 47923)
#guard (Env.lookup (initWorld sunfish).globals "MATE_UPPER") ==
  some (RVal.int 69290)
#guard (Env.lookup (initWorld sunfish).globals "directions").isSome

/-! Every top-level statement's binding set was determined, so a missing
module name is the faithful `NameError` — the second, independent half of
the pass. (`isModuleDunder` keeps `__name__`/`__doc__`/… loud regardless:
the import machinery binds them, no statement does.) -/

#guard (moduleGlobals sunfish).2

/-! ### PASS 3 CAPSTONE: the module-init padding loop RUNS

`for k, table in pst.items(): padrow = lambda …; pst[k] = sum(…); …`
executes in the live pipeline — the dict-items shell, the module-level
zero-capture lambda rebound per iteration (its body reads `piece` and
the CURRENT `k` through the live globals at call time), the lowered
genexp of computed tuple slices, `sum(…, ())`, and `(0,)*20` padding —
so the SHIPPED `pst` materializes in the model. The values below are
CPython's own (the shipped module imported and probed; A1 = 91, H8 = 28
are real squares, 0 and 119 the padding ring). `K_MID`/`K_END` land
with it, and `Position.value()` — refused before this pass because
`pst` was poisoned — now runs on the shipped file. -/

private def pstAt (p : String) (sq : Nat) : Option RVal :=
  match Env.lookup (initWorld sunfish).globals "pst" with
  | some (.ref a) =>
    (match Heap.get? (initWorld sunfish).heap a with
     | some (.dict es _) =>
       (match dictFind es.toList (.str p) with
        | some (.tuple xs) => some (xs.getD sq .none)
        | _ => Option.none)
     | _ => Option.none)
  | _ => Option.none

#guard pstAt "P" 91 == some (.int 100)
#guard pstAt "N" 91 == some (.int 206)
#guard pstAt "N" 54 == some (.int 317)
#guard pstAt "B" 28 == some (.int 270)
#guard pstAt "R" 54 == some (.int 492)
#guard pstAt "Q" 28 == some (.int 955)
#guard pstAt "K" 91 == some (.int 60017)
#guard ["P", "N", "B", "R", "Q", "K"].all fun p =>
  pstAt p 0 == some (.int 0) && pstAt p 119 == some (.int 0)

/-! `K_MID` is the padded shipped K table; `K_END` the endgame
centralization gradient — both 120 wide, both live-view bindings from
the ONE #158 tuple-target assign, whose right-hand side runs through
the live pipeline: a subscript read of the live `pst` AND
`tuple(<genexpr@6>(range(120)))` — the drained module-scope genexp.
The #158 formula covers all 120 squares (no zero padding ring
anymore): the corner value 59870 = 60000 + 70 − 10·(11 + 9) is
CPython's own answer at 0 and 119. -/

#guard (match Env.lookup (initWorld sunfish).globals "K_MID" with
        | some (.tuple xs) => xs.size == 120 && xs.getD 95 .none == .int 60006
        | _ => false)
#guard (match Env.lookup (initWorld sunfish).globals "K_END" with
        | some (.tuple xs) =>
          xs.size == 120 && xs.getD 95 .none == .int 59990
            && xs.getD 54 .none == .int 60050
            && xs.getD 0 .none == .int 59870
            && xs.getD 119 .none == .int 59870
        | _ => false)

/-! ### `Position.value()` on the shipped file — UNBLOCKED

The move-ordering heuristic over the REAL padded tables (the values are
CPython's: 46 for the double push e2e4-shaped Move(84, 64), 42 for
Move(85, 65), 5 for the knight Move(92, 71) — the same probes
`sf_order` pinned against its oracle-generated table, now answered by
the SHIPPED file's own init). -/

private def mv (i j : Int) (prom : String) : RVal :=
  .ntuple "Move" #["i", "j", "prom"] #[.int i, .int j, .str prom]

#guard (match callIn sunfish 8192 (initWorld sunfish) "Position.value"
          #[posH 0, mv 84 64 ""] with
        | .ok _ v => v == .int 46 | _ => false)
#guard (match callIn sunfish 8192 (initWorld sunfish) "Position.value"
          #[posH 0, mv 85 65 ""] with
        | .ok _ v => v == .int 42 | _ => false)
#guard (match callIn sunfish 8192 (initWorld sunfish) "Position.value"
          #[posH 0, mv 92 71 ""] with
        | .ok _ v => v == .int 5 | _ => false)

end Examples.python.sunfish.pins_init
