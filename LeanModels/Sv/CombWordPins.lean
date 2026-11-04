import LeanModels.Sv.CombProcTactic

/-!
# Axiom pins of the word-level lemma set (WP-B2, gates 1 to 4, and `*`)

`#pin_axioms` (defined in `CombProcEq.lean`, downstream of the lemmas it checks) is an error unless every named
constant depends on at most `propext`, `Classical.choice` and `Quot.sound`. The lemmas below are the ones WP-B2
added to `CombWord`, `CombView`, `CombViewThm`, `CombEqBase`, `CombEqShape` and `CombEqThm`. This module is imported
by `Examples/system-verilog/comb_word/comb_proof.lean`, so every build of that example checks the pins.
-/

#pin_axioms LeanModels.Sv.XF.val_congr_lt LeanModels.Sv.XF.val_zext LeanModels.Sv.XF.val_testBit
  LeanModels.Sv.XF.toNat_bv LeanModels.Sv.XF.bv_congr_lt LeanModels.Sv.XF.bv_zext LeanModels.Sv.XF.bv_addBits
  LeanModels.Sv.XF.bv_subBits LeanModels.Sv.XF.addBits_congr LeanModels.Sv.XF.subBits_congr

#pin_axioms LeanModels.Sv.CombView.ctxOpW_cases LeanModels.Sv.CombView.selfOpW_cases
  LeanModels.Sv.CombView.rdsOfW?_binary LeanModels.Sv.CombView.rdsOfW?_unary
  LeanModels.Sv.CombView.rdsOfW?_ternary LeanModels.Sv.CombView.rdsOfW?_reduce
  LeanModels.Sv.CombView.rdsOfW?_resize LeanModels.Sv.CombView.signedCast_of_rdsW
  LeanModels.Sv.CombView.leaf_flags LeanModels.Sv.CombView.ie_addsub_cases
  LeanModels.Sv.CombView.ie_resize_cases LeanModels.Sv.CombView.inst_rdW LeanModels.Sv.CombView.rhs_ok

#pin_axioms LeanModels.Sv.CombEq.rdsLeaf_ok LeanModels.Sv.CombEq.rdsOfW?_len LeanModels.Sv.CombEq.skT_leavesW
  LeanModels.Sv.CombEq.Sk.bitC_of_selfOk LeanModels.Sv.CombEq.Sk.rmax_le LeanModels.Sv.CombEq.Sk.rok_of_width
  LeanModels.Sv.CombEq.Sk.rmax_le_width LeanModels.Sv.CombEq.Sk.widthOk_width_le LeanModels.Sv.CombEq.Sk.selfOk_of_v1
  LeanModels.Sv.CombEq.skT_resize_op LeanModels.Sv.CombEq.xf_lit_ofInt LeanModels.Sv.CombView.ie_resize_op
  LeanModels.Sv.CombView.ie_resize_op_eq LeanModels.Sv.CombView.ie_cmp_cases LeanModels.Sv.CombView.ie_cmp LeanModels.Sv.CombEq.Sk.WidthOkC.mono
  LeanModels.Sv.CombEq.Sk.WidthOk.toC LeanModels.Sv.CombEq.ie_resize_leaf LeanModels.Sv.CombEq.ie_resize_lit
  LeanModels.Sv.CombEq.ie_bin_none LeanModels.Sv.CombEq.ie_ternary_none' LeanModels.Sv.CombEq.skT_shapeC
  LeanModels.Sv.CombEq.gate_shapeC LeanModels.Sv.CombEq.rhs_shapeC LeanModels.Sv.CombEq.proc_shapeC
  LeanModels.Sv.CombEq.part_xf LeanModels.Sv.CombEq.low_xf_genC
  LeanModels.Sv.CombEq.low_xfWidthC LeanModels.Sv.CombEq.low_xfBitsC LeanModels.Sv.CombEq.skRhs_leaves
  LeanModels.Sv.CombEq.site_sk LeanModels.Sv.CombEq.eq_of_summary LeanModels.Sv.CombEq.eq_view
  LeanModels.Sv.CombEq.Sk.WidthOkC.toV1 LeanModels.Sv.CombEq.skT_v1 LeanModels.Sv.CombProc.inst_idxFreeW

/-!
Gate 3 (run-time shifts): the glue lemmas of `CombWord`, the recognizer and instantiation facts of `CombView` /
`CombViewThm`, the skeleton constructor's lemmas (`CombEqBase`), the shape and x-free arms (`CombEqShape`) and the
index-freedom of the proc chain (`CombProc`).
-/

#pin_axioms LeanModels.Sv.XF.bv_shlBits LeanModels.Sv.XF.bv_shrBits LeanModels.Sv.XF.getLsbD_signExtend_bv
  LeanModels.Sv.XF.bv_shlBits_s LeanModels.Sv.LVec.back?_ofBoolFn LeanModels.Sv.LVec.resizeSigned_ofBoolFn
  LeanModels.Sv.evals_resizeSigned

#pin_axioms LeanModels.Sv.CombView.rdsLeaf_ok' LeanModels.Sv.CombView.shOpW_cases
  LeanModels.Sv.CombView.shOpdRd?_cases LeanModels.Sv.CombView.shLeftRd?_cases LeanModels.Sv.CombView.RdOK.fitDiv
  LeanModels.Sv.CombView.RdOK.ctxTrunc LeanModels.Sv.CombView.ie_shl_form LeanModels.Sv.CombView.ie_shr_form
  LeanModels.Sv.CombView.instDiv_default LeanModels.Sv.CombView.instDiv_resize
  LeanModels.Sv.CombView.leafKind_of_leafRd LeanModels.Sv.CombView.shOpdKind LeanModels.Sv.CombView.rd_shOpd
  LeanModels.Sv.CombView.rd_shLeft LeanModels.Sv.CombView.instDiv_sresize LeanModels.Sv.CombView.RdOK.resizeSigned
  LeanModels.Sv.CombView.shSign_shr

#pin_axioms LeanModels.Sv.CombEq.shOpd_len LeanModels.Sv.CombEq.shLeft_len LeanModels.Sv.CombEq.skT_sh
  LeanModels.Sv.CombEq.shOpd_leaves LeanModels.Sv.CombEq.ie_shl_some LeanModels.Sv.CombEq.ie_shr_some
  LeanModels.Sv.CombEq.ie_shl_none LeanModels.Sv.CombEq.ie_shr_none LeanModels.Sv.CombEq.divW_eq_selfW
  LeanModels.Sv.CombEq.shOpd_shape LeanModels.Sv.CombEq.xf_shLeft LeanModels.Sv.CombEq.xf_shCore
  LeanModels.Sv.CombEq.xf_shFin LeanModels.Sv.CombEq.sext_congr LeanModels.Sv.CombEq.shrBits_zext
  LeanModels.Sv.CombProc.idxFree_fitDiv LeanModels.Sv.CombProc.idxFree_ctxTrunc
  LeanModels.Sv.CombProc.idxFree_shOpd LeanModels.Sv.CombProc.idxFree_shLeft

/-!
Gate 3b (concatenation operands): the glue of `CombWord`, the parts lemmas that moved down to `CombEqBase` (they are
needed by the leaf-count and leaf lemmas of the word-level fragment) and the two `fragW` projections.
-/

#pin_axioms LeanModels.Sv.XF.ite_zext LeanModels.Sv.XF.bv_pad LeanModels.Sv.XF.bv_cat2
  LeanModels.Sv.CombView.selfOpW_false_of_ctx
  LeanModels.Sv.CombView.selfOpW_false_of_sh LeanModels.Sv.CombEq.Sk.rmax_cat LeanModels.Sv.CombEq.fragW_bin_ctx LeanModels.Sv.CombEq.fragW_bin_self
  LeanModels.Sv.CombEq.rdsLeaf_cases LeanModels.Sv.CombEq.partRd?_of_ne LeanModels.Sv.CombEq.partsT_lit
  LeanModels.Sv.CombEq.partsT_of_ne LeanModels.Sv.CombEq.partsT_leaves LeanModels.Sv.CombEq.partsRd_len

/-!
Gate 4a (rows and part selects): the legacy-select reclassification (`bitAcc`) with its inversions, the element-width
facts of the instantiation environment, and the instance lemmas of the legacy part select (read, self-width, target).
-/

#pin_axioms LeanModels.Sv.CombView.bitAcc?_cases LeanModels.Sv.CombView.DeclT.elemW_vals
  LeanModels.Sv.CombView.ctxElemsRow LeanModels.Sv.CombView.ctxElemsOne LeanModels.Sv.CombView.inst_partSel
  LeanModels.Sv.CombView.selfWidth_partSel LeanModels.Sv.CombView.instLhs_partSel
  LeanModels.Sv.CombView.tgtOf?_cases LeanModels.Sv.CombView.inst_leaf LeanModels.Sv.CombView.instLhs_acc
  LeanModels.Sv.CombEq.leaf_eq LeanModels.Sv.CombEq.instLhs_acc_w LeanModels.Sv.CombEq.divW_eq_selfW

/-!
Gate 4b (a genvar as the amount of a shift): the recognizer's amount case and the constants-of-the-instance names
(`R`: `PExpr.cnames`, `TSite.cnames` in `TSite.affNames`, `site_cn`), the amount lemmas (reads, lengths, leaves,
shape, index-freedom), the leaf guard of the proc chain, and the word-level theorems that gained the scope hypothesis.
-/

#pin_axioms LeanModels.Sv.CombView.shAmtRd?_cases LeanModels.Sv.CombView.cnames_binary_l
  LeanModels.Sv.CombView.cnames_binary_r LeanModels.Sv.CombView.cnames_unary LeanModels.Sv.CombView.cnames_reduce
  LeanModels.Sv.CombView.cnames_resize LeanModels.Sv.CombView.cnames_ternary_c LeanModels.Sv.CombView.cnames_ternary_t
  LeanModels.Sv.CombView.cnames_ternary_e LeanModels.Sv.CombView.cnames_amount LeanModels.Sv.CombView.rd_shAmt
  LeanModels.Sv.CombView.inst_rdW LeanModels.Sv.CombView.rhs_ok LeanModels.Sv.CombView.site_desc
  LeanModels.Sv.CombView.site_cn LeanModels.Sv.CombView.site_co LeanModels.Sv.CombEq.shAmt_len LeanModels.Sv.CombEq.shAmt_leaves
  LeanModels.Sv.CombEq.fragOkL_spec LeanModels.Sv.CombEq.fragOkL_co LeanModels.Sv.CombEq.shAmt_shape
  LeanModels.Sv.CombEq.skT_shapeC LeanModels.Sv.CombEq.gate_shapeC LeanModels.Sv.CombEq.rhs_shapeC
  LeanModels.Sv.CombProc.idxFree_shAmt

/-!
Gate 4c (replication `{N{x}}` of a sized literal or one access): the recognizer's cases (`repArgRd?_cases`,
`repRd?_cases`, `notWhole_ok`), the instantiation of a replication and its self-width (`repl_facts`, `inst_repl`,
`selfWidth_repl`, `rd_repl`, `inst_partsW`), the shape of a replication and of the parts of a word-level concatenation
(`repl_shape`, `parts_shapeW`, `rep_bundle`), the x-free layer of a part (`part_low`), the guarded non-negativity of the
counts (`InRangeObl.rc_all`, `site_co`), and the index-freedom of the proc chain's readers.
-/

#pin_axioms LeanModels.Sv.CombView.repArgRd?_cases LeanModels.Sv.CombView.repRd?_cases LeanModels.Sv.CombView.notWhole_ok
  LeanModels.Sv.CombView.repl_facts LeanModels.Sv.CombView.inst_repl LeanModels.Sv.CombView.selfWidth_repl
  LeanModels.Sv.CombView.rd_repl LeanModels.Sv.CombView.inst_partsW LeanModels.Sv.CombView.Summary.InRangeObl.rc_all
  LeanModels.Sv.CombEq.repl_shape LeanModels.Sv.CombEq.parts_shapeW LeanModels.Sv.CombEq.rep_bundle
  LeanModels.Sv.CombEq.part_low LeanModels.Sv.CombEq.partsT_leavesW LeanModels.Sv.CombEq.partsRdW_len
  LeanModels.Sv.CombProc.inst_repl_idxFree LeanModels.Sv.CombProc.inst_repRd_idxFree
  LeanModels.Sv.CombProc.inst_parts_idxFreeW LeanModels.Sv.CombView.Summary.inRangeObl_of_plain

/-!
Gate 4c (the heartbeat budget): the constants of a site, forced at recognition time and checked in one traversal.
-/

#pin_axioms LeanModels.Sv.CombView.consts_eq LeanModels.Sv.CombView.noConst_spec LeanModels.Sv.CombView.flatMap_nil_of_all
  LeanModels.Sv.CombView.forceC_eq LeanModels.Sv.CombView.forceSite_eq

/-!
`*` (a product with a signal-access factor, `sigOpd`): the glue and the value lemma of `CombWord`, the recognizer's
inversion, the failure of the constant evaluation on such a product and the instance lemmas it gives (`CombViewThm`).
-/

#pin_axioms LeanModels.Sv.XF.bv_mulBits LeanModels.Sv.XF.val_mulBits LeanModels.Sv.XF.mulBits_congr
  LeanModels.Sv.CombView.rdsOfW?_mul LeanModels.Sv.CombView.evalAt_sigOpd LeanModels.Sv.CombView.isInt_sigOpd
  LeanModels.Sv.CombView.evalInt_mul_sig LeanModels.Sv.CombView.ie_mul_cases LeanModels.Sv.CombView.instExpr2_mul
  LeanModels.Sv.CombView.ie_mul_none

/-!
`$clog2` localparams (`CE.clog2`): the two facts about the ceiling logarithm the obligations of a `$clog2`-bounded loop read.
-/

#pin_axioms LeanModels.Sv.CombView.clog2_le LeanModels.Sv.CombView.le_two_pow_clog2
