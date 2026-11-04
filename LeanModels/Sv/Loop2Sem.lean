import LeanModels.Sv.Loop2Rows
import LeanModels.Sv.CombView

/-!
# `sem N` of a single-process loop design (WS3 plan item A) — *provisional over `run2`*

A flat envelope with no generate item and one `always_comb` process instantiates, at a symbolic
parameter point, to one design: its declarations, and the one process with its body instantiated
(`sem_single`). The declaration stage is NOT re-derived here: it is the comb chain's own recognizer
and its soundness lemmas (`CombView.declsOf?`, `buildDecls_summary`, `buildElems_summary`, the stage
`sv_structure`'s `sound_prefix` composes), so the two routes share one staging. The headers, the
guard, the driver rule and the tactic `sv_loop_sem` that uses `sem_single` are in `Loop2Frag.lean`.
-/

namespace LeanModels.Sv.Loop2

open CombView

/-- A parameter's value in an environment (`0` when unbound). -/
def envVal (env : IEnv) (n : String) : Int := (env.vals.lookup n).getD 0

theorem envVal_of_lookup {env : IEnv} {n : String} {v : Int} (h : env.vals.lookup n = some v) :
    envVal env n = v := by simp [envVal, h]

@[simp] theorem envVal_bindVal_ne (env : IEnv) {it n : String} (v : Int) (h : n ≠ it) :
    envVal (env.bindVal it v) n = envVal env n := by
  unfold envVal; rw [vals_lookup_bindVal_ne v h]

@[simp] theorem lookup_isSome_bindVal_ne (env : IEnv) {it n : String} (v : Int) (h : n ≠ it) :
    ((env.bindVal it v).vals.lookup n).isSome = (env.vals.lookup n).isSome := by
  rw [vals_lookup_bindVal_ne v h]

theorem toNat_natCast_add (a b : Nat) : ((a : Int) + (b : Int)).toNat = a + b := by omega

/-- **`sem N` of a single-process flat design**: the comb chain's declaration stage
(`buildDecls_summary`/`buildElems_summary` over `declsOf?`), no generate item, one `always_comb`
whose instantiated body `B` the guard admits and which passes the one-driver rule. -/
theorem sem_single {d : PDesign} {args : List Int} {env : IEnv} {sd : List DeclT} {body : PStmt}
    {B : Stmt2} {decls : List Decl}
    (harity : args.length = d.params.length) (h1 : d.paramEnv2 args = .ok env)
    (hsd : declsOf? d.decls = .ok sd) (hgen : d.generates = []) (hoth : d.others = [])
    (hproc : d.processes = [.alwaysComb body])
    (hag : (sd.flatMap DeclT.affNames).all (fun n => (env.vals.lookup n).isSome) = true)
    (hdecls : sd.map (·.toDecl (envVal env)) = decls)
    (hinst : instStmt2 (env.withDecls decls) (sd.map fun dt => (dt.name, dt.elemW (envVal env))) body
      = B)
    (hadm : B.combAdmits (fun n => (env.withDecls decls).widths.lookup n) = true)
    (hdrv : driversOk d.declNames d.inputNames [.alwaysComb B] = true) :
    d.instantiateGD2 args = ⟨d.name, decls.toArray, #[.alwaysComb B]⟩ := by
  have hag' : ∀ dt ∈ sd, ∀ n ∈ dt.affNames, env.vals.lookup n = some (envVal env n) :=
    fun dt hdt n hn => by
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
        (List.all_eq_true.mp hag n (List.mem_flatMap.mpr ⟨dt, hdt, hn⟩))
      rw [hv, envVal_of_lookup hv]
  subst hdecls
  have h4 : expandList2 (env.withDecls (sd.map (·.toDecl (envVal env))))
      (sd.map fun dt => (dt.name, dt.elemW (envVal env))) (PDesign.surfaceFuel args) d.generates =
      .ok [] := by rw [hgen]; simp
  have hi := PDesign.instantiate2_of_ok harity h1 (buildDecls_summary d.decls sd hsd env hag')
    (buildElems_summary d.decls sd hsd env hag') h4
  have hg : instProcess2 (env.withDecls (sd.map (·.toDecl (envVal env))))
      (sd.map fun dt => (dt.name, dt.elemW (envVal env))) (.alwaysComb body) = .alwaysComb B := by
    show combGuardProc _ (instStmt2 _ _ body) = _
    rw [hinst]
    exact combGuardProc_of_admits hadm
  have hp : (d.assemble2 env (sd.map (·.toDecl (envVal env)))
      (sd.map fun dt => (dt.name, dt.elemW (envVal env))) []).processes.toList = [.alwaysComb B] := by
    rw [PDesign.assemble2_processes, hproc, hoth]
    simp only [List.map_cons, List.map_nil, hg, List.append_nil]
  rw [PDesign.instantiateGD2_of_ok hi (by rw [hp]; exact hdrv)]
  simp only [PDesign.assemble2, hproc, hoth, List.map_cons, List.map_nil, hg, List.append_nil]

end LeanModels.Sv.Loop2

#pin_axioms LeanModels.Sv.Loop2.envVal_of_lookup LeanModels.Sv.Loop2.envVal_bindVal_ne
  LeanModels.Sv.Loop2.lookup_isSome_bindVal_ne
  LeanModels.Sv.Loop2.toNat_natCast_add LeanModels.Sv.Loop2.sem_single
