import LeanModels.Sv.CombEBase
import LeanModels.Sv.Pure2Adequacy
import LeanModels.Sv.Sem2Run
import LeanModels.Sv.Spec2

namespace LeanModels.Sv


/-- **A leaf process writes its one window** with the whole resized value. -/
theorem combWrite_of_window? {d : Design2} {st : SvState} {t : Lhs2} {n : String} {lo w : Nat}
    (ht : t.window? d = some (n, lo, w)) {old : LVec} (hold : SvState.lookup st n = some old)
    (v : LVec) : combWrite d st t v = SvState.set st n (old.insertAt lo (v.resizeU w)) := by
  simp only [combWrite, Lhs2.wins_of_window? ht, Win.sumWidth_cons, Win.sumWidth_nil,
    Win.placed_cons, Win.placed_nil, Nat.add_zero, SvState.writeWins_cons_some hold,
    LVec.extract_zero_of_width (LVec.width_resizeU v w)]
  rfl

/-! ## Resolving and writing a concatenated target -/

/-- A leaf target with a static window resolves to it (on a state where the
signal is bound at its declared width and the window is in range, at
positive fuel — the literal index of an element select is evaluated). -/
theorem resolveLhs2_of_window? {d : Design2} {fuel : Nat} (hf : 0 < fuel) {st : SvState}
    {t : Lhs2} {n : String} {lo w : Nat} (ht : t.window? d = some (n, lo, w)) {old : LVec}
    (hold : SvState.lookup st n = some old) (hin : lo + w ≤ old.width)
    (hdw : d.declWidth n = some old.width) :
    resolveLhs2 fuel st t = .ok (n, some (lo, w)) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  cases t with
  | ident m =>
      simp only [Lhs2.window?, Option.map_eq_some_iff, Prod.mk.injEq] at ht
      obtain ⟨dw, hdw', rfl, rfl, rfl⟩ := ht
      rw [hdw] at hdw'; cases hdw'
      simp [resolveLhs2, hold]
  | slice m lo' w' =>
      simp only [Lhs2.window?, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      rfl
  | index m idx elemW =>
      cases idx with
      | lit c =>
          simp only [Lhs2.window?, Option.map_eq_some_iff, Prod.mk.injEq] at ht
          obtain ⟨k, hk, rfl, rfl, rfl⟩ := ht
          have hr : (k + 1) * elemW ≤ old.width := by rw [Nat.succ_mul]; omega
          have hr' : (k + 1 : Int) * (elemW : Int) ≤ (old.width : Int) := by
            exact_mod_cast hr
          have hlit : evalExpr2 (f + 1) st (.lit c) = .ok c := rfl
          simp [resolveLhs2, indexInt?, Expr2.indexSigned, hold, hk, hr, hr', hlit]
      | _ => simp [Lhs2.window?] at ht
  | concat parts => simp [Lhs2.window?] at ht

/-- A leaf target resolves, as a one-leaf concatenation, to its window. -/
private theorem resolveConcatLhs2_leaf {d : Design2} {fuel : Nat} (hf : 0 < fuel) {st : SvState}
    {t : Lhs2} (hnc : ∀ ps, t = .concat ps → False) {n : String} {lo w : Nat}
    (ht : t.window? d = some (n, lo, w)) {old : LVec} (hold : SvState.lookup st n = some old)
    (hin : lo + w ≤ old.width) (hdw : d.declWidth n = some old.width) :
    resolveConcatLhs2 fuel st t = .ok [(n, lo, w)] := by
  rw [resolveConcatLhs2.eq_2 fuel st t hnc, resolveLhs2_of_window? hf ht hold hin hdw]
  rfl

/-- The leaf case of `resolveConcatLhs2_of_windows?`. -/
private theorem resolveConcatLhs2_of_windows?_leaf {d : Design2} {fuel : Nat} (hf : 0 < fuel)
    {st : SvState} {t : Lhs2} (hnc : ∀ ps, t = .concat ps → False) {ws : List Win}
    (h : ((t.window? d).map ([·])) = some ws)
    (hb : ∀ n lo w, (n, lo, w) ∈ ws → ∃ old, SvState.lookup st n = some old ∧
      lo + w ≤ old.width ∧ d.declWidth n = some old.width) :
    resolveConcatLhs2 fuel st t = .ok ws := by
  obtain ⟨⟨n, lo, w⟩, ht, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨old, hold, hin, hdw⟩ := hb n lo w (List.mem_singleton_self _)
  exact resolveConcatLhs2_leaf hf hnc ht hold hin hdw

mutual

/-- **Static windows resolve.** On a state where every window of the target
is bound at its declared width and in range, `resolveConcatLhs2` (at positive
fuel) returns exactly the static windows `Lhs2.windows?`, in order. -/
theorem resolveConcatLhs2_of_windows? {d : Design2} {fuel : Nat} (hf : 0 < fuel)
    {st : SvState} : ∀ (t : Lhs2) (ws : List Win), t.windows? d = some ws →
      (∀ n lo w, (n, lo, w) ∈ ws → ∃ old, SvState.lookup st n = some old ∧
        lo + w ≤ old.width ∧ d.declWidth n = some old.width) →
      resolveConcatLhs2 fuel st t = .ok ws
  | .ident n, ws, h, hb =>
      resolveConcatLhs2_of_windows?_leaf hf (fun _ h => by cases h) h hb
  | .slice n lo w, ws, h, hb =>
      resolveConcatLhs2_of_windows?_leaf hf (fun _ h => by cases h) h hb
  | .index n idx elemW, ws, h, hb =>
      resolveConcatLhs2_of_windows?_leaf hf (fun _ h => by cases h) h hb
  | .concat parts, ws, h, hb => by
      rw [resolveConcatLhs2.eq_1]
      have := resolveConcatLhs2_list_of_windows? hf parts [] ws h hb
      rwa [List.nil_append] at this
termination_by structural t => t

/-- The part-list fold of `resolveConcatLhs2_of_windows?` (accumulator
generalized). -/
theorem resolveConcatLhs2_list_of_windows? {d : Design2} {fuel : Nat} (hf : 0 < fuel)
    {st : SvState} : ∀ (parts : List Lhs2) (acc ws : List Win),
      Lhs2.listWindows? d parts = some ws →
      (∀ n lo w, (n, lo, w) ∈ ws → ∃ old, SvState.lookup st n = some old ∧
        lo + w ≤ old.width ∧ d.declWidth n = some old.width) →
      parts.foldlM (fun acc part => do
          let windows ← resolveConcatLhs2 fuel st part
          pure (acc ++ windows)) acc = .ok (acc ++ ws)
  | [], acc, ws, h, _ => by
      simp only [Lhs2.listWindows?_nil, Option.some.injEq] at h
      subst h
      simp
  | t :: ts, acc, ws, h, hb => by
      obtain ⟨a, b, ha, hbs, rfl⟩ := Lhs2.listWindows?_cons_eq_some.mp h
      rw [List.foldlM_cons, resolveConcatLhs2_of_windows? hf t a ha
        (fun n lo w hm => hb n lo w (List.mem_append_left _ hm))]
      rw [Res.ok_bind]
      show List.foldlM _ (acc ++ a) ts = _
      rw [resolveConcatLhs2_list_of_windows? hf ts (acc ++ a) b hbs
        (fun n lo w hm => hb n lo w (List.mem_append_right _ hm)), List.append_assoc]
termination_by structural parts => parts

end

/-- The width total `writeConcatLhs2` folds is `Win.sumWidth`. -/
private theorem foldl_width_eq {f : Nat → Win → Nat} (hf : ∀ n x, f n x = n + x.2.2) :
    ∀ (ws : List Win) (acc : Nat), ws.foldl f acc = acc + Win.sumWidth ws
  | [], acc => by simp
  | x :: rest, acc => by
      rw [List.foldl_cons, foldl_width_eq hf rest, hf, Win.sumWidth_cons]
      omega

/-- `writeConcatLhs2`'s worker is `SvState.writeWins` of the placed windows
(every name bound). -/
private theorem writeConcatLhs2_go_eq (repl : LVec) : ∀ (s : SvState) (rem : List Win),
    (∀ wn ∈ rem, (SvState.lookup s wn.1).isSome) →
    writeConcatLhs2.go repl s rem (Win.sumWidth rem) =
      .ok (SvState.writeWins s repl (Win.placed rem))
  | _, [], _ => rfl
  | s, (n, lo, w) :: rest, hb => by
      obtain ⟨old, hold⟩ := Option.isSome_iff_exists.mp (hb _ (List.mem_cons_self ..))
      rw [writeConcatLhs2.go.eq_2, hold, Win.placed_cons, SvState.writeWins_cons_some hold]
      simp only [Win.sumWidth_cons, Nat.add_sub_cancel_left]
      refine writeConcatLhs2_go_eq repl _ rest fun wn hwn => ?_
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hb wn (List.mem_cons_of_mem _ hwn))
      obtain ⟨x, hx, -⟩ := SvState.exists_lookup_set_insertAt hold ho (lo := lo)
        (p := repl.extract (Win.sumWidth rest) w)
      simp [hx]

/-- **`writeConcatLhs2` is a multi-window write**: on a state binding every
window's name, it writes the value resized to the total width, slice by slice
at the `Win.placed` offsets. -/
theorem writeConcatLhs2_eq {st : SvState} {v : LVec} {ws : List Win}
    (hb : ∀ wn ∈ ws, (SvState.lookup st wn.1).isSome) :
    writeConcatLhs2 st v ws =
      .ok (SvState.writeWins st (v.resizeU (Win.sumWidth ws)) (Win.placed ws)) := by
  unfold writeConcatLhs2
  rw [foldl_width_eq (fun _ _ => rfl), Nat.zero_add]
  exact writeConcatLhs2_go_eq _ st ws hb

/-! ## One comb process -/

/-- Right-hand sides of a comb design evaluate (`.ok`) on shaped states. -/
theorem CombDesign.evalPure2_ok {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) : ∃ v, evalPure2 st e = .ok v :=
  evalPure2_ok_of_wf (hd.rhsFree i t e hp)
    (fun x hx => hs.lookup_of_mem (hd.rhsDeclared i t e hp x hx))

/-- **One comb process, from an evaluated right-hand side** (any target in
profile, leaf or concatenation): the run is `combWrite`. -/
private theorem runCombProcess2_assign_of_eval {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e))
    {fuel : Nat} (hfuel : 0 < fuel) {v : LVec} (he : evalExpr2 fuel st e = .ok v) :
    runCombProcess2 fuel st (.assign t e) = .ok (combWrite d st t v) := by
  have hws := hd.windows?_of_proc hp
  have hb : ∀ n lo w, (n, lo, w) ∈ t.wins d → ∃ old, SvState.lookup st n = some old ∧
      lo + w ≤ old.width ∧ d.declWidth n = some old.width :=
    fun n lo w hm => hd.lookup_writes hs ⟨t, e, hp, hm⟩
  cases t with
  | concat parts =>
      have hres := resolveConcatLhs2_of_windows? hfuel (.concat parts) _ hws hb
      have hwr := writeConcatLhs2_eq (st := st) (v := v) (ws := (Lhs2.concat parts).wins d)
        fun wn hwn => by
          obtain ⟨n, lo, w⟩ := wn
          obtain ⟨old, hold, -, -⟩ := hb n lo w hwn
          simp [hold]
      simp only [runCombProcess2, he, Res.ok_bind, hres, hwr]
      rfl
  | _ =>
      obtain ⟨⟨n, lo, w⟩, hw, -⟩ := Lhs2.window?_of_windows? (fun _ h => by cases h) hws
      obtain ⟨old, hold, hin, hdw⟩ := hd.lookup_writes hs (Design2.writes_of_window? hp hw)
      rw [combWrite_of_window? hw hold]
      have hr := resolveLhs2_of_window? hfuel hw hold hin hdw
      simp only [runCombProcess2, he, Res.ok_bind, hr, hold]

/-- **One comb process, forward** (any target in profile). On a shaped state,
with fuel above the right-hand side's size, an assign whose right-hand side
evaluates to `v` produces `combWrite d st t v`. -/
theorem runCombProcess2_assign_write {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) {fuel : Nat} (hf : e.size < fuel) {v : LVec}
    (hv : evalPure2 st e = .ok v) :
    runCombProcess2 fuel st (.assign t e) = .ok (combWrite d st t v) :=
  runCombProcess2_assign_of_eval hd hs hp (by omega) ((evalExpr2_eq_evalPure2 hf).trans hv)

/-- **One comb process, inversion** (any target in profile, any fuel). A
successful run of an assign on a shaped state is `combWrite` of the
fuel-free value of its right-hand side. -/
theorem runCombProcess2_assign_write_ok {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) {fuel : Nat} {st' : SvState}
    (h : runCombProcess2 fuel st (.assign t e) = .ok st') :
    ∃ v, evalPure2 st e = .ok v ∧ st' = combWrite d st t v := by
  have : ∃ v, evalExpr2 fuel st e = .ok v := by
    cases he : evalExpr2 fuel st e with
    | ok v => exact ⟨v, rfl⟩
    | timeout => simp [runCombProcess2, he] at h
    | unsupported msg => simp [runCombProcess2, he] at h
  obtain ⟨v, he⟩ := this
  have hfuel : 0 < fuel := by
    cases fuel with
    | zero => simp [evalExpr2] at he
    | succ => omega
  rw [runCombProcess2_assign_of_eval hd hs hp hfuel he] at h
  cases h
  exact ⟨v, evalPure2_of_evalExpr2_ok he, rfl⟩

/-- **One comb process, forward** (a leaf target). On a shaped state, with
fuel above the right-hand side's size, a windowed assign writes the resized
value into its window: `set st n (old.insertAt lo (v.resizeU w))`. -/
theorem runCombProcess2_assign_eq {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2} {n : String} {lo w : Nat}
    (hp : d.processes[i]? = some (.assign t e)) (hw : t.window? d = some (n, lo, w))
    {fuel : Nat} (hf : e.size < fuel) {old v : LVec}
    (hold : SvState.lookup st n = some old) (hv : evalPure2 st e = .ok v) :
    runCombProcess2 fuel st (.assign t e) =
      .ok (SvState.set st n (old.insertAt lo (v.resizeU w))) := by
  rw [runCombProcess2_assign_write hd hs hp hf hv, combWrite_of_window? hw hold]

/-- `runCombProcess2_assign_eq` with the old value and the right-hand side's
value produced (they exist on a shaped state). -/
theorem runCombProcess2_assign {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2} {n : String} {lo w : Nat}
    (hp : d.processes[i]? = some (.assign t e)) (hw : t.window? d = some (n, lo, w))
    {fuel : Nat} (hf : e.size < fuel) :
    ∃ old v, SvState.lookup st n = some old ∧ evalPure2 st e = .ok v ∧
      runCombProcess2 fuel st (.assign t e) =
        .ok (SvState.set st n (old.insertAt lo (v.resizeU w))) := by
  obtain ⟨old, hold, -, -⟩ := hd.lookup_writes hs (Design2.writes_of_window? hp hw)
  obtain ⟨v, hv⟩ := hd.evalPure2_ok hs hp
  exact ⟨old, v, hold, hv, runCombProcess2_assign_eq hd hs hp hw hf hold hv⟩

/-- **One comb process, inversion** (a leaf target, any fuel). A successful
run of a windowed assign on a shaped state is the window write of the
fuel-free value. -/
theorem runCombProcess2_assign_ok {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2} {n : String} {lo w : Nat}
    (hp : d.processes[i]? = some (.assign t e)) (hw : t.window? d = some (n, lo, w))
    {fuel : Nat} {st' : SvState} (h : runCombProcess2 fuel st (.assign t e) = .ok st') :
    ∃ old v, SvState.lookup st n = some old ∧ evalPure2 st e = .ok v ∧
      st' = SvState.set st n (old.insertAt lo (v.resizeU w)) := by
  obtain ⟨v, hv, rfl⟩ := runCombProcess2_assign_write_ok hd hs hp h
  obtain ⟨old, hold, -, -⟩ := hd.lookup_writes hs (Design2.writes_of_window? hp hw)
  exact ⟨old, v, hold, hv, combWrite_of_window? hw hold v⟩

/-- After a window write, the window holds the written part (in range by the
profile). -/
theorem CombDesign.extract_written {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {n : String} {lo w : Nat} (hW : d.Writes i (n, lo, w))
    {old : LVec} (hold : SvState.lookup st n = some old) {p : LVec} (hp : p.width = w) :
    SvState.lookup (SvState.set st n (old.insertAt lo p)) n = some (old.insertAt lo p) ∧
      (old.insertAt lo p).extract lo w = p := by
  obtain ⟨old', hold', hin, -⟩ := hd.lookup_writes hs hW
  rw [hold] at hold'; cases hold'
  exact ⟨SvState.lookup_set_self _ _ _, LVec.extract_insertAt_self hp hin⟩

/-! ## A comb pass -/

/-- The empty pass is the identity. -/
@[simp] theorem combPass2_nil (d : Design2) (fuel : Nat) (st : SvState) :
    combPass2 d fuel st [] = .ok st := rfl

/-- A pass step at an out-of-range index is skipped. -/
theorem combPass2_cons_none {d : Design2} {fuel : Nat} {st : SvState} {i : Nat}
    {is : List Nat} (h : d.processes[i]? = none) :
    combPass2 d fuel st (i :: is) = combPass2 d fuel st is := by
  simp [combPass2, h]

/-- A pass step at a process runs it, then the rest. -/
theorem combPass2_cons_some {d : Design2} {fuel : Nat} {st : SvState} {i : Nat}
    {is : List Nat} {p : Process2} (h : d.processes[i]? = some p) :
    combPass2 d fuel st (i :: is) =
      (runCombProcess2 fuel st p >>= fun st' => combPass2 d fuel st' is) := by
  simp [combPass2, h]

/-- A pass step at an assign, forward (any target in profile; fuel above the
rhs size): the head process's `combWrite`, then the rest. -/
theorem combPass2_cons_write {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) {fuel : Nat} (hf : e.size < fuel) {v : LVec}
    (hv : evalPure2 st e = .ok v) (is : List Nat) :
    combPass2 d fuel st (i :: is) = combPass2 d fuel (combWrite d st t v) is := by
  rw [combPass2_cons_some hp, runCombProcess2_assign_write hd hs hp hf hv]
  rfl

/-- A pass step at a windowed (leaf-target) assign, forward (fuel above the
rhs size). -/
theorem combPass2_cons_assign {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {i : Nat} {t : Lhs2} {e : Expr2} {n : String} {lo w : Nat}
    (hp : d.processes[i]? = some (.assign t e)) (hw : t.window? d = some (n, lo, w))
    {fuel : Nat} (hf : e.size < fuel) {old v : LVec}
    (hold : SvState.lookup st n = some old) (hv : evalPure2 st e = .ok v) (is : List Nat) :
    combPass2 d fuel st (i :: is) =
      combPass2 d fuel (SvState.set st n (old.insertAt lo (v.resizeU w))) is := by
  rw [combPass2_cons_write hd hs hp hf hv, combWrite_of_window? hw hold]

/-- **Pass step inversion** (any fuel): a successful pass from a shaped state
either skipped an out-of-range index or ran the head process — an assign
whose right-hand side evaluated to `v` — as `combWrite`. -/
theorem combPass2_cons_ok {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) {fuel : Nat} {i : Nat} {is : List Nat} {st' : SvState}
    (h : combPass2 d fuel st (i :: is) = .ok st') :
    (d.processes[i]? = none ∧ combPass2 d fuel st is = .ok st') ∨
    ∃ t e v, d.processes[i]? = some (.assign t e) ∧ evalPure2 st e = .ok v ∧
      combPass2 d fuel (combWrite d st t v) is = .ok st' := by
  cases hpi : d.processes[i]? with
  | none => exact Or.inl ⟨rfl, by rw [combPass2_cons_none hpi] at h; exact h⟩
  | some p =>
      right
      obtain ⟨t, e, ws, rfl, -⟩ := hd.assign i p hpi
      rw [combPass2_cons_some hpi] at h
      obtain ⟨s1, h1, h2⟩ := Res.bind_eq_ok.mp h
      obtain ⟨v, hv, rfl⟩ := runCombProcess2_assign_write_ok hd hs hpi h1
      exact ⟨t, e, v, rfl, hv, h2⟩

/-- **Frame of a pass.** A successful pass (any fuel, any index list) from a
shaped state ends in a shaped state, and every read that overlaps no window of
a listed process sees the same thing before and after. -/
theorem combPass2_frame {d : Design2} (hd : CombDesign d) {fuel : Nat} :
    ∀ {is : List Nat} {st st' : SvState}, StateShape d st → combPass2 d fuel st is = .ok st' →
      StateShape d st' ∧
      ∀ r : ReadWin, (∀ i ∈ is, ∀ wn, d.Writes i wn → r.overlaps wn = false) → r.agree st st'
  | [], st, st', hs, h => by
      cases h
      exact ⟨hs, fun r _ => ReadWin.agree_refl _ r⟩
  | i :: is, st, st', hs, h => by
      rcases combPass2_cons_ok hd hs h with ⟨-, h⟩ | ⟨t, e, v, hp, hv, h⟩
      · obtain ⟨hs', hagree⟩ := combPass2_frame hd hs h
        exact ⟨hs', fun r hr => hagree r (fun j hj => hr j (List.mem_cons_of_mem _ hj))⟩
      · obtain ⟨hs', hagree⟩ := combPass2_frame hd (hs.combWrite t v) h
        refine ⟨hs', fun r hr => ?_⟩
        have h1 : r.agree st (combWrite d st t v) :=
          ReadWin.agree_combWrite fun wn hwn => hr i (List.mem_cons_self ..) wn ⟨t, e, hp, hwn⟩
        exact ReadWin.agree_trans h1
          (hagree r (fun j hj => hr j (List.mem_cons_of_mem _ hj)))

/-- A pass never touches an undriven signal. -/
theorem combPass2_notDriven {d : Design2} (hd : CombDesign d) {fuel : Nat} {is : List Nat}
    {st st' : SvState} (hs : StateShape d st) (h : combPass2 d fuel st is = .ok st')
    {n : String} (hn : NotDriven d n) : SvState.lookup st' n = SvState.lookup st n := by
  have := (combPass2_frame hd hs h).2 (.whole n) (fun i _ wn hW => by
    obtain ⟨m, lo, w⟩ := wn
    have hnm : n ≠ m := fun hnm => hn ⟨i, lo, w, hnm ▸ hW⟩
    simp [ReadWin.overlaps, hnm])
  exact this.symm

/-- A pass keeps the key list. -/
theorem combPass2_keys {d : Design2} (hd : CombDesign d) {fuel : Nat} {is : List Nat}
    {st st' : SvState} (hs : StateShape d st) (h : combPass2 d fuel st is = .ok st') :
    st'.map Prod.fst = st.map Prod.fst :=
  (combPass2_frame hd hs h).1.keys.trans hs.keys.symm

/-- Widths never change in a pass (`insertAt` is width-preserving). -/
theorem combPass2_width {d : Design2} (hd : CombDesign d) {fuel : Nat} {is : List Nat}
    {st st' : SvState} (hs : StateShape d st) (h : combPass2 d fuel st is = .ok st') (n : String) :
    (SvState.lookup st n).map LVec.width = (SvState.lookup st' n).map LVec.width := by
  -- the zero-width read at bit 0 sees only the width, and overlaps no write
  -- window (`Win.overlaps` would need a window starting below bit 0)
  have := (combPass2_frame hd hs h).2 (.win n 0 0) (fun _ _ wn _ => by
    obtain ⟨m, lo, w⟩ := wn
    simp [ReadWin.overlaps, Win.overlaps])
  simp only [ReadWin.agree] at this
  have h' := congrArg (Option.map Prod.fst) this
  simpa [Option.map_map, Function.comp_def] using h'

/-- **A pass completes** at any fuel above every right-hand side's size. -/
theorem combPass2_ok {d : Design2} (hd : CombDesign d) {fuel : Nat}
    (hf : ∀ (i : Nat) (t : Lhs2) (e : Expr2), d.processes[i]? = some (.assign t e) →
      e.size < fuel) :
    ∀ (is : List Nat) {st : SvState}, StateShape d st → ∃ st', combPass2 d fuel st is = .ok st'
  | [], st, _ => ⟨st, rfl⟩
  | i :: is, st, hs => by
      cases hpi : d.processes[i]? with
      | none =>
          rw [combPass2_cons_none hpi]
          exact combPass2_ok hd hf is hs
      | some p =>
          obtain ⟨t, e, ws, rfl, -⟩ := hd.assign i p hpi
          obtain ⟨v, hv⟩ := hd.evalPure2_ok hs hpi
          rw [combPass2_cons_write hd hs hpi (hf i t e hpi) hv]
          exact combPass2_ok hd hf is (hs.combWrite t v)

/-! ## Fuel for every right-hand side -/

mutual

/-- Statement fuel of an `always_comb` body: the fuel at which `execStmt2` runs a body of the
lowering's profile to completion. The same equations as `Comb2Proc`'s `Stmt2.fuelB`
(`Stmt2.combFuelB_eq_fuelB`, `Comb2Fuel.lean`), stated here so that `Process2.rhsSize` counts
it; sufficiency for `runCombProcess2` is `runCombProcess2_alwaysComb_of_combFuelB` there. -/
def Stmt2.combFuelB : Stmt2 → Nat
  | .blockingAssign _ e => e.size + 2
  | .ifStmt c t e => max (c.size + 1) (max t.combFuelB (Stmt2.optCombFuelB e)) + 1
  | .block body => Stmt2.listCombFuelB body.toList + 1
  | .caseStmt subj items dflt _ _ =>
      max (subj.size + 1) (CaseItem2.listCombFuelB (Stmt2.optCombFuelB dflt) items.toList) + 1
  | .nbaAssign _ _ => 0
  | .unsupported _ _ => 0
termination_by structural s => s

def Stmt2.optCombFuelB : Option Stmt2 → Nat
  | none => 0
  | some s => s.combFuelB
termination_by structural o => o

def Stmt2.listCombFuelB : List Stmt2 → Nat
  | [] => 1
  | s :: ss => max s.combFuelB (Stmt2.listCombFuelB ss) + 1
termination_by structural ss => ss

def CaseItem2.combFuelB : CaseItem2 → Nat
  | .mk pats body => max (Expr2.listSize pats.toList + 1) body.combFuelB
termination_by structural it => it

def CaseItem2.listCombFuelB (fd : Nat) : List CaseItem2 → Nat
  | [] => fd + 1
  | it :: rest => max it.combFuelB (CaseItem2.listCombFuelB fd rest) + 1
termination_by structural its => its

end

/-- Size of a process's right-hand side: an assign's expression size, an `always_comb` body's
statement fuel (`Stmt2.combFuelB`), `0` off-profile. -/
def Process2.rhsSize : Process2 → Nat
  | .assign _ e => e.size
  | .alwaysComb body => body.combFuelB
  | _ => 0

/-- Fuel sufficient for every right-hand side of the design (`Design2.size_lt_combFuel`) and for
every `always_comb` body of the lowering's profile (`Design2.combFuelB_lt_combFuel`; sufficiency:
`runCombProcess2_alwaysComb_of_combFuelB`, `Comb2Fuel.lean`). -/
def Design2.combFuel (d : Design2) : Nat :=
  (d.processes.toList.map Process2.rhsSize).foldr max 0 + 1

private theorem le_foldr_max {x : Nat} : ∀ {l : List Nat}, x ∈ l → x ≤ l.foldr max 0
  | a :: l, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

/-- Every right-hand side is smaller than `Design2.combFuel`. -/
theorem Design2.size_lt_combFuel {d : Design2} {i : Nat} {t : Lhs2} {e : Expr2}
    (h : d.processes[i]? = some (.assign t e)) : e.size < d.combFuel := by
  have hmem : Process2.assign t e ∈ d.processes.toList :=
    List.mem_iff_getElem?.mpr ⟨i, by rw [Array.getElem?_toList]; exact h⟩
  have := le_foldr_max (l := d.processes.toList.map Process2.rhsSize)
    (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  simp only [Process2.rhsSize] at this
  simp only [Design2.combFuel]
  omega

/-- Every `always_comb` body's statement fuel is below `Design2.combFuel`. -/
theorem Design2.combFuelB_lt_combFuel {d : Design2} {i : Nat} {body : Stmt2}
    (h : d.processes[i]? = some (.alwaysComb body)) : body.combFuelB < d.combFuel := by
  have hmem : Process2.alwaysComb body ∈ d.processes.toList :=
    List.mem_iff_getElem?.mpr ⟨i, by rw [Array.getElem?_toList]; exact h⟩
  have := le_foldr_max (l := d.processes.toList.map Process2.rhsSize)
    (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  simp only [Process2.rhsSize] at this
  simp only [Design2.combFuel]
  omega

/-- **A pass completes** at any fuel from `Design2.combFuel` on. -/
theorem combPass2_ok_of_combFuel {d : Design2} (hd : CombDesign d) {fuel : Nat}
    (hf : d.combFuel ≤ fuel) (is : List Nat) {st : SvState} (hs : StateShape d st) :
    ∃ st', combPass2 d fuel st is = .ok st' :=
  combPass2_ok hd (fun _ _ _ hp => Nat.lt_of_lt_of_le (Design2.size_lt_combFuel hp) hf) is hs

/-! ## The comb-only cycle -/

/-- `initState2` binds each declared name to its initializer, else a net to
all-z (an undriven net holds z) and any other declaration to all-x, the value
then squashed to 2-state for a 2-state declaration (`Sem2.initState2` since
ls-sv 6f146c58c, "retain undriven net z state"). -/
theorem lookup_initState2 (d : Design2) (n : String) :
    SvState.lookup (initState2 d) n =
      (d.decls.toList.find? fun dc => dc.name == n).map
        fun dc =>
          let value := dc.init.getD (if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width)
          if dc.twoState then value.toTwoState else value := by
  unfold initState2
  generalize d.decls.toList = ds
  induction ds with
  | nil => rfl
  | cons dc rest ih =>
      simp only [List.map_cons, SvState.lookup_cons, List.find?_cons, ih]
      by_cases h : dc.name = n
      · simp [h]
      · have hb : (dc.name == n) = false := by simpa using h
        simp [h, hb]

/-- The startup state has the comb shape. -/
theorem StateShape.of_initState2 {d : Design2} (hd : CombDesign d) :
    StateShape d (LeanModels.Sv.initState2 d) := by
  refine ⟨by simp [LeanModels.Sv.initState2], ?_⟩
  intro n hn
  obtain ⟨i, lo, w, hW⟩ := hn
  obtain ⟨dw, hdw, -⟩ := hd.inWidth i n lo w hW
  obtain ⟨dc, hf, rfl⟩ := Design2.declWidth_eq_some_iff.mp hdw
  have hname : dc.name = n := by simpa using List.find?_some hf
  have hmem := List.mem_of_find?_eq_some hf
  let value := dc.init.getD (if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width)
  have hw0 : value.width = dc.width := by
    cases hi : dc.init with
    | none =>
      change (dc.init.getD (if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width)).width = dc.width
      rw [hi]
      cases hnet : dc.isNet <;> simp [hnet, LVec.replicate, LVec.xVec, LVec.width]
    | some v => simp [value, hi, hd.initWidth n ⟨i, lo, w, hW⟩ dc hmem hname v hi]
  refine ⟨if dc.twoState then value.toTwoState else value, by rw [lookup_initState2, hf]; rfl, ?_⟩
  rw [hdw]
  by_cases h2 : dc.twoState = true
  · simp [h2, LVec.toTwoState, LVec.width] at hw0 ⊢
    exact hw0.symm
  · simp [h2, hw0]

/-- Input names are declared names. -/
theorem Design2.mem_names_of_mem_inputNames {d : Design2} {n : String}
    (h : n ∈ d.inputNames.toList) : n ∈ d.decls.toList.map Decl.name := by
  simp only [Design2.inputNames, Array.toList_filterMap, List.mem_filterMap] at h
  obtain ⟨dc, hdc, hf⟩ := h
  split at hf
  · cases hf; exact List.mem_map.mpr ⟨dc, hdc, rfl⟩
  · cases hf

/-- On a design whose input declarations are all 4-state, `applyInputs2` is
the plain walk over the input names (the stimulus value stored verbatim): the
squash of a 2-state input is the only difference from the pre-2-state
definition. -/
theorem applyInputs2_eq_names (d : Design2) (inputs st : SvState)
    (h4 : ∀ dc ∈ d.decls.toList, dc.isInput = true → dc.twoState = false) :
    applyInputs2 d inputs st =
      d.inputNames.toList.foldl
        (fun s name => match SvState.lookup inputs name with
          | some v => SvState.set s name v
          | none => s) st := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  simp only [Design2.inputNames, Array.toList_filterMap]
  generalize d.decls.toList = ds at h4 ⊢
  induction ds generalizing st with
  | nil => rfl
  | cons dc rest ih =>
      have ih' := fun st' => ih st' (fun x hx => h4 x (List.mem_cons_of_mem _ hx))
      cases hin : dc.isInput with
      | false => simp [List.foldl_cons, List.filterMap_cons, hin, ih']
      | true =>
          have h2 : dc.twoState = false := h4 dc (List.mem_cons_self ..) hin
          simp only [List.foldl_cons, List.filterMap_cons, hin, h2, if_true, Bool.false_eq_true,
            if_false]
          exact ih' _

/-- What `applyInputs2` does to one name: an input takes the stimulus value
if the stimulus has one; every other binding is held. (4-state inputs: the
profile field `CombDesign.inFourState`.) -/
theorem lookup_applyInputs2 (d : Design2) (inputs st : SvState) (n : String)
    (h4 : ∀ dc ∈ d.decls.toList, dc.isInput = true → dc.twoState = false) :
    SvState.lookup (applyInputs2 d inputs st) n =
      if n ∈ d.inputNames.toList then (SvState.lookup inputs n).or (SvState.lookup st n)
      else SvState.lookup st n := by
  rw [applyInputs2_eq_names d inputs st h4]
  generalize d.inputNames.toList = names
  induction names generalizing st with
  | nil => simp
  | cons m ms ih =>
      rw [List.foldl_cons, ih]
      cases hm : SvState.lookup inputs m with
      | none =>
          by_cases hmn : m = n
          · subst hmn; simp [hm]
          · simp [Ne.symm hmn]
      | some v =>
          by_cases hmn : m = n
          · subst hmn; simp [hm, SvState.lookup_set_self]
          · simp [Ne.symm hmn, SvState.lookup_set_ne _ _ hmn]

/-- `applyInputs2` keeps the key list when every input name is a key. -/
theorem keys_applyInputs2 (d : Design2) (inputs : SvState) {st : SvState}
    (h4 : ∀ dc ∈ d.decls.toList, dc.isInput = true → dc.twoState = false)
    (h : ∀ n ∈ d.inputNames.toList, n ∈ st.map Prod.fst) :
    (applyInputs2 d inputs st).map Prod.fst = st.map Prod.fst := by
  rw [applyInputs2_eq_names d inputs st h4]
  generalize d.inputNames.toList = names at h
  induction names generalizing st with
  | nil => rfl
  | cons m ms ih =>
      rw [List.foldl_cons]
      have hm := h m (List.mem_cons_self ..)
      cases hv : SvState.lookup inputs m with
      | none =>
          exact ih (fun n hn => h n (List.mem_cons_of_mem _ hn))
      | some v =>
          simp only
          rw [ih (fun n hn => by
              rw [SvState.keys_set _ hm]; exact h n (List.mem_cons_of_mem _ hn)),
            SvState.keys_set _ hm]

/-- Input ports are undriven. -/
theorem CombDesign.notDriven_of_input {d : Design2} (hd : CombDesign d) {n : String}
    (h : n ∈ d.inputNames.toList) : NotDriven d n :=
  fun hD => hd.notInput n hD h

/-- `applyInputs2` never touches a driven signal. -/
theorem CombDesign.lookup_applyInputs2_driven {d : Design2} (hd : CombDesign d)
    (inputs st : SvState) {n : String} (hn : Driven d n) :
    SvState.lookup (applyInputs2 d inputs st) n = SvState.lookup st n := by
  rw [lookup_applyInputs2 d inputs st n hd.inFourState, if_neg (hd.notInput n hn)]

/-- `applyInputs2` keeps the comb shape. -/
theorem StateShape.of_applyInputs2 {d : Design2} (hd : CombDesign d) {st : SvState}
    (hs : StateShape d st) (inputs : SvState) :
    StateShape d (LeanModels.Sv.applyInputs2 d inputs st) := by
  refine ⟨?_, ?_⟩
  · rw [keys_applyInputs2 d inputs hd.inFourState
      (fun n hn => hs.keys ▸ Design2.mem_names_of_mem_inputNames hn), hs.keys]
  · intro n hn
    rw [hd.lookup_applyInputs2_driven inputs st hn]
    exact hs.driven n hn

/-- **The comb-only cycle**: no reset event, no edge process, an empty NBA
queue — a cycle is the input settle followed by the post-edge settle. -/
theorem cycleStep2_of_comb {d : Design2} (hd : CombDesign d) (σ : ScheduleOracle) (fuel : Nat)
    (inputs st : SvState) (k : Nat) :
    cycleStep2 d σ fuel inputs st k =
      (combSettle2 d σ fuel (LeanModels.Sv.applyInputs2 d inputs st) k >>=
        fun p => combSettle2 d σ fuel p.1 (p.2 + 1)) := by
  unfold cycleStep2
  simp only [hd.resetIndices_eq, hd.edgeIndices_eq, ScheduleOracle.choose_nil]
  cases combSettle2 d σ fuel (LeanModels.Sv.applyInputs2 d inputs st) k with
  | ok p => obtain ⟨st1, k1⟩ := p; rfl
  | timeout => rfl
  | unsupported msg => rfl

/-! ## Smoke test: a hand-built full adder is in the profile

`faDesign` is a full adder (`s = a ^ b ^ ci`, `co = (a & b) | (ci & (a ^ b))`)
plus a 2-bit bus `y` driven by one slice target (`y[1] = co`) and one
constant-index target (`y[0] = s`, the `index … (lit 0) 1` shape) — every
target kind of the profile. `fa_comb`/`fa_acyclic` prove the profile and the
certificate (explicit rank: the adder gates 0, the bus 1); the `#guard`s run
it through `run2` under two schedules.

These are SHARED smoke fixtures, public on purpose: `faDesign`, `fa_proc`,
`fa_writes`, `fa_driven`, `fa_comb` and `fa_acyclic` are consumed by the smoke
sections of `Comb2Sound.lean`, `Comb2Term.lean` and `Comb2.lean`, and by the
end-to-end example `Comb2Example.lean`. -/

namespace Comb2Smoke

/-- The full adder with a 2-bit bus. -/
def faDesign : Design2 where
  name := "fa"
  decls := #[
    { name := "a", width := 1, isInput := true },
    { name := "b", width := 1, isInput := true },
    { name := "ci", width := 1, isInput := true },
    { name := "s", width := 1, isOutput := true },
    { name := "co", width := 1, isOutput := true },
    { name := "y", width := 2, isOutput := true }]
  processes := #[
    .assign (.ident "s") (.binary .xor (.binary .xor (.ident "a") (.ident "b")) (.ident "ci")),
    .assign (.ident "co") (.binary .or (.binary .and (.ident "a") (.ident "b"))
      (.binary .and (.ident "ci") (.binary .xor (.ident "a") (.ident "b")))),
    .assign (.slice "y" 1 1) (.ident "co"),
    .assign (.index "y" (.lit (LVec.ofNat 1 0)) 1) (.ident "s")]

/-- The process table, as a disjunction. -/
theorem fa_proc {i : Nat} {p : Process2} : faDesign.processes[i]? = some p ↔
    (i = 0 ∧ p = .assign (.ident "s")
      (.binary .xor (.binary .xor (.ident "a") (.ident "b")) (.ident "ci"))) ∨
    (i = 1 ∧ p = .assign (.ident "co") (.binary .or (.binary .and (.ident "a") (.ident "b"))
      (.binary .and (.ident "ci") (.binary .xor (.ident "a") (.ident "b"))))) ∨
    (i = 2 ∧ p = .assign (.slice "y" 1 1) (.ident "co")) ∨
    (i = 3 ∧ p = .assign (.index "y" (.lit (LVec.ofNat 1 0)) 1) (.ident "s")) := by
  match i with
  | 0 | 1 | 2 | 3 => simp [faDesign, eq_comm]
  | i + 4 => simp [faDesign]

/-- The write windows. -/
theorem fa_writes {i : Nat} {wn : Win} : faDesign.Writes i wn ↔
    (i = 0 ∧ wn = ("s", 0, 1)) ∨ (i = 1 ∧ wn = ("co", 0, 1)) ∨
    (i = 2 ∧ wn = ("y", 1, 1)) ∨ (i = 3 ∧ wn = ("y", 0, 1)) := by
  have h0 : (LVec.ofNat 1 0).toNat? = some 0 := by rw [LVec.toNat?_ofNat]
  constructor
  · rintro ⟨t, e, hp, hw⟩
    rcases fa_proc.mp hp with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      simp only [Process2.assign.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp [Design2.declWidth, faDesign, h0] at hw <;> simp [hw]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      exact ⟨_, _, rfl, by simp [Design2.declWidth, faDesign, h0]⟩

/-- The driven signals. -/
theorem fa_driven {n : String} : Driven faDesign n ↔ n = "s" ∨ n = "co" ∨ n = "y" := by
  constructor
  · rintro ⟨i, lo, w, h⟩
    rcases fa_writes.mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> simp [h.1]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, 0, 1, fa_writes.mpr (by simp)⟩
    · exact ⟨1, 0, 1, fa_writes.mpr (by simp)⟩
    · exact ⟨2, 1, 1, fa_writes.mpr (by simp)⟩

/-- **Satisfiability of the profile.** -/
theorem fa_comb : CombDesign faDesign where
  nodup := by decide
  assign := by
    intro i p hp
    have hW : ∃ wn, faDesign.Writes i wn := by
      rcases fa_proc.mp hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨_, fa_writes.mpr (Or.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨_, fa_writes.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨_, fa_writes.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
      · exact ⟨_, fa_writes.mpr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    obtain ⟨wn, t, e, h1, h2⟩ := hW
    rw [hp] at h1; cases h1
    obtain ⟨ws, hws⟩ := Lhs2.exists_windows?_of_mem_wins h2
    exact ⟨t, e, ws, rfl, hws⟩
  inWidth := by
    intro i n lo w h
    rcases fa_writes.mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
      simp [Design2.declWidth, faDesign]
  notInput := by
    intro n hn
    rcases fa_driven.mp hn with rfl | rfl | rfl <;> simp [Design2.inputNames, faDesign]
  disjoint := by
    intro i j wi wj hij hi hj
    rcases fa_writes.mp hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases fa_writes.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact absurd rfl hij | decide
  selfDisjoint := by
    intro i t e hp
    rcases fa_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Process2.assign.injEq] at h <;> obtain ⟨rfl, -⟩ := h <;>
      exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro i t e hp
    rcases fa_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Process2.assign.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;> rfl
  rhsDeclared := by
    intro i t e hp
    rcases fa_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Process2.assign.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;>
      simp [Expr2.idents, faDesign]
  initWidth := by
    intro n _ dc hdc _ v hv
    simp [faDesign] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    simp [faDesign] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Satisfiability of the certificate**: rank 0 for the adder gates (they
read only inputs), rank 1 for the bus (it reads `s`/`co`). -/
theorem fa_acyclic : Acyclic faDesign := by
  refine ⟨fun i => if i < 2 then 0 else 1, ?_⟩
  intro i j ti ei tj ej wj hi hj hw hex
  have hWj := fa_writes.mp ⟨tj, ej, hj, hw⟩
  rcases fa_proc.mp hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    simp only [Process2.assign.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;>
    rcases hWj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | decide | exact absurd hex (by decide)

/-- The startup state has the comb shape (through the general lemma). -/
example : StateShape faDesign (initState2 faDesign) := StateShape.of_initState2 fa_comb

/-- Every comb pass order is a permutation of the four processes. -/
example (σ : ScheduleOracle) (k : Nat) :
    (σ.choose k faDesign.combIndices).Perm (List.range 4) :=
  fa_comb.choose_perm_range σ k

private def faStim : List SvState :=
  [[("a", .lit "1"), ("b", .lit "1"), ("ci", .lit "0")],
   [("a", .lit "1"), ("b", .lit "0"), ("ci", .lit "1")],
   [("a", .lit "0"), ("b", .lit "0"), ("ci", .lit "1")]]

private def faView (st : SvState) : String × String × String :=
  (SvState.showSignal st "s", SvState.showSignal st "co", SvState.showSignal st "y")

#guard (run2 faDesign σ_src 64 faStim).toOption.map (·.map faView) ==
  some [("0", "1", "10"), ("0", "1", "10"), ("1", "0", "01")]
#guard (run2 faDesign σ_rev 64 faStim).toOption.map (·.map faView) ==
  some [("0", "1", "10"), ("0", "1", "10"), ("1", "0", "01")]

end Comb2Smoke


end LeanModels.Sv
