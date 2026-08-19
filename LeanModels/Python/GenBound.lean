import LeanModels.Python.VCGen

/-!
# L8 — the three constructs `bound_probe` was blocked behind

`Examples/python/sunfish/genmoves_drain.lean` closed the whole-drain bridge
(§L6) and named what `sf_order`'s `bound_probe` still needed on top of it,
verbatim: *a `sorted`-over-a-generator EXPRESSION rule (the builtin arm drains
through `drainIter` and then allocates the sorted list, so `IterDrains` is its
engine but not its statement), generator-internal `break` at the loop-frame
level, and `callClosure`'s generator arm.* This file is those three, in a
module that IMPORTS VCGen rather than editing it (§L7 finding 3 — a downstream
module builds in a second, and the tree is paid once at the cut).

## What each one is, and what was already there

**§1 `sorted` over a generator.** `IterDrains` says what the argument's drain
IS; nothing said what the `sorted` CALL evaluates to. The interpreter's arms
(Semantics.lean, `fname == "sorted"` in both the keyword and the no-keyword
call paths) drain through `drainIter`, sort the drained list with `sortByLt`
and ALLOCATE the result, so the value is a `.ref` at the post-drain heap's end
— a fact no existing judgment could state, because `EvalsTo` pins the state
and the expression allocates twice. `EvalsIn.sortedDrain` /
`EvalsIn.sortedDrainRev` are the two arms.

Two pieces of plumbing come with them, because the shipped ordering line
(`sorted(((pos.value(m), m) for m in pos.gen_moves()), reverse=True)`) cannot
use the existing call rule: the lowered genexp's FIRST argument is
`pos.gen_moves()`, which allocates, and `EvalsIn.genCall` takes a PURE
`EvalsToList`. `EvalsInList` is the effectful argument list, `EvalsIn.genCallIn`
is `EvalsIn.genCall` over it, and `EvalsIn.ntupleGenMethod` is the receiver
form (a generator METHOD on a namedtuple, which is what `pos.gen_moves()` is).

**§2 generator-internal `break` at the LOOP-FRAME level.** §L4 landed the
UNWIND (`genSilent_delegateBreak` / `GenEmits.blockBreak`: put the enclosing
loop frame inside `pre` and `genBreak` lands at the free continuation). What
was still missing is the loop that CONSUMES it for the frame `sorted(…)`
actually produces: `sorted` allocates a heap LIST, so `execGen`'s `.forHere`
arm pushes a **`forList`** frame, and `forList` had only its two `GenSilent`
primitives — no `GenEmits`-altitude rule at all, where `forSeq` has an
induction and `forGen` has the L4 round/break/done trio. §2 is that trio for
`forList` plus `GenEmits.forListRounds`, the "n whole rounds, then whatever the
caller has" induction that a beta cutoff needs.

**§3 `callClosure`'s generator arm.** `callIn_genCall` is the MODULE-function
creation arm; a nested `def` that yields is a `.closure` object and
`callClosure` has its own creation arm (the captured snapshot goes INSIDE the
generator's stored locals). `callClosure_genCall` is that arm in equational
form, `execStmt_nestedDef` is the `def` statement that allocates the closure,
and `EvalsIn.closureGenCall` is the call expression over it.

## What is deliberately not here

Nothing in this file is about any one program: the gates that exercise it on
the shipped `sf_order` are `Examples/python/sf_order/proof.lean`.
-/

namespace LeanModels.Python

/-- Destructure a nonzero-threshold bound (private twin of VC.lean's,
VC2.lean's and VCGen.lean's helper — all of them are `private`). -/
private theorem succ_le_dest {t F : Nat} (h : t + 1 ≤ F) :
    ∃ F', F = F' + 1 ∧ t ≤ F' := ⟨F - 1, by omega, by omega⟩

/-! ## §0 Argument lists that MOVE the state

`EvalsToList` (VC2.lean) pins the out-state to the in-state, which is right
for every argument in the value tier and wrong for exactly one shape: an
argument that ALLOCATES. The shipped ordering line has one
(`<genexpr@2>(pos.gen_moves(), pos)` — the first argument is a generator
call), so the effectful twin is a prerequisite of §1 rather than a
convenience. It is to `EvalsToList` what `EvalsIn` is to `EvalsTo`. -/

/-- **Terminating EFFECTFUL argument-list evaluation**: `es` evaluate left to
right to `vs`, moving the state to `st'`. -/
def EvalsInList (m : Module) (st : FrameState) (es : List Expr) (vs : List RVal)
    (st' : FrameState) : Prop :=
  ∃ t, ∀ F ≥ t, evalExprs m F st es = .ok st' vs

namespace EvalsInList

/-- Introduce from one concrete run (any fuel). -/
theorem of_eval {m : Module} {fuel : Nat} {st st' : FrameState} {es : List Expr}
    {vs : List RVal} (h : evalExprs m fuel st es = .ok st' vs) :
    EvalsInList m st es vs st' :=
  ⟨fuel, fun F hF => evalExprs_mono h (by simp) F hF⟩

/-- A pinned-state argument list is an effectful one that moved nothing. -/
theorem of_evalsToList {m : Module} {st : FrameState} {es : List Expr}
    {vs : List RVal} (h : EvalsToList m st es vs) : EvalsInList m st es vs st :=
  h.at_least

theorem nil {m : Module} {st : FrameState} : EvalsInList m st [] [] st :=
  ⟨1, fun F hF => by
    obtain ⟨F', rfl, -⟩ := succ_le_dest hF
    rw [evalExprs]⟩

/-- One argument, then the rest — each evaluated at the state the previous
one left, which is the whole point of the judgment. -/
theorem cons {m : Module} {st st₁ st₂ : FrameState} {e : Expr} {es : List Expr}
    {v : RVal} {vs : List RVal} (hv : EvalsIn m st e v st₁)
    (hvs : EvalsInList m st₁ es vs st₂) :
    EvalsInList m st (e :: es) (v :: vs) st₂ := by
  obtain ⟨t₁, ht₁⟩ := hv
  obtain ⟨t₂, ht₂⟩ := hvs
  refine ⟨t₁ + t₂ + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  rw [evalExprs]
  simp only [ht₁ F' (by omega), Run.ok_bind, ht₂ F' (by omega)]

/-- The singleton list — `sorted`'s own argument shape. -/
theorem one {m : Module} {st st₁ : FrameState} {e : Expr} {v : RVal}
    (h : EvalsIn m st e v st₁) : EvalsInList m st [e] [v] st₁ :=
  EvalsInList.cons h EvalsInList.nil

end EvalsInList

/-! ## §1 `sorted` over a generator EXPRESSION

The interpreter's `sorted` arms take the argument's VALUE, see a generator
object at it, `drainIter` it, `sortByLt` the drained list and PUSH the result.
So the expression's value is a `.ref` at the post-drain heap's size, and its
out-state is the post-drain world with one object more. `IterDrains` (§L6)
supplies the drain; these two theorems are the statement it did not have. -/

/-- **`sorted(<generator>, reverse=r)`** — the SHIPPED ordering line's shape
(sunfish.py 412). The reverse flag's truthiness decides the direction
(`truthyH`), the object drains (`IterDrains`), `sortByLt` orders the drained
values and the result is a FRESH list at the post-drain heap's end.

The five resolution hypotheses are `evalExpr`'s own name-resolution order for
the callee (`sorted` must be the builtin, not a shadow); at a literal module
every one closes by `rfl`. -/
theorem EvalsIn.sortedDrainRev {m : Module} {st st₁ st₂ : FrameState}
    {arg rev : Expr} {a : Addr} {rv : RVal} {desc : Bool} {qname : String}
    {locals : REnv} {cont : GenCont} {status : GenStatus}
    {vs sortedVs : List RVal} {w' : World} {sp sp' : Span}
    (hlocal : Env.lookup st.locals "sorted" = Option.none)
    (hglob : lookupG (moduleGlobals m).1 "sorted" = Option.none)
    (hfn : findFunction m "sorted" = Option.none)
    (hcls : findClass m "sorted" = Option.none)
    (hnt : findNamedTuple m "sorted" = Option.none)
    (harg : EvalsIn m st arg (.ref a) st₁)
    (hrev : EvalsIn m st₁ rev rv st₂)
    (hdesc : truthyH st₂.world.heap rv = .ok desc)
    (hobj : Heap.get? st₂.world.heap a = some (.generator qname locals cont status))
    (hdrain : IterDrains m st₂.world a vs w')
    (hsort : sortByLt desc vs = .ok sortedVs) :
    EvalsIn m st (.call (.name "sorted" sp) #[arg] #[("reverse", rev)] Option.none sp')
      (.ref w'.heap.size)
      ⟨{ w' with heap := w'.heap.push (.list sortedVs.toArray) }, st₂.locals⟩ := by
  obtain ⟨t₁, ht₁⟩ := EvalsInList.one harg
  obtain ⟨t₂, ht₂⟩ := EvalsInList.one hrev
  obtain ⟨t₃, ht₃⟩ := hdrain
  refine ⟨t₁ + t₂ + t₃ + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  have hkw : (#[("reverse", rev)] : Array (String × Expr)).isEmpty = false := rfl
  have hdict : ("sorted" == "dict") = false := rfl
  have hself : ("sorted" == "sorted") = true := rfl
  have hkey : ([("reverse", rev)].any fun x : String × Expr => x.fst == "key") = false := rfl
  have hfind :
      List.find? (fun kv : String × Expr => kv.fst != "reverse") [("reverse", rev)]
        = Option.none := rfl
  have hmap : List.map (fun x : String × Expr => x.snd) [("reverse", rev)] = [rev] := rfl
  rw [evalExpr]
  simp only [hkw, Bool.false_eq_true, if_neg, not_false_eq_true, hlocal, hglob,
    hfn, hcls, hnt, Option.isSome_none, hdict, hself, hkey, hfind, hmap, if_pos,
    ht₁ F' (by omega), ht₂ F' (by omega), Run.ok_bind, Run.liftRes, hdesc, hobj,
    Run.withLocals, ht₃ F' (by omega), hsort]

/-- **`sorted(<generator>)`** — the keyword-free arm, through the interpreter's
other `sorted` dispatch (a call with no keywords never reaches the keyword
path, so the two arms are genuinely two theorems). Ascending, so `sortByLt` at
`false`. -/
theorem EvalsIn.sortedDrain {m : Module} {st st₁ : FrameState}
    {arg : Expr} {a : Addr} {qname : String}
    {locals : REnv} {cont : GenCont} {status : GenStatus}
    {vs sortedVs : List RVal} {w' : World} {sp sp' : Span}
    (hlocal : Env.lookup st.locals "sorted" = Option.none)
    (hglob : lookupG (moduleGlobals m).1 "sorted" = Option.none)
    (hfn : findFunction m "sorted" = Option.none)
    (hcls : findClass m "sorted" = Option.none)
    (hnt : findNamedTuple m "sorted" = Option.none)
    (harg : EvalsIn m st arg (.ref a) st₁)
    (hobj : Heap.get? st₁.world.heap a = some (.generator qname locals cont status))
    (hdrain : IterDrains m st₁.world a vs w')
    (hsort : sortByLt false vs = .ok sortedVs) :
    EvalsIn m st (.call (.name "sorted" sp) #[arg] #[] Option.none sp')
      (.ref w'.heap.size)
      ⟨{ w' with heap := w'.heap.push (.list sortedVs.toArray) }, st₁.locals⟩ := by
  obtain ⟨t₁, ht₁⟩ := EvalsInList.one harg
  obtain ⟨t₃, ht₃⟩ := hdrain
  refine ⟨t₁ + t₃ + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  have hkw : (#[] : Array (String × Expr)).isEmpty = true := rfl
  have hlen : ("sorted" == "len") = false := rfl
  have hself : ("sorted" == "sorted") = true := rfl
  rw [evalExpr]
  simp only [hkw, hlocal, hglob, hfn, hcls, hnt, Option.isSome_none, hlen, hself,
    Bool.false_eq_true, if_neg, not_false_eq_true, if_pos,
    ht₁ F' (by omega), Run.ok_bind, Run.liftRes, hobj,
    Run.withLocals, ht₃ F' (by omega), hsort]

/-- **A generator call whose ARGUMENTS move the state** — `EvalsIn.genCall`
over `EvalsInList`. The lowered genexp's first argument is the outer iterator
(CPython's `.0`), which for the shipped ordering line is `pos.gen_moves()` and
therefore allocates; the pure rule cannot express that call. -/
theorem EvalsIn.genCallIn {m : Module} {st st₁ : FrameState} {fname : String}
    {f : FunctionDefn} {argEs : Array Expr} {vs : List RVal} {sp sp' : Span}
    (hlocal : Env.lookup st.locals fname = Option.none)
    (hglob : lookupG (moduleGlobals m).1 fname = Option.none)
    (hcls : findClass m fname = Option.none)
    (hnt : findNamedTuple m fname = Option.none)
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : arityOk f.params vs.length = true) (hgen : f.isGenerator = true)
    (hargs : EvalsInList m st argEs.toList vs st₁) :
    EvalsIn m st (.call (.name fname sp) argEs #[] Option.none sp')
      (.ref st₁.world.heap.size)
      ⟨{ st₁.world with heap := st₁.world.heap.push (genObj fname f vs.toArray) },
        st₁.locals⟩ := by
  obtain ⟨ta, ha⟩ := hargs
  refine ⟨ta + 2, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  obtain ⟨F'', rfl, hF''⟩ := succ_le_dest hF'
  have hcall := callIn_genCall (m := m) (fuel := F'') (w := st₁.world) (fname := fname)
    (args := vs.toArray) hf hargsOk hlocalsOk (by simpa using harity) hgen
  rw [evalExpr]
  simp only [Array.isEmpty, Array.size_empty, hlocal, hglob, hcls, hnt, hf,
    ha (F'' + 1) (by omega), Run.ok_bind, Option.isSome_some, if_pos,
    Option.isSome_none, Bool.false_or, Bool.false_eq_true, if_neg,
    not_false_eq_true, hcall, Run.withLocals]
  rfl

/-- **A generator METHOD on a namedtuple receiver** — `pos.gen_moves()`. The
receiver evaluates first (CPython's order), the plan is decided from the
receiver's type before any argument runs, and `self` is the ntuple VALUE
prepended to the arguments; the creation arm is `callIn`'s, so what comes back
is a `.ref` at the heap's end with the body as its stored continuation. -/
theorem EvalsIn.ntupleGenMethod {m : Module} {st st₀ st₁ : FrameState}
    {recv : Expr} {attr qname : String} {tn : String} {fs : Array String}
    {xs : Array RVal} {f : FunctionDefn} {argEs : Array Expr} {vs : List RVal}
    {sp sp' : Span}
    (hclock : isClockCall m st recv attr = false)
    (hrecv : EvalsIn m st recv (.ntuple tn fs xs) st₀)
    (hplan : ntupleCallPlan m tn fs attr = .instMethod qname)
    (hargs : EvalsInList m st₀ argEs.toList vs st₁)
    (hf : findFunction m qname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : arityOk f.params (vs.length + 1) = true) (hgen : f.isGenerator = true) :
    EvalsIn m st (.call (.attribute recv attr sp) argEs #[] Option.none sp')
      (.ref st₁.world.heap.size)
      ⟨{ st₁.world with
            heap := st₁.world.heap.push
              (genObj qname f (.ntuple tn fs xs :: vs).toArray) },
          st₁.locals⟩ := by
  obtain ⟨tr, hr⟩ := hrecv
  obtain ⟨ta, ha⟩ := hargs
  refine ⟨tr + ta + 2, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  obtain ⟨F'', rfl, hF''⟩ := succ_le_dest hF'
  have hcall := callIn_genCall (m := m) (fuel := F'') (w := st₁.world) (fname := qname)
    (args := (RVal.ntuple tn fs xs :: vs).toArray) hf hargsOk hlocalsOk
    (by simpa using harity) hgen
  rw [evalExpr]
  simp only [Array.isEmpty, Array.size_empty, hclock, Bool.false_eq_true, if_neg,
    not_false_eq_true, hr (F'' + 1) (by omega), Run.ok_bind, hplan,
    ha (F'' + 1) (by omega), hcall, Run.withLocals]
  simp

/-- **Call a generator function and drain what it answered, in one step** —
`EvalsIn.genCallIn` and `IterDrains.of_genYields` composed, which is the PAIR
`sorted` needs about its argument: the value AND the drain of the object at
it. The body's frame-level yield fact is the only hypothesis that is not
bookkeeping. -/
theorem EvalsIn.genCallDrains {m : Module} {st st₁ : FrameState} {fname : String}
    {f : FunctionDefn} {argEs : Array Expr} {vs : List RVal} {ys : List RVal}
    {st' : FrameState} {sp sp' : Span}
    (hlocal : Env.lookup st.locals fname = Option.none)
    (hglob : lookupG (moduleGlobals m).1 fname = Option.none)
    (hcls : findClass m fname = Option.none)
    (hnt : findNamedTuple m fname = Option.none)
    (hf : findFunction m fname = some f)
    (hargsOk : f.argsOk = true) (hlocalsOk : f.localsOk = true)
    (harity : arityOk f.params vs.length = true) (hgen : f.isGenerator = true)
    (hargs : EvalsInList m st argEs.toList vs st₁)
    (hy : GenYields m
      ⟨{ st₁.world with heap := st₁.world.heap.push (.generator fname
          (mkCallEnv f.params vs.toArray) [.block f.body.toList] .running) },
        mkCallEnv f.params vs.toArray⟩ [.block f.body.toList] ys st') :
    ∃ w', EvalsIn m st (.call (.name fname sp) argEs #[] Option.none sp')
        (.ref st₁.world.heap.size)
        ⟨{ st₁.world with heap := st₁.world.heap.push (genObj fname f vs.toArray) },
          st₁.locals⟩ ∧
      IterDrains m
        { st₁.world with heap := st₁.world.heap.push (genObj fname f vs.toArray) }
        st₁.world.heap.size ys w' := by
  obtain ⟨w', hd⟩ := IterDrains.of_genYields ys
    { st₁.world with heap := st₁.world.heap.push (genObj fname f vs.toArray) }
    (mkCallEnv f.params vs.toArray) [.block f.body.toList] .created
    (st₁.world.heap.push (.generator fname (mkCallEnv f.params vs.toArray)
      [.block f.body.toList] .running)) st'
    (Heap.get?_push_size _ _) (Or.inl rfl) (Heap.update_push_size _ _ _) hy
  exact ⟨w', EvalsIn.genCallIn hlocal hglob hcls hnt hf hargsOk hlocalsOk harity
    hgen hargs, hd⟩

/-! ## §2 The `forList` loop at `GenEmits` altitude — where a `break` lands

`sorted` ALLOCATES its answer, so `for x in sorted(…)` inside a generator
pushes a **`forList`** frame (`execGen`'s `.forHere` arm: only an immutable
value sequence becomes `forSeq`, and a `.ref` to a heap list becomes
`forList`). §L4's `GenEmits.blockBreak` already unwinds a `break` whose
enclosing loop frame sits in the polymorphic prefix; what had no rule at all
was the `forList` LOOP that consumes it. These are `forGen`'s L4 trio,
transposed, plus the induction a beta cutoff needs.

The live cursor re-reads the object every round, so each rule carries the heap
read AT THE STATE THE ROUND STARTS FROM — the file-level reason VCGen.lean
gives for not offering a snapshot-style invariant rule here. `forListRounds`
keeps that honest by asking the caller's invariant to re-establish the read. -/

/-- **Entering the loop** — the piece without which the frame below is
unreachable. `genSilent_forHere` (VCGen) covers a value SEQUENCE through
`IterVals` and a pinned-state `EvalsTo`; `sorted(…)` is neither — it answers a
`.ref` to a heap LIST and it ALLOCATES twice getting there. `execGen`'s
`.forHere` arm dispatches on the heap object and pushes a `forList` frame;
this is that arm, over `EvalsIn`. -/
theorem genSilent_forHereList {m : Module} {st st₁ : FrameState} {s : Stmt}
    {target iter : Expr} {body ss : List Stmt} {k : GenCont} {ad : Addr}
    {xs : Array RVal} (hplan : genPlan s = .forHere target iter body)
    (hv : EvalsIn m st iter (.ref ad) st₁)
    (hobj : Heap.get? st₁.world.heap ad = some (.list xs)) :
    GenSilent m st (.block (s :: ss) :: k) st₁
      (.forList target ad 0 body :: .block ss :: k) := by
  obtain ⟨t, ht⟩ := hv
  refine ⟨1, t, fun F hF => ?_⟩
  rw [execGen]
  simp only [hplan, ht F hF, Run.ok_bind, hobj]

/-- **Entering the loop, at `GenEmits` altitude.** The whole `for` statement
(and the block frame around it) becomes the loop frame plus the rest of the
block, so §2's round rules apply to what the caller has. -/
theorem GenEmits.blockForList {m : Module} {st st₁ st₂ : FrameState} {s : Stmt}
    {target iter : Expr} {body ss : List Stmt} {ad : Addr} {xs : Array RVal}
    {ws : List RVal} (hplan : genPlan s = .forHere target iter body)
    (hv : EvalsIn m st iter (.ref ad) st₁)
    (hobj : Heap.get? st₁.world.heap ad = some (.list xs))
    (hrest : GenEmits m st₁ [.forList target ad 0 body, .block ss] ws st₂) :
    GenEmits m st [.block (s :: ss)] ws st₂ :=
  GenEmits.silent (pre := [GenFrame.block (s :: ss)])
    (pre₁ := [GenFrame.forList target ad 0 body, GenFrame.block ss])
    (fun k => by simpa using genSilent_forHereList (k := k) hplan hv hobj)
    hrest

/-- **A round of `for x in <heap list>` whose body FALLS THROUGH**: the cursor
hands over element `i`, the target binds it, the body emits `ws`, and the loop
frame is still below for the rest. -/
theorem GenEmits.forListRound {m : Module} {target : Expr} {body : List Stmt}
    {ad : Addr} {i : Nat} {xs : Array RVal} {st st₂ st₃ : FrameState} {env₁ : REnv}
    {ws ws' : List RVal}
    (hobj : Heap.get? st.world.heap ad = some (.list xs)) (hi : i < xs.size)
    (hasg : assignToH st.world.heap st.locals target (xs.getD i .none) = .ok env₁)
    (hbody : GenEmits m { st with locals := env₁ } [.block body] ws st₂)
    (hrest : GenEmits m st₂ [.forList target ad (i + 1) body] ws' st₃) :
    GenEmits m st [.forList target ad i body] (ws ++ ws') st₃ :=
  GenEmits.silent (pre := [GenFrame.forList target ad i body])
    (pre₁ := [GenFrame.block body, GenFrame.forList target ad (i + 1) body])
    (fun k => by simpa using genSilent_forListCons (k := k) hobj hi hasg)
    (GenEmits.trans hbody hrest)

/-- **The round that BREAKS** — the beta cutoff. The body's own emission
consumes `[.block body, .forList …]` together, because `genBreak` unwinds past
the loop frame: body and loop leave as one, which is exactly why
`GenEmits.blockBreak` (with the loop frame in its prefix) meets this rule with
no new judgment between them. -/
theorem GenEmits.forListBreak {m : Module} {target : Expr} {body : List Stmt}
    {ad : Addr} {i : Nat} {xs : Array RVal} {st st₂ : FrameState} {env₁ : REnv}
    {ws : List RVal}
    (hobj : Heap.get? st.world.heap ad = some (.list xs)) (hi : i < xs.size)
    (hasg : assignToH st.world.heap st.locals target (xs.getD i .none) = .ok env₁)
    (hbody : GenEmits m { st with locals := env₁ }
      [.block body, .forList target ad (i + 1) body] ws st₂) :
    GenEmits m st [.forList target ad i body] ws st₂ :=
  GenEmits.silent (pre := [GenFrame.forList target ad i body])
    (pre₁ := [GenFrame.block body, GenFrame.forList target ad (i + 1) body])
    (fun k => by simpa using genSilent_forListCons (k := k) hobj hi hasg)
    hbody

/-- **The cursor ran off the end** — the loop frame pops, emitting nothing.
The bound is re-read here rather than fixed at entry, which is the faithful
behaviour for a list that shrank under its own iterator. -/
theorem GenEmits.forListDone {m : Module} {target : Expr} {body : List Stmt}
    {ad : Addr} {i : Nat} {xs : Array RVal} {st : FrameState}
    (hobj : Heap.get? st.world.heap ad = some (.list xs)) (hi : ¬ i < xs.size) :
    GenEmits m st [.forList target ad i body] [] st :=
  GenEmits.silent (pre := [GenFrame.forList target ad i body]) (pre₁ := ([] : GenCont))
    (fun _ => by
      simpa using genSilent_forListDone (target := target) (body := body) hobj hi)
    GenEmits.nil

/-- The outputs of `n` consecutive rounds starting at index `i`. -/
def GenEmits.roundsOut (out : Nat → List RVal) (i : Nat) : Nat → List RVal
  | 0 => []
  | n + 1 => out i ++ GenEmits.roundsOut out (i + 1) n

/-- **`n` whole rounds, then whatever the caller has.** The lazy half of the
loop: a consumer that breaks out at round `n` (or finds the cursor exhausted
there) supplies the ending, and this induction supplies the prefix. There is
no exit obligation and no stability side condition — the invariant carries the
cursor's own heap read, so a body that mutates the list is describable rather
than excluded. -/
theorem GenEmits.forListRounds {m : Module} {target : Expr} {body : List Stmt}
    {ad : Addr} (out : Nat → List RVal) (Inv : Nat → FrameState → Prop)
    (hstep : ∀ i st, Inv i st → ∃ (xs : Array RVal) (env₁ : REnv) (st₂ : FrameState),
      Heap.get? st.world.heap ad = some (.list xs) ∧ i < xs.size ∧
        assignToH st.world.heap st.locals target (xs.getD i .none) = .ok env₁ ∧
        Inv (i + 1) st₂ ∧
        GenEmits m { st with locals := env₁ } [.block body] (out i) st₂) :
    ∀ (n i : Nat) (st : FrameState), Inv i st →
      ∃ st₂, Inv (i + n) st₂ ∧
        ∀ (ws : List RVal) (st₃ : FrameState),
          GenEmits m st₂ [.forList target ad (i + n) body] ws st₃ →
          GenEmits m st [.forList target ad i body]
            (GenEmits.roundsOut out i n ++ ws) st₃ := by
  intro n
  induction n with
  | zero =>
    intro i st hI
    exact ⟨st, by simpa using hI,
      fun ws st₃ h => by simpa [GenEmits.roundsOut] using h⟩
  | succ n ih =>
    intro i st hI
    obtain ⟨xs, env₁, st₂, hobj, hi, hasg, hI₂, hbody⟩ := hstep i st hI
    obtain ⟨st₃, hI₃, hcont⟩ := ih (i + 1) st₂ hI₂
    refine ⟨st₃, by simpa [Nat.add_right_comm, Nat.add_assoc] using hI₃, ?_⟩
    intro ws st₄ htail
    have := GenEmits.forListRound hobj hi hasg hbody
      (hcont ws st₄ (by simpa [Nat.add_right_comm, Nat.add_assoc] using htail))
    simpa [GenEmits.roundsOut, List.append_assoc] using this

/-! ## §3 `callClosure`'s generator arm — a nested `def` that yields

A nested `def` allocates a `.closure` object carrying the SNAPSHOT of its
captured names (`execStmt`'s `defStmt` arm); calling it goes to `callClosure`,
whose generator arm allocates the H4 object with `mkCallEnv params args ++
captured` as the stored locals — parameters shadow captures, and resume-time
capture reads therefore ride the ordinary stepper. `callIn_genCall` (VCGen)
is the module-function twin of the middle theorem here. -/

/-- **The heap object a generator CLOSURE call allocates.** `genObj`'s
closure twin: the qualified name is CPython's `<closure:name>` shape, and the
captured snapshot sits INSIDE the stored locals, after the parameters. -/
def closureGenObj (name : String) (params : Array Param) (body : Array Stmt)
    (captured : REnv) (args : Array RVal) : Obj :=
  .generator s!"<closure:{name}>" (mkCallEnv params args ++ captured)
    [.block body.toList] .created

/-- **The `def` statement ALLOCATES the closure**: the captures snapshot out of
the current frame, the object lands at the heap's end and the name binds to
it. The one statement between a nested generator's definition and its call. -/
theorem execStmt_nestedDef {m : Module} {fuel : Nat} {st : FrameState}
    {name : String} {params : Array Param} {argsOk localsOk hasGlobal isGenerator : Bool}
    {body : Array Stmt} {captures : Array String} {cap : REnv} {sp : Span}
    -- H7 cells: a capture list with no CELL keys allocates nothing, so the
    -- frame the snapshot reads is the frame the statement started in
    (hnc : allocCells st captures.toList = st)
    (hcap : capturesSnapshot st.locals captures.toList = some cap) :
    execStmt m (fuel + 1) st
        (.defStmt name params argsOk localsOk hasGlobal isGenerator body captures sp)
      = .ok ⟨{ st.world with
                heap := st.world.heap.push
                  (.closure name params argsOk localsOk hasGlobal isGenerator body cap) },
              Env.set st.locals name (.ref st.world.heap.size)⟩ .next := by
  rw [execStmt]
  simp only [hnc, hcap]

/-- **Calling a generator CLOSURE runs no code**: it appends the suspended
frame to the heap and answers its address. `callClosure`'s creation arm in
equational form (the guards are the interpreter's own, in its own order);
`callIn_genCall`'s twin for the nested-def half of the tier. -/
theorem callClosure_genCall {m : Module} {fuel : Nat} {w : World} {name : String}
    {params : Array Param} {body : Array Stmt} {captured : REnv}
    {args : Array RVal} (harity : arityOk params args.size = true) :
    callClosure m (fuel + 1) w name params true true true body captured args
      = .ok { w with heap := w.heap.push (closureGenObj name params body captured args) }
          (.ref w.heap.size) := by
  rw [callClosure]
  simp [harity, closureGenObj]

/-- **A generator-closure call is a value with a specification** —
`EvalsIn.genCall`'s closure twin. The callee name resolves in the frame's
LOCALS to a `.ref` (that is what a nested `def` binds), the tier's closure
guard must be open (`funsHeapFree && topLevelDefFree` is `false` the moment
any body contains a nested def — heap-free modules keep the faithful
`TypeError`), and what comes back is the address of a fresh generator whose
stored continuation is the closure's body. -/
theorem EvalsIn.closureGenCall {m : Module} {st : FrameState} {fname : String}
    {a : Addr} {nm : String} {ps : Array Param} {hg : Bool} {bd : Array Stmt}
    {cap : REnv} {argEs : Array Expr} {vs : List RVal} {sp sp' : Span}
    (hlocal : Env.lookup st.locals fname = some (.ref a))
    (hnotfree : (funsHeapFree m.functions.toList && topLevelDefFree m) = false)
    (hobj : Heap.get? st.world.heap a = some (.closure nm ps true true hg true bd cap))
    -- H7 cells: a capture list with no CELL keys resolves to itself
    (hnc : cellsFor st.world.heap st.locals cap = .ok cap)
    (harity : arityOk ps vs.length = true)
    (hargs : EvalsToList m st argEs.toList vs) :
    EvalsIn m st (.call (.name fname sp) argEs #[] Option.none sp')
      (.ref st.world.heap.size)
      ⟨{ st.world with heap :=
            st.world.heap.push (closureGenObj nm ps bd cap vs.toArray) }, st.locals⟩ := by
  obtain ⟨ta, ha⟩ := hargs.at_least
  refine ⟨ta + 2, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ := succ_le_dest hF
  obtain ⟨F'', rfl, hF''⟩ := succ_le_dest hF'
  have hcall := callClosure_genCall (m := m) (fuel := F'') (w := st.world) (name := nm)
    (params := ps) (body := bd) (captured := cap) (args := vs.toArray)
    (by simpa using harity)
  rw [evalExpr]
  simp only [Array.isEmpty, Array.size_empty, hlocal, ha (F'' + 1) (by omega),
    Run.ok_bind, hnotfree, if_neg, Bool.false_eq_true, not_false_eq_true, hobj,
    Run.withLocals]
  simp only [hnc, Run.liftRes, Run.ok_bind, hcall]
  simp

/-! ## Smoke tests

Hand-built frame stacks over an empty module, exercising the composition and
nothing else — the real acceptance is `Examples/python/sf_order/proof.lean`
over the ingested program. -/

namespace GenBoundSmokeTest

private def m0 : Module := ⟨#[], #[], #[], #[]⟩
private def sp0 : Span := ⟨0, 0, 0, 0⟩
private def w0 : World := ⟨#[.list #[.int 7, .int 8]], [], [], []⟩
private def tgt : Expr := .name "x" sp0
private def yieldS : Stmt := .yieldStmt (.constant (.int 1) sp0) sp0

/-- The loop body of the smoke below, at one bound element. -/
private theorem yield_round (v : RVal) :
    GenEmits m0 ⟨w0, [("x", v)]⟩ [.block [yieldS]] [.int 1] ⟨w0, [("x", v)]⟩ := by
  refine GenEmits.cons (v := .int 1) (pre₁ := [GenFrame.block []])
    (st₁ := ⟨w0, [("x", v)]⟩) (fun k => ?_) ?_
  · have h := genSteps_yieldHere (m := m0) (st := ⟨w0, [("x", v)]⟩) (s := yieldS)
      (e := .constant (.int 1) sp0) (ss := ([] : List Stmt)) (k := k) (v := .int 1)
      rfl (EvalsTo.of_eval (fuel := 1) rfl)
    simpa using h
  · exact GenEmits.silent (pre₁ := ([] : GenCont))
      (fun k => by simpa using genSilent_blockNil (m := m0) (k := k)) GenEmits.nil

/-- **The loop**: a two-element heap list iterated inside a generator, one
yield per round, then the live cursor runs off the end. `forListRound` twice
and `forListDone` once — the trio `forList` did not have. -/
example :
    GenEmits m0 ⟨w0, []⟩ [.forList tgt 0 0 [yieldS]] [.int 1, .int 1]
      ⟨w0, [("x", .int 8)]⟩ := by
  have r2 := GenEmits.forListRound (m := m0) (target := tgt) (body := [yieldS])
    (ad := 0) (i := 1) (xs := #[.int 7, .int 8]) (st := ⟨w0, [("x", .int 7)]⟩)
    rfl (by decide) rfl (yield_round (.int 8))
    (GenEmits.forListDone (m := m0) (target := tgt) (body := [yieldS]) (ad := 0)
      (i := 2) (xs := #[.int 7, .int 8]) (st := ⟨w0, [("x", .int 8)]⟩) rfl (by decide))
  have r1 := GenEmits.forListRound (m := m0) (target := tgt) (body := [yieldS])
    (ad := 0) (i := 0) (xs := #[.int 7, .int 8]) (st := ⟨w0, ([] : REnv)⟩)
    rfl (by decide) rfl (yield_round (.int 7)) r2
  simpa using r1

/-- **The BREAK**: the same loop whose body is `break`. `GenEmits.blockBreak`
unwinds the statement AND the loop frame (the loop frame is its prefix), and
`forListBreak` is what receives that — body and loop leave together, nothing
is emitted, and the frame stack below is untouched. -/
example :
    GenEmits m0 ⟨w0, []⟩ [.forList tgt 0 0 [Stmt.brk sp0]] [] ⟨w0, [("x", .int 7)]⟩ :=
  GenEmits.forListBreak (m := m0) (target := tgt) (body := [Stmt.brk sp0]) (ad := 0)
    (i := 0) (xs := #[.int 7, .int 8]) (st := ⟨w0, ([] : REnv)⟩) rfl (by decide) rfl
    (GenEmits.blockBreak (m := m0) (s := Stmt.brk sp0) (ss := ([] : List Stmt))
      (pre := [GenFrame.forList tgt 0 1 [Stmt.brk sp0]]) rfl (fun _ => rfl)
      ⟨1, fun F hF => by obtain ⟨F', rfl, -⟩ := succ_le_dest hF; rfl⟩)

end GenBoundSmokeTest

end LeanModels.Python
