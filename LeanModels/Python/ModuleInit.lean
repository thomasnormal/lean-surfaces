/-
**The module-INIT calculus** — statements about a real module's STARTING
WORLD, proved one top-level statement at a time.

Everything that reasons about a shipped program eventually has to say
something about `initWorld m`: the world every public call starts from.
`initWorld` is not a literal — it RUNS the module (`initFoldLive` over
`m.topLevel`, docs/memory-model.md §module-init execution), so a ground
fact about it is a fact about a whole interpreter run, and asking the
kernel for one by `rfl` asks it for the WHOLE run in a single reduction.
On the shipped sunfish module that does not finish (docs/backlog.md §L12
has the numbers: OOM at ~7 min / 16 GB).

This module is the alternative: **the pipeline's own equations, stated at
the altitude the pipeline is written at.** Each lemma consumes ONE
top-level statement and hands back the pipeline at the next one, with the
statement's effect as a hypothesis. A chain of them turns "reduce
`initWorld m`" into "reduce each statement's effect, separately" — which
is a different computation with a different price, and it is the price
that can be paid per statement (or, where a statement is itself too big,
left as one named ground hypothesis about THAT statement instead of about
the whole initializer).

**Nothing here is about any particular module.** Every lemma quantifies
over `m`, `s`, `done` and `rest`; the sunfish chain that exercises them is
`Examples/python/sunfish/init_chain.lean`. That is deliberate — the next
consumer (a `TableOK`-shaped statement about the starting world) reuses
these unchanged.

**Proof shape, and why it is one line each.** `initFoldLive` is
structurally recursive on the remaining statements and its body is a
two-level `match` on `initFoldStep` and then on `initExecStmt`; each lemma
below rewrites with the pipeline's own equation and then with the
hypothesis that selects the arm. No induction, no simp set, no unfolding
of any program.
-/
import LeanModels.Python.Semantics

namespace LeanModels.Python

/-! ## One top-level statement, three arms

The pipeline gives each statement the pure FOLD step first
(`initFoldStep`); a fold-refused statement gets the EXEC attempt under the
per-statement prefix view (`topLevel := done.push s`); a failed attempt
ROLLS BACK and poisons (`globalsDirty`). The three lemmas are those three
arms, and together they are exhaustive: `initFoldLive_step` below packages
them so a caller never has to know which one fired. -/

/-- The pipeline at the end of the top level: the accumulated world. -/
@[simp] theorem initFoldLive_nil (m : Module) (fuel : Nat) (h : Heap)
    (acc : GlobalsAcc) (done : Array Stmt) :
    initFoldLive m fuel h acc done [] = (h, acc) := by
  rw [initFoldLive]

/-- **The fold arm.** A statement the pure fold accepts (a statically
valued binding — `globalsStep`'s in-tier arms) advances the live state to
exactly what the fold says, with no interpreter run at all. -/
theorem initFoldLive_fold {m : Module} {fuel : Nat} {h h' : Heap}
    {acc acc' : GlobalsAcc} {done : Array Stmt} {s : Stmt} {rest : List Stmt}
    (hs : initFoldStep h acc s = some (h', acc')) :
    initFoldLive m fuel h acc done (s :: rest)
      = initFoldLive m fuel h' acc' (done.push s) rest := by
  rw [initFoldLive, hs]

/-- **The exec arm.** A fold-refused statement whose EXEC attempt succeeds
advances to the attempt's own state. The module the attempt runs under is
the prefix view `{ m with topLevel := done.push s }` — the statement's own
resolution view, which is part of the statement of the lemma rather than
something a caller may choose. -/
theorem initFoldLive_exec {m : Module} {fuel : Nat} {h h' : Heap}
    {acc acc' : GlobalsAcc} {done : Array Stmt} {s : Stmt} {rest : List Stmt}
    (hs : initFoldStep h acc s = Option.none)
    (he : initExecStmt { m with topLevel := done.push s } fuel h acc s
      = .ok (h', acc') ()) :
    initFoldLive m fuel h acc done (s :: rest)
      = initFoldLive m fuel h' acc' (done.push s) rest := by
  rw [initFoldLive, hs, he]

/-- **The rollback arm.** A fold-refused statement whose EXEC attempt
FAILS is rolled back and its dirty names poisoned — in the live
accumulator too, which is what keeps a stale pre-statement value from
resurfacing through the poisoned-arm consult. `hr` names the failure; the
three failing constructors are the three `Run` arms that are not `.ok`,
and each of them selects this arm. -/
theorem initFoldLive_dirty {m : Module} {fuel : Nat} {h h' : Heap}
    {acc acc' : GlobalsAcc} {done : Array Stmt} {s : Stmt} {rest : List Stmt}
    {r : Run (Heap × GlobalsAcc) Unit} {b : Bool}
    (hs : initFoldStep h acc s = Option.none)
    (he : initExecStmt { m with topLevel := done.push s } fuel h acc s = r)
    (hr : ∀ p u, r ≠ .ok p u)
    (hd : globalsDirty h acc true s = (h', acc', b)) :
    initFoldLive m fuel h acc done (s :: rest)
      = initFoldLive m fuel h' acc' (done.push s) rest := by
  rw [initFoldLive, hs, he]
  cases r with
  | ok p u => exact absurd rfl (hr p u)
  | exn _ _ => rw [hd]
  | timeout => rw [hd]
  | unsupported _ => rw [hd]

/-- The rollback arm at an `unsupported` attempt — the common shape (a
statement whose right-hand side is out of tier), with the `≠` obligation
discharged. -/
theorem initFoldLive_unsupported {m : Module} {fuel : Nat} {h h' : Heap}
    {acc acc' : GlobalsAcc} {done : Array Stmt} {s : Stmt} {rest : List Stmt}
    {msg : String} {b : Bool}
    (hs : initFoldStep h acc s = Option.none)
    (he : initExecStmt { m with topLevel := done.push s } fuel h acc s
      = .unsupported msg)
    (hd : globalsDirty h acc true s = (h', acc', b)) :
    initFoldLive m fuel h acc done (s :: rest)
      = initFoldLive m fuel h' acc' (done.push s) rest :=
  initFoldLive_dirty hs he (by rintro _ _ ⟨⟩) hd

/-- The rollback arm at a RAISING attempt (the statement's exception is
not the module's — it is rolled back and poisoned, loudly, exactly like a
refusal). -/
theorem initFoldLive_exn {m : Module} {fuel : Nat} {h h' : Heap}
    {acc acc' : GlobalsAcc} {done : Array Stmt} {s : Stmt} {rest : List Stmt}
    {p : Heap × GlobalsAcc} {e : PyErr} {b : Bool}
    (hs : initFoldStep h acc s = Option.none)
    (he : initExecStmt { m with topLevel := done.push s } fuel h acc s = .exn p e)
    (hd : globalsDirty h acc true s = (h', acc', b)) :
    initFoldLive m fuel h acc done (s :: rest)
      = initFoldLive m fuel h' acc' (done.push s) rest :=
  initFoldLive_dirty hs he (by rintro _ _ ⟨⟩) hd

/-! ## The whole prefix, and the world it makes

Two lemmas that turn a chain of the above into a statement about
`initWorld` itself. `initFoldLive_append` is the associativity the chain
needs when a run of statements is discharged in ONE reduction (cheap
statements are not worth a lemma each); `initWorld_of_run` is the last
step, and it is where `resolvedG` enters. -/

/-- `done.push x ++ xs.toArray = done ++ (x :: xs).toArray` — the `done`
view's bookkeeping, the one array identity the split needs. -/
private theorem push_append_toArray {α : Type _} (done : Array α) (x : α) (xs : List α) :
    done.push x ++ xs.toArray = done ++ (x :: xs).toArray := by
  apply Array.toList_inj.mp
  simp

/-- Splitting the top level: running `xs` then `ys` is running `xs ++ ys`.
The `done` view accumulates across the split exactly as the pipeline
accumulates it, which is why `done ++ xs` appears on the right. -/
theorem initFoldLive_append (m : Module) (fuel : Nat) :
    ∀ (xs ys : List Stmt) (h : Heap) (acc : GlobalsAcc) (done : Array Stmt),
      initFoldLive m fuel h acc done (xs ++ ys)
        = initFoldLive m fuel (initFoldLive m fuel h acc done xs).1
            (initFoldLive m fuel h acc done xs).2 (done ++ xs.toArray) ys
  | [], ys, h, acc, done => by simp [initFoldLive]
  | x :: xs, ys, h, acc, done => by
    rw [List.cons_append, initFoldLive]
    cases hs : initFoldStep h acc x with
    | some p =>
      rw [initFoldLive, hs]
      have := initFoldLive_append m fuel xs ys p.1 p.2 (done.push x)
      simpa [push_append_toArray] using this
    | none =>
      rw [initFoldLive, hs]
      cases he : initExecStmt { m with topLevel := done.push x } fuel h acc x with
      | ok p u =>
        have := initFoldLive_append m fuel xs ys p.1 p.2 (done.push x)
        simpa [push_append_toArray] using this
      | exn p e =>
        cases hd : globalsDirty h acc true x with
        | mk h' r =>
          cases r with
          | mk acc' b =>
            have := initFoldLive_append m fuel xs ys h' acc' (done.push x)
            simpa [push_append_toArray] using this
      | timeout =>
        cases hd : globalsDirty h acc true x with
        | mk h' r =>
          cases r with
          | mk acc' b =>
            have := initFoldLive_append m fuel xs ys h' acc' (done.push x)
            simpa [push_append_toArray] using this
      | unsupported msg =>
        cases hd : globalsDirty h acc true x with
        | mk h' r =>
          cases r with
          | mk acc' b =>
            have := initFoldLive_append m fuel xs ys h' acc' (done.push x)
            simpa [push_append_toArray] using this

/-- **The world, from the run.** `initWorld` is the live pipeline over the
whole top level, read off as heap + resolved globals; a chain that has
computed the pipeline's final `(h, acc)` gets the world for free. -/
theorem initWorld_of_run {m : Module} {h : Heap} {acc : GlobalsAcc}
    (hrun : initFoldLive m initExecFuel #[] [] #[] m.topLevel.toList = (h, acc)) :
    initWorld m = { heap := h, globals := resolvedG acc } := by
  rw [initWorld, hrun]

/-- The two projections a caller actually asks for, so a chain never has
to re-reduce the world to read one of them. -/
theorem initWorld_heap_of_run {m : Module} {h : Heap} {acc : GlobalsAcc}
    (hrun : initFoldLive m initExecFuel #[] [] #[] m.topLevel.toList = (h, acc)) :
    (initWorld m).heap = h := by
  rw [initWorld_of_run hrun]

theorem initWorld_globals_of_run {m : Module} {h : Heap} {acc : GlobalsAcc}
    (hrun : initFoldLive m initExecFuel #[] [] #[] m.topLevel.toList = (h, acc)) :
    (initWorld m).globals = resolvedG acc := by
  rw [initWorld_of_run hrun]

/-! ## Inside one statement: the dict-items shell

The one control shell `execStmt` cannot express is the init `for k, v in
d.items():` loop, and on a real module it is where the initializer's weight
sits (the sunfish `pst` pipeline is one such statement). These are its
per-ITERATION equations — the same service `initFoldLive_fold` / `_exec` do
for the top level, one level in — so a chain can consume the loop one entry
at a time instead of asking for all of it at once.

**Why the shell's unfolding is hand-stated.** `initExecStmt` matches the
items shell through ARRAY LITERALS (`#[]` for the call's args and kwargs),
and Lean's match-equation generator goes through `Array.getLit` under a
sparse-cases motive and fails outright ("failed to generate equality
theorems for match expression `initExecStmt.match_3`") — which takes out
`rw`, `simp` and `unfold` at that head together. That is §L11 finding 1
again, on a second definition, and the fix is the one `Ref.ray` and `drain`
already use: state the unfolding yourself, prove it `rfl`, and never mention
the definition again. Reduction on a CONCRETE statement is unaffected. -/

private def itemsMsg : String :=
  "'.items()' on a non-dict receiver is outside the init shell (docs/memory-model.md §module-init execution)"

/-- `initExecStmt`'s items-shell arm, unfolded BY HAND (see the section note:
the `#[]` patterns take out the generated equations). Everything downstream
of the shell goes through this equation rather than through the definition. -/
theorem initExecStmt_items_unfold (mV : Module) (fuel : Nat) (h : Heap)
    (acc : GlobalsAcc) (target d : Expr) (body : Array Stmt) (sp sp' sp'' : Span) :
    initExecStmt mV (fuel + 1) h acc
        (.forStmt target (.call (.attribute d "items" sp) #[] #[] Option.none sp') body #[] sp'')
      = (match evalExpr mV fuel ⟨⟨h, resolvedG acc, [], []⟩, []⟩ d with
         | .ok st dv =>
           (match dv with
            | .ref a =>
              (match Heap.get? st.world.heap a with
               | some (.dict entries _) =>
                 initItemsLoop mV fuel st.world.heap acc a entries.size 0 target body.toList
               | _ => .unsupported itemsMsg)
            | _ => .unsupported itemsMsg)
         | .exn st e => .exn (st.world.heap, acc) e
         | .timeout => .timeout
         | .unsupported msg => .unsupported msg) := rfl

/-- **The items shell, entered.** A fold-refused `for … in d.items():` with
no `else` runs the shell over the receiver's own dict, at the size the
iterator saw when it was created. -/
theorem initExecStmt_items {mV : Module} {fuel : Nat} {h : Heap}
    {acc : GlobalsAcc} {target d : Expr} {body : Array Stmt}
    {sp sp' sp'' : Span} {a : Addr} {st : FrameState} {entries : Array (RVal × RVal)}
    {sv : Nat}
    (hd : evalExpr mV fuel ⟨⟨h, resolvedG acc, [], []⟩, []⟩ d = .ok st (.ref a))
    (ho : Heap.get? st.world.heap a = some (.dict entries sv)) :
    initExecStmt mV (fuel + 1) h acc
        (.forStmt target (.call (.attribute d "items" sp) #[] #[] Option.none sp') body #[] sp'')
      = initItemsLoop mV fuel st.world.heap acc a entries.size 0 target body.toList := by
  rw [initExecStmt_items_unfold, hd]
  simp only [ho]

/-- **One entry.** The loop re-reads the dict every step (CPython's
`dict_items` iterator: live entries, and a size change is the faithful
`RuntimeError`), binds the target, flushes, runs the body, and comes back at
`i + 1`. -/
theorem initItemsLoop_step {mV : Module} {fuel : Nat} {h h' : Heap}
    {acc acc₁ acc₂ : GlobalsAcc} {a : Addr} {n i : Nat} {target : Expr}
    {body : List Stmt} {entries : Array (RVal × RVal)} {sv : Nat} {env₀ : Env}
    (ho : Heap.get? h a = some (.dict entries sv))
    (hn : entries.size = n) (hi : i < entries.size)
    (hasg : assignToH h [] target (.tuple #[entries[i].1, entries[i].2]) = .ok env₀)
    (hflush : flushInitLocals mV acc env₀ = some acc₁)
    (hbody : initBodyStmts mV fuel h acc₁ body = .ok (h', acc₂) .next) :
    initItemsLoop mV (fuel + 1) h acc a n i target body
      = initItemsLoop mV fuel h' acc₂ a n (i + 1) target body := by
  subst hn
  rw [initItemsLoop.eq_2, ho]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hi, ↓reduceDIte, hasg, hflush, hbody]

/-- **The loop's end.** Past the last entry the shell returns the state it
holds. -/
theorem initItemsLoop_done {mV : Module} {fuel : Nat} {h : Heap}
    {acc : GlobalsAcc} {a : Addr} {n i : Nat} {target : Expr} {body : List Stmt}
    {entries : Array (RVal × RVal)} {sv : Nat}
    (ho : Heap.get? h a = some (.dict entries sv))
    (hn : entries.size = n) (hi : ¬ i < entries.size) :
    initItemsLoop mV (fuel + 1) h acc a n i target body = .ok (h, acc) () := by
  subst hn
  rw [initItemsLoop.eq_2, ho]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hi, ↓reduceDIte]

/-! ## Inside one iteration: the body, statement by statement

`initBodyStmts` runs an items-loop body ONE statement at a time, each in a
fresh empty-locals frame over the current live globals, flushing after each.
These are its two equations — the chop that lets a body statement be priced
(or hypothesised) on its own. -/

theorem initBodyStmts_nil (mV : Module) (fuel : Nat) (h : Heap) (acc : GlobalsAcc) :
    initBodyStmts mV fuel h acc [] = .ok (h, acc) .next := by
  rw [initBodyStmts]

/-- One body statement that runs to `.next`. -/
theorem initBodyStmts_cons {mV : Module} {fuel : Nat} {h : Heap} {acc acc' : GlobalsAcc}
    {s : Stmt} {rest : List Stmt} {st : FrameState}
    (hex : execStmt mV fuel ⟨⟨h, resolvedG acc, [], []⟩, []⟩ s = .ok st .next)
    (hflush : flushInitLocals mV acc st.locals = some acc') :
    initBodyStmts mV (fuel + 1) h acc (s :: rest)
      = initBodyStmts mV fuel st.world.heap acc' rest := by
  rw [initBodyStmts.eq_3, hex]
  simp only [hflush]

end LeanModels.Python
