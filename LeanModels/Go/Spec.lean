import LeanModels.Go.Stmt
import LeanModels.Go.SpecAttr

/-!
# The Go tier's specification lemmas

M1 inch 1, fourth part. Every lemma here is registered `@[go_spec]`.

## The split, from theorem one — STMT-65 / `docs/statement-cookbook.md` §6

The law's axis is *"does the STATEMENT mention the interpreter?"*, and the
measured stake is that 65% of the flagship estate survived a definition
swap because it did not. So this file is in two halves and they are
**separated by that criterion and not by subject**:

* **§1 THE SPEC HALF.** Statements about the mathematics — integer
  representation, the zero value, the language-version predicate, the
  refusal taxonomy's shape. **None of them mention `execStmt`,
  `evalExpr`, `GoM`, fuel or a world.** If the walker is rewritten, every
  one of these recompiles unchanged.
* **§2 THE INTERPRETER HALF.** Statements that necessarily mention the
  walker. This is the re-founding scope, and it is deliberately the
  smaller half.

The cookbook's trap is *"writing a spec-side fact into an
interpreter-shaped statement because that is where you needed it"*, and
the temptation here is real: it is easier to state "the walker never
refuses `undefined`" than to state that `GoRefusal`'s image excludes it.
The second is the spec-side fact, so it is where the gate lives — and the
interpreter-side corollary in §2 then costs one line and carries no
content of its own.
-/

namespace LeanModels.Go

/-! ## §1 THE SPEC HALF — no statement below mentions the interpreter -/

/-! ### 1.1 Integer overflow is DEFINED — the charter's headline, checkable

The Go specification, "Integer overflow": unsigned operations are
"computed modulo 2ⁿ"; signed ones "may legally overflow and the resulting
value exists and is deterministically defined". `docs/c-tier-charter.md`
§2.2(a) needed *two* rules and a refusal between them; Go needs one. -/

/-- Unsigned overflow wraps, and the spec invites programs to rely on it. -/
@[go_spec] theorem uint8_wraps : IntKind.wrap IntKind.uint8 256 = 0 := by decide
@[go_spec] theorem uint8_wraps_one : IntKind.wrap IntKind.uint8 255 = 255 := by decide
@[go_spec] theorem uint8_wraps_neg : IntKind.wrap IntKind.uint8 (-1) = 255 := by decide

/-- **Signed overflow wraps and is DEFINED.** In C this is undefined
behaviour and the C tier must refuse it; here it is an ordinary value. -/
@[go_spec] theorem int8_max_plus_one : IntKind.wrap IntKind.int8 128 = -128 := by decide
@[go_spec] theorem int8_min_minus_one : IntKind.wrap IntKind.int8 (-129) = 127 := by decide
@[go_spec] theorem int8_in_range : IntKind.wrap IntKind.int8 127 = 127 := by decide

/-- Reduction is idempotent: a value already in range is unchanged. This
is what makes `GoVal.mkInt` safe to apply at every arithmetic site. -/
@[go_spec] theorem wrap_idem_int8 (n : Int) :
    IntKind.wrap IntKind.int8 (IntKind.wrap IntKind.int8 n)
      = IntKind.wrap IntKind.int8 n := by
  simp [IntKind.wrap, IntKind.int8, IntKind.modulus]
  omega

/-! ### 1.2 The zero value — "The zero value" -/

@[go_spec] theorem zero_bool : GoVal.zeroBool = GoVal.boolV false := rfl
@[go_spec] theorem zero_string : GoVal.zeroString = GoVal.stringV [] := rfl
@[go_spec] theorem zero_int (k : IntKind) : GoVal.zeroInt k = GoVal.intV k 0 := rfl

/-! ### 1.3 The language-version predicate — the versioning exemplar

`docs/go-charter.md` §3 measured this as the family's copies-vs-deltas
test case: ONE compiler invocation applies BOTH scoping rules to
byte-identical loop bodies, selected per FILE. The model therefore carries
the version as data and branches on it — it does not fork into two models.
These rows are the branch, stated about the predicate alone. -/

@[go_spec] theorem loopvars_go121 :
    LangVersion.perIterationLoopVars LangVersion.go121 = false := by decide
@[go_spec] theorem loopvars_go122 :
    LangVersion.perIterationLoopVars LangVersion.go122 = true := by decide
/-- Every later version keeps per-iteration scoping — the delta is a
threshold, not a special case. -/
@[go_spec] theorem loopvars_go123 :
    LangVersion.perIterationLoopVars ⟨1, 23⟩ = true := by decide

/-! ### 1.3b FRAME PREDICATES for the store — the substrate the loop
induction needs

`docs/statement-cookbook.md` §9. A loop induction over a Go program is an
induction over what the STORE does, so before the induction can be
written the store needs the two lemmas every frame argument uses: a write
is visible at the address written, and invisible everywhere else.

These are stated about **pure world functions** — `wStore`, `wRead`,
`wLookup` — and mention no interpreter, so they are spec-half by the
cookbook's axis and they survive a walker redefinition. They are landed
ahead of the induction that consumes them because they are reusable by
every later theorem about mutation, not just by `bitLen`'s. -/

/-- The pure shape `storeLocal` produces: shadow the address, keep the rest. -/
def wStore (w : GoWorld) (a : Addr) (v : GoVal) : GoWorld :=
  { w with store := (a, v) :: w.store.filter (fun p => p.1 != a) }

/-- Resolve a name to its address. -/
def wLookup (w : GoWorld) (name : String) : Option Addr :=
  (w.locals.find? (fun p => p.1 == name)).map (·.2)

/-- Read an address. -/
def wRead (w : GoWorld) (a : Addr) : Option GoVal :=
  (w.store.find? (fun p => p.1 == a)).map (·.2)

/-- The list fact both frame lemmas rest on: filtering out `a` does not
disturb a lookup of any OTHER address. Proved by induction on the store
rather than by a library lemma, because the shapes did not line up and an
explicit induction is cheaper to keep than a fragile rewrite. -/
theorem find_filter_ne (l : List (Addr × GoVal)) (a b : Addr) (h : b ≠ a) :
    (l.filter (fun p => p.1 != a)).find? (fun p => p.1 == b)
      = l.find? (fun p => p.1 == b) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hxa : x.1 = a
    · have hxb : ¬ (x.1 = b) := by rw [hxa]; exact fun hc => h hc.symm
      rw [List.filter_cons]
      simp only [hxa, bne_self_eq_false, Bool.false_eq_true, if_false]
      rw [ih, List.find?_cons_of_neg]
      simp [hxb]
    · rw [List.filter_cons]
      simp only [hxa, bne_iff_ne, ne_eq, not_false_eq_true, if_true]
      by_cases hxb : x.1 = b
      · rw [List.find?_cons_of_pos, List.find?_cons_of_pos] <;> simp [hxb]
      · rw [List.find?_cons_of_neg, List.find?_cons_of_neg, ih] <;> simp [hxb]

/-- **A write is visible where it was written.** -/
@[go_spec] theorem wRead_wStore_same (w : GoWorld) (a : Addr) (v : GoVal) :
    wRead (wStore w a v) a = some v := by
  simp [wRead, wStore]

/-- **A write is invisible everywhere else** — the frame half. -/
@[go_spec] theorem wRead_wStore_other (w : GoWorld) (a b : Addr) (v : GoVal)
    (h : b ≠ a) : wRead (wStore w a v) b = wRead w b := by
  have hb : ¬ (a = b) := fun hc => h hc.symm
  simp only [wRead, wStore]
  rw [List.find?_cons_of_neg (by simp [hb])]
  rw [find_filter_ne _ a b h]

/-- **A write moves no binding.** Names keep their addresses; only the
address's contents change. -/
@[go_spec] theorem wLookup_wStore (w : GoWorld) (a : Addr) (v : GoVal)
    (name : String) : wLookup (wStore w a v) name = wLookup w name := by
  simp [wLookup, wStore]

/-! ### 1.3c FRAME PREDICATES FOR SLICES — the aliasing-aware pair

§1.3b's `wRead_wStore_same`/`_other` frame a write to an ADDRESS. A slice
write is not addressed that way: it goes through a header into a backing
array, and **two different headers can name the same element**. So the
pair needs its aliasing-aware form, and it is the slice analogue of the
two above rather than a replacement for them.

The aliasing question is entirely `off + i`: two headers over the same
backing array name the same element exactly when their offsets and
indices sum alike. That is why the predicate below mentions no header at
all — it is arithmetic, and stating it that way is what keeps these in
the spec half. -/

/-- Read element `i` through a header at offset `off`. -/
def sliceElem (es : List GoVal) (off i : Nat) : Option GoVal := es[off + i]?

/-- **Two headers name the same element.** Same backing array is a
separate condition, handled by §1.3b's address-level pair — this is the
within-array half. -/
def AliasAt (off₁ i₁ off₂ i₂ : Nat) : Prop := off₁ + i₁ = off₂ + i₂

/-- **A write through one slice IS visible through an overlapping one.**
This is the row `docs/backlog/go.md` §G17 measured a copy model failing:
`out[0] = 'X'` seen through `base`. -/
@[go_spec] theorem sliceElem_set_alias (es : List GoVal) (off₁ i₁ off₂ i₂ : Nat)
    (v : GoVal) (ha : AliasAt off₁ i₁ off₂ i₂) (h : off₁ + i₁ < es.length) :
    sliceElem (es.set (off₁ + i₁) v) off₂ i₂ = some v := by
  unfold AliasAt at ha
  unfold sliceElem
  rw [← ha]
  exact List.getElem?_set_self h

/-- **And INVISIBLE through a slice that does not overlap it.** The frame
half: everything the write did not name is untouched. -/
@[go_spec] theorem sliceElem_set_disjoint (es : List GoVal) (off₁ i₁ off₂ i₂ : Nat)
    (v : GoVal) (hd : ¬ AliasAt off₁ i₁ off₂ i₂) :
    sliceElem (es.set (off₁ + i₁) v) off₂ i₂ = sliceElem es off₂ i₂ := by
  unfold AliasAt at hd
  unfold sliceElem
  exact List.getElem?_set_ne hd

/-- **Across DIFFERENT backing arrays a write is invisible**, and that
half needs no new lemma: backing arrays are store entries keyed by
address, so it is §1.3b's `wRead_wStore_other` unchanged. Recorded here so
the pair is findable as a pair. -/
@[go_spec] theorem slice_write_other_backing (w : GoWorld) (a b : Addr) (v : GoVal)
    (h : b ≠ a) : wRead (wStore w a v) b = wRead w b :=
  wRead_wStore_other w a b v h

/-! ### 1.4 THE ZERO-UB GATE

`docs/go-charter.md`'s headline is that the Go specification never says
"undefined". `docs/family-architecture.md` §4.3's Go row turns that into
an obligation: cause 2 is expected EMPTY and should be gated.

This is the gate, and it is a statement about a function between two
enumerations — no interpreter, no world, no fuel. -/

/-- **The Go tier cannot refuse `undefined`.** Not "does not": cannot.

Stated against Core's own `isUndefined`, which Core lifted from the ES
lane so the gate is written once per family. This tier's contribution is
the narrower `GoRefusal`; the predicate is everyone's. -/
@[go_spec] theorem goRefusal_never_undefined (r : GoRefusal) (π : SpecRef) :
    (r.toCore π).isUndefined = false := by
  cases r <;> rfl

/-- The image, spelled out, so a reader can see the bucket is exactly
three and which three. -/
@[go_spec] theorem goRefusal_image (r : GoRefusal) (π : SpecRef) :
    (r.toCore π).className = "unsupported"
      ∨ (r.toCore π).className = "environment"
      ∨ (r.toCore π).className = "order-dependence" := by
  cases r <;> simp [GoRefusal.toCore, RefusalCause.className]

/-- Non-vacuity: `undefined` really is a constructor of the family type,
so the theorem above is a restriction and not a statement about an empty
type. Without this row, deleting `undefined` from `RefusalCause` would
make the gate pass for the wrong reason. -/
@[go_spec] theorem undefined_is_a_real_cause (π : SpecRef) :
    (RefusalCause.undefined π).isUndefined = true := rfl

/-! ## §2 THE INTERPRETER HALF — everything below mentions the walker

Deliberately thin. This is the re-founding scope if the substrate or the
walker is redefined. -/

/-! ### 2.1 The refusal covenant

A refusal is not an error a program can catch: it is not in ρ, so no
`recover` can reach it. It lands in Core's `Loud`, which is the
state-DISCARDING channel, while a panic lands in ρ, which is
state-RETAINING — the distinction Core's layer order exists to keep.

`SemMWith W ρ π σ α` unfolds to `W → Except (Loud π σ) (Except ρ α × W)`, so
applying the computation to a world IS the run; Core exports no separate
`run`. (This tier instantiates `π := SpecRef`, `σ := Unit`: it cites a clause
and keeps no diagnostic snapshot.) -/

@[go_spec] theorem refuseGo_run
    (W : Type) (w : W) (r : GoRefusal) (π : SpecRef) (m : String) :
    (refuseGo (W := W) (ρ := Panic) (α := Unit) r π m) w
      = .error (.unsupported (r.toCore π) m none) := rfl

@[go_spec] theorem exhausted_is_not_catchable (W : Type) (w : W) :
    (LeanModels.exhausted : SemMWith W Panic SpecRef Unit Unit) w
      = .error .timeout := rfl

/-- The interpreter-side corollary of §1.4, and it carries no content of
its own — which is the point of having put the gate in the spec half.
Every refusal this tier emits carries a cause drawn from `GoRefusal`, and
§1.4 says that image is never `undefined`. -/
@[go_spec] theorem refuseGo_cause_never_undefined (r : GoRefusal) (π : SpecRef) :
    (r.toCore π).isUndefined = false :=
  goRefusal_never_undefined r π

/-! ### 2.1b THE STORE OPERATIONS, opened by the seam

**These are the three lemmas `docs/backlog/go.md` §G8 recorded as
unprovable**, and they are what the loop induction steps through. §G8's
blocker was real — `lookupLocal name w` is not definitionally the match
on `w.locals.find? …` — and `LeanModels/Go/Obs.lean` is the answer: with
`go_run` opening the stack, each proof is four lines instead of an
open-ended fight with `simp`.

They connect the interpreter's monadic helpers to §1.3b's PURE world
functions, which is exactly the join an induction over mutation needs:
the pure side carries the frame reasoning, these carry the stepping. -/

@[go_spec] theorem lookupLocal_ok {w : GoWorld} {name : String} {a : Addr}
    (h : wLookup w name = some a) :
    lookupLocal name w = .ok (.ok a, w) := by
  unfold wLookup at h
  cases hf : w.locals.find? (fun p => p.1 == name) with
  | none => rw [hf] at h; simp at h
  | some p =>
    rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h
    simp only [lookupLocal, go_run, hf, h]

@[go_spec] theorem loadAddr_ok {w : GoWorld} {a : Addr} {v : GoVal}
    (h : wRead w a = some v) : loadAddr a w = .ok (.ok v, w) := by
  unfold wRead at h
  cases hf : w.store.find? (fun p => p.1 == a) with
  | none => rw [hf] at h; simp at h
  | some p =>
    rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h
    simp only [loadAddr, go_run, hf, h]

/-- A write lands in exactly the world §1.3b's frame lemmas describe —
the join between the monadic step and the pure reasoning. -/
@[go_spec] theorem storeLocal_ok {w : GoWorld} {name : String} {a : Addr}
    {v : GoVal} (h : wLookup w name = some a) :
    storeLocal name v w = .ok (.ok ⟨⟩, wStore w a v) := by
  simp only [storeLocal, go_run, lookupLocal_ok h, wStore]

/-! ### 2.2 Flow short-circuits — cookbook §13

A non-normal flow stops the sequence. Stated at the sequence combinator,
which is where the rule lives. -/

@[go_spec] theorem execSeq_nil (fuel : Nat) (w : GoWorld) :
    (execSeq [] (fuel + 1) []) w = .ok (.ok Flow.normal, w) := rfl

/-- **Fuel exhaustion is `timeout`, never a refusal**, and it is reachable
at every statement form — the walker recurses on fuel alone. -/
@[go_spec] theorem execSeq_no_fuel (body : List Stmt) (w : GoWorld) :
    (execSeq [] 0 body) w = .error .timeout := rfl

@[go_spec] theorem execStmt_no_fuel (st : Stmt) (w : GoWorld) :
    (execStmt [] 0 st) w = .error .timeout := rfl

/-- Bare `for {}` — 47.0% of the standard library's `for` loops — is
where that stops being a formality: with no condition, only fuel bounds
it. -/
@[go_spec] theorem bare_for_exhausts (w : GoWorld) :
    (execLoop [] 0 none none [] []) w = .error .timeout := rfl

@[go_spec] theorem flow_normal_isNormal : Flow.normal.isNormal = true := rfl
@[go_spec] theorem flow_returned_not_normal (v) : (Flow.returned v).isNormal = false := rfl
@[go_spec] theorem flow_broke_not_normal (l) : (Flow.broke l).isNormal = false := rfl
@[go_spec] theorem flow_continued_not_normal (l) : (Flow.continued l).isNormal = false := rfl

/-! ### 2.3 The empty statement really is a no-op -/

@[go_spec] theorem exec_empty (fuel : Nat) (w : GoWorld) :
    (execStmt [] (fuel + 1) Stmt.empty) w = .ok (.ok Flow.normal, w) := rfl

end LeanModels.Go
