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
@[go_spec] theorem zero_string : GoVal.zeroString = GoVal.stringV "" := rfl
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

/-! ### 1.4 THE ZERO-UB GATE

`docs/go-charter.md`'s headline is that the Go specification never says
"undefined". `docs/family-architecture.md` §4.3's Go row turns that into
an obligation: cause 2 is expected EMPTY and should be gated.

This is the gate, and it is a statement about a function between two
enumerations — no interpreter, no world, no fuel. -/

/-- **The Go tier cannot refuse `undefined`.** Not "does not": cannot. -/
@[go_spec] theorem goRefusal_never_undefined (r : GoRefusal) :
    r.toCause ≠ RefusalCause.undefined := by
  cases r <;> simp [GoRefusal.toCause]

/-- The image, spelled out, so a reader can see the bucket is exactly
three and which three. -/
@[go_spec] theorem goRefusal_image (r : GoRefusal) :
    r.toCause = RefusalCause.unsupportedConstruct
      ∨ r.toCause = RefusalCause.environment
      ∨ r.toCause = RefusalCause.orderDependence := by
  cases r <;> simp [GoRefusal.toCause]

/-- Non-vacuity: `undefined` really is a constructor of the family type,
so the theorem above is a restriction and not a statement about an empty
type. Without this row, deleting `undefined` from `RefusalCause` would
make the gate pass for the wrong reason. -/
@[go_spec] theorem undefined_is_a_real_cause :
    RefusalCause.undefined ≠ RefusalCause.unsupportedConstruct := by decide

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
      = .error (.unsupported (r.toCause.toCore π) (renderRefusal r.toCause π m)
          none) := rfl

@[go_spec] theorem exhausted_is_not_catchable (W : Type) (w : W) :
    (LeanModels.exhausted : SemMWith W Panic SpecRef Unit Unit) w
      = .error .timeout := rfl

/-- The interpreter-side corollary of §1.4, and it carries no content of
its own — which is the point of having put the gate in the spec half.
Every refusal this tier emits renders a cause drawn from `GoRefusal`, and
§1.4 says that image excludes `undefined`. -/
@[go_spec] theorem refuseGo_cause_never_undefined (r : GoRefusal) :
    r.toCause ≠ RefusalCause.undefined :=
  goRefusal_never_undefined r

/-! ### 2.2 Flow short-circuits — cookbook §13

A non-normal flow stops the sequence. Stated at the sequence combinator,
which is where the rule lives. -/

@[go_spec] theorem execSeq_nil (fuel : Nat) (w : GoWorld) :
    (execSeq fuel []) w = .ok (.ok Flow.normal, w) := rfl

@[go_spec] theorem flow_normal_isNormal : Flow.normal.isNormal = true := rfl
@[go_spec] theorem flow_returned_not_normal (v) : (Flow.returned v).isNormal = false := rfl
@[go_spec] theorem flow_broke_not_normal (l) : (Flow.broke l).isNormal = false := rfl
@[go_spec] theorem flow_continued_not_normal (l) : (Flow.continued l).isNormal = false := rfl

/-! ### 2.3 The empty statement really is a no-op -/

@[go_spec] theorem exec_empty (fuel : Nat) (w : GoWorld) :
    (execStmt fuel Stmt.empty) w = .ok (.ok Flow.normal, w) := rfl

end LeanModels.Go
