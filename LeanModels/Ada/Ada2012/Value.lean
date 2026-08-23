import LeanModels.Ada.Ast

/-!
# M2 inch 1 — the value layer, and the one decision that cannot be retrofitted

`docs/ada-semantics-design.md` §4. The ARM edition this file is about is
**Ada 2012**, which is why it is here and not in the trunk: the AST is
kind-agnostic and provably edition-insensitive (`LeanModels/Ada.lean`), and
**meaning is not** — the ARM carries 953 Legality-Rule paragraphs against 572
Syntax ones, and it is the first number that differs between editions.

**No interpreter is built here.** This is the value layer plus the substrate
shape the walker will be typed in, and the `#guard`s that pin the one
decision the rest of M2 rests on.

## THE DECISION: a constraint violation RAISES, it does not wrap and does not refuse

The C lane's `close` is the model for "the one function where the decision
lives" (`docs/backlog.md` §L57): in range → the value, out of range and
unsigned → wrap, out of range and signed → **REFUSE**, because C leaves
signed overflow undefined.

**Ada's answer is the opposite and it is the whole reason this tier is
cheap where C's is expensive.** An out-of-range scalar is not undefined in
Ada — it is a *defined raise of a predefined exception*, `Constraint_Error`
(ARM 4.6, 5.2, and the checks of ARM 3.5). So `constrain` below raises, and
the raise is an ORDINARY OUTCOME travelling in `ρ`, never a refusal.

Getting this backwards would make the tier refuse a large fraction of a suite
that is largely *about* constraint checking, and it is not recoverable later:
every rule that can produce a scalar would have to be revisited.

## SUBSTRATE: defined BY SHAPE, with an adoption note

`Core.SemM` and `Core.RefusalCause` are ruled and imminent
(`docs/family-architecture.md`, ruling `14bdd7a`) but not landed. Per the
dispatch, this file defines them **by shape** exactly as
`LeanModels/Es/Completion.lean` did, so that adoption is an import change and
not a redesign. Every definition below that Core will own is marked
**`ADOPT`**; nothing else in the Ada lane may define these.
-/

namespace LeanModels.Ada.Ada2012

/-! ## The tier payload — `π` = an ARM paragraph reference -/

/--
A citation into the Ada Reference Manual, in the ARM's own form:
clause `3.5.4`, paragraph `10`, optionally a version suffix (`10/3`).

This is the tier payload `π` of the `RefusalCause π` ruling. C instantiates
it with a J.2 index, ES with a host-hook name; Ada's is a paragraph, which is
also what makes the paragraph map (`docs/ada-charter.md` §5.8) generable from
the tier rather than written beside it — a refusal that cites 1.1.5 is a row.
-/
structure ArmRef where
  clause : String
  para : String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- `3.5.4(10/3)` — the ARM's own citation spelling. -/
def ArmRef.toString (r : ArmRef) : String := s!"{r.clause}({r.para})"

instance : ToString ArmRef := ⟨ArmRef.toString⟩

/-! ## ADOPT — the four refusal classes, parameterized by the tier payload -/

/--
**ADOPT** (`Core.RefusalCause` when it lands). The four §5.2 classes are
family law; the payload is the tier's.

**All four are present even where Ada expects one to be empty**, which is the
ruling's sharpest clause: *an expected-empty class is PRESENT AND GATED,
never absent* — omitting it makes the emptiness a fact about the type,
invisible to a scoreboard that then cannot tell *"this language has no such
behaviour"* from *"this tier did not model that column."* **A gate needs a
constructor to be about.**
-/
inductive RefusalCause (π : Type) where
  /-- Out of tier. Retires by climbing a rung. -/
  | unsupportedConstruct (at_ : π)
  /-- **The language says this run has no meaning.** For Ada this is ARM
  1.1.5's *erroneous execution* — the class with no language-specified bound
  on the possible effect. **Never retires: it is the product.** Measured at
  23 paragraphs in clauses 1-13, concentrated in ARM 11.5 (*Suppressing
  Checks*) and ARM 13.9.1 (*Data Validity*). -/
  | undefined (at_ : π)
  /-- Outside the modeled slice — a library unit this tier does not model.
  Retires by widening the slice. -/
  | environment (at_ : π)
  /-- Several admissible orders and the model cannot show the observable
  invariant under all of them. **GATED for Ada**: see `orderDependenceGate`.
  -/
  | orderDependence (at_ : π)
  deriving Repr, Inhabited

/-- Ada's cause type: the four classes, carrying ARM paragraphs. -/
abbrev Cause := RefusalCause ArmRef

/-- The class name, so a cause rendered into a message string is still
mechanically recoverable while §the correction note's divergence stands. -/
def Cause.tag : Cause → String
  | .unsupportedConstruct r => s!"unsupportedConstruct@{r.toString}"
  | .undefined r => s!"undefined@{r.toString}"
  | .environment r => s!"environment@{r.toString}"
  | .orderDependence r => s!"orderDependence@{r.toString}"

/--
**THE GATE the ruling requires.** Ada's unspecified-order surface is real —
"unspecified" occurs 109 times in the core clauses — but whether it ever
*fires as a refusal* is a question about the CORPUS and a running model, and
neither exists yet.

So the expectation is written down as a predicate rather than as an absent
constructor. When the inch-6 scoreboard runs, this is the claim that gets
checked: if it holds, the bucket is empty and that is a measured fact about
Ada's v0 core; if it fails, the failing site is the finding.

**It is deliberately not asserted here.** A gate asserted before the thing it
gates exists is decoration.
-/
def orderDependenceGate (cs : List Cause) : Bool :=
  cs.all fun c => match c with
    | .orderDependence _ => false
    | _ => true

/-- The erroneous-execution citation, so `undefined` always carries the
clause that defines it rather than an ad-hoc string. -/
def erroneousExecution : ArmRef := { clause := "1.1.5", para := "9" }

/-! ## ADOPT — the base outcome and the semantic monad -/

/-!
## ADOPT — the base outcome, and a CORRECTION

The first version of this file defined `Halt` as a bespoke three-constructor
inductive with a hand-written `Monad` instance, and put the refusal CAUSE
inside its `unsupported` arm. **Both were wrong against the Core that
landed** (`LeanModels/Core/Outcome.lean`, `376735e`), and the second was
wrong in a way the base's own docstring warns about:

> *"A tier that needs more than two causes does **not** extend this type; it
> adds an `.except` layer of its own, which composes for free."*

So the base below is Core's, spelled Core's way — `Except Loud`, which gets
its `Monad` from `Except` rather than from twenty hand-written lines. When
`LeanModels/Core/Outcome.lean` is imported, these three definitions delete.
-/

/-- **ADOPT** (`Core.Loud`). The model giving up — never a statement about
the program. Both arms DISCARD state, which is what distinguishes them from a
language-level raise: there is no meaningful world to hand back, because the
model stopped rather than the program.

Note `unsupported` carries **only a message**. The four-class `Cause` above
does not go here; see the correction note. -/
inductive Loud where
  | timeout
  | unsupported (msg : String)
  deriving Repr, Inhabited, BEq, DecidableEq

/-- **ADOPT** (`Core.Halt`). A run either produces a value or halts loudly. -/
abbrev Halt := Except Loud

/-! ## The values

Ada's scalar values, and one representation choice that is the ARM's rather
than a convenience: **`Boolean` and `Character` ARE enumeration types** (ARM
3.5.3, *Boolean Types*; ARM 3.5.2, *Character Types*), so one `enum` arm
covers user enumerations, `Boolean` and `Character` alike. A tier that gave
`Boolean` its own constructor would be modelling a language Ada is not. -/

/-- An integer subtype: a name and a range (ARM 3.5.4, *Integer Types*).
The bounds are carried in the VALUE rather than looked up, because the
constraint check is the hot path and a value that cannot say what it must
satisfy cannot be checked at all. -/
structure IntSubtype where
  typeName : String
  lo : Int
  hi : Int
  deriving Repr, DecidableEq, Inhabited, BEq

/-- An enumeration subtype (ARM 3.5.1). `first`/`last` are POSITIONS, so a
subtype of an enumeration is a narrowing of the range and not a new list. -/
structure EnumSubtype where
  typeName : String
  literals : Array String
  first : Nat
  last : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

/-- A scalar value. -/
inductive Val where
  | int (sub : IntSubtype) (v : Int)
  | enum (sub : EnumSubtype) (pos : Nat)
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `Standard.Boolean` — an enumeration type, per ARM 3.5.3. -/
def booleanType : EnumSubtype :=
  { typeName := "Boolean", literals := #["FALSE", "TRUE"], first := 0, last := 1 }

def Val.ofBool (b : Bool) : Val := .enum booleanType (if b then 1 else 0)

/--
An abrupt completion in Ada.

`raised` is an exception OCCURRENCE, not an arbitrary value — Ada names a
declared exception (ARM 11.1, 11.3) and carries an identity plus a message
(ARM 11.4.1). That is the opposite of ES, whose `throw` must carry any
language value, and both are right: `ρ` is a parameter.

`goto` is deliberately absent — 39 of 4,188 tests, intra-subprogram (ARM
5.8), and putting it here would make every statement rule carry a
label-continuation it almost never needs.
-/
inductive Abrupt where
  /-- ARM 11.1, 11.3, 11.4. `name` is the exception's identity. -/
  | raised (name : String) (message : String)
  /-- ARM 6.5, *Return Statements*. -/
  | ret (value : Option Val)
  /-- ARM 5.7, *Exit Statements*. `target` is the loop name, if written. -/
  | exitLoop (target : Option String)
  deriving Repr, Inhabited, BEq, DecidableEq

/-! ## THE DECISION

`constrain` is this tier's `close`, and it is where Ada and C part company.
-/

/-- The predefined exceptions of ARM 11.1. Named rather than stringly-typed
at the call sites, so a raise cites the clause that declares it. -/
def constraintError : String := "Constraint_Error"
def programError : String := "Program_Error"

/--
**THE ONE DECISION THAT CANNOT BE RETROFITTED.**

In range → the value. Out of range → **raise `Constraint_Error`** (ARM 4.6,
5.2; the checks of ARM 3.5). Not a wrap, and — the part that matters —
**not a refusal**: the ARM defines this outcome completely, so refusing it
would be a false statement about the language, and would refuse most of a
suite that is largely about constraint checking.

Compare the C lane's `close` (`docs/backlog.md` §L57): *out of range and
signed → REFUSE*, because C leaves signed overflow undefined. Same position
in the design, opposite answer, and the difference is the languages'.
-/
def constrain (sub : IntSubtype) (v : Int) : Except Abrupt Val :=
  if sub.lo ≤ v && v ≤ sub.hi then
    .ok (.int sub v)
  else
    .error (.raised constraintError
      s!"value {v} outside {sub.typeName} range {sub.lo} .. {sub.hi}")

/-- The same rule for an enumeration position (ARM 3.5.1). -/
def constrainEnum (sub : EnumSubtype) (pos : Nat) : Except Abrupt Val :=
  if sub.first ≤ pos && pos ≤ sub.last then
    .ok (.enum sub pos)
  else
    .error (.raised constraintError
      s!"position {pos} outside {sub.typeName} range {sub.first} .. {sub.last}")

/-- Addition, with the result constrained (ARM 4.5.3). The operation itself
is on unbounded `Int` and the CHECK is what makes it Ada's — computing in the
target width first would decide the overflow before the check could see it,
which is the C lane's recorded reason for the same shape. -/
def addOp (sub : IntSubtype) (a b : Int) : Except Abrupt Val :=
  constrain sub (a + b)

/-- Subtraction (ARM 4.5.3). -/
def subOp (sub : IntSubtype) (a b : Int) : Except Abrupt Val :=
  constrain sub (a - b)

/-- Multiplication (ARM 4.5.5). -/
def mulOp (sub : IntSubtype) (a b : Int) : Except Abrupt Val :=
  constrain sub (a * b)

/--
Ada's integer division: **truncation toward zero** (ARM 4.5.5(5)).

Defined here rather than borrowed. Lean's `/` on `Int` is whichever instance
is in scope, and core and Mathlib have not always agreed; a tier whose
division is "whatever `/` resolved to" has not decided anything. Written on
`natAbs` and `Nat` division, both of which are unambiguous, the rounding is
the ARM's and is visible in the source.
-/
def adaDiv (a b : Int) : Int :=
  -- `Int.ofNat` and `decide` rather than a coercion and `==` on `a < 0`:
  -- `a < 0` is a Prop, so comparing two of them with `==` does not
  -- elaborate, and an implicit Nat-to-Int coercion is one more thing that
  -- could resolve differently than intended.
  let q : Int := Int.ofNat (a.natAbs / b.natAbs)
  let signsDiffer : Bool := decide (a < 0) != decide (b < 0)
  if signsDiffer then -q else q

/-- Ada's `rem`, which takes the sign of the LEFT operand (ARM 4.5.5(6)) —
and is therefore not Ada's `mod`, which takes the right operand's. The pair
is a classic divergence and the guards pin both. -/
def adaRem (a b : Int) : Int := a - b * adaDiv a b

/-- Division (ARM 4.5.5). A zero divisor raises `Constraint_Error` — ARM
4.5.5(11) — which is again a DEFINED outcome where C's is undefined. -/
def divOp (sub : IntSubtype) (a b : Int) : Except Abrupt Val :=
  if b == 0 then
    .error (.raised constraintError "division by zero")
  else
    constrain sub (adaDiv a b)


/-- **ADOPT** (`Core.SemM`). `ExceptT` OUTSIDE `StateT`, so the world
survives a raise. Fuel is an INDEX on the step function, never in state. -/
abbrev SemM (W : Type) (ρ : Type) := ExceptT ρ (StateT W Halt)

/-- The tier's usual instantiation. -/
abbrev AdaM (W : Type) := SemM W Abrupt

namespace SemM

/-- Refuse: loud and fuel-independent. Not an error in `ρ` — a refusal is not
something an Ada program can handle.

**The `Cause` is rendered into the message for now, and that is a placeholder
this file names rather than hides.** Core's `Loud` carries no cause and its
docstring says a tier wanting one adds an `.except` layer of its own; the
four-class `RefusalCause π` the ruling assigns to Core has **not landed**
(measured: it exists only in `LeanModels/Es/Completion.lean`). Wiring the
cause structurally is therefore blocked on that divergence being resolved,
and a string is the honest interim — it loses the scoreboard's ability to
bucket without parsing prose, which is precisely why this is a placeholder
and not a design. -/
def refuse (c : Cause) (msg : String) : SemM W ρ α :=
  fun _ => .error (.unsupported s!"[{Cause.tag c}] {msg}")

/-- Fuel exhaustion. The only exhaustion outcome. -/
def timeout : SemM W ρ α := fun _ => .error .timeout

end SemM



/-! ## The gate

`#guard`s on the value layer, non-vacuous by the C lane's test: flip a claim
and Lean must report the failing expression. Every one of these is a fact the
ARM states, cited where it states it. -/

private def Int8 : IntSubtype := { typeName := "Int8", lo := -128, hi := 127 }
private def Nat100 : IntSubtype := { typeName := "Positive100", lo := 1, hi := 100 }

private def isRaise (name : String) : Except Abrupt Val → Bool
  | .error (.raised n _) => n == name
  | _ => false

private def isOk : Except Abrupt Val → Bool
  | .ok _ => true
  | _ => false

/-- `okIs v r` — `r` is exactly `.ok v`.

Written out rather than comparing with `==`, because **`Except` carries no
`BEq` instance in this toolchain** (measured: `failed to synthesize BEq
(Except Abrupt Val)`, three sites). Declaring an orphan `BEq` for a core type
to serve three guards would be the wrong trade — it is a global instance
added for a local convenience, and the next tier to compare an `Except` would
inherit it without asking. This needs only `BEq Val`, which is derived. -/
private def okIs (v : Val) : Except Abrupt Val → Bool
  | .ok w => w == v
  | _ => false

-- In range: the value, not an exception. ARM 3.5.4.
#guard isOk (constrain Int8 0)
#guard isOk (constrain Int8 127)
#guard isOk (constrain Int8 (-128))

-- OUT of range RAISES Constraint_Error -- it does not wrap, and it is NOT a
-- refusal. This is the inch's whole decision, in three lines. ARM 4.6, 5.2.
#guard isRaise constraintError (constrain Int8 128)
#guard isRaise constraintError (constrain Int8 (-129))
#guard isRaise constraintError (constrain Nat100 0)

-- The C lane's `close` WRAPS an unsigned out-of-range value. Ada never
-- wraps: 128 in an 8-bit signed subtype is not -128, it is an exception.
#guard !okIs (.int Int8 (-128)) (constrain Int8 128)

-- Arithmetic overflow is a DEFINED raise, where C's signed overflow is
-- undefined and must refuse. ARM 4.5.3.
#guard isOk (addOp Int8 100 27)
#guard isRaise constraintError (addOp Int8 100 28)
#guard isRaise constraintError (mulOp Int8 100 2)
#guard isOk (subOp Int8 (-100) 28)
#guard isRaise constraintError (subOp Int8 (-100) 29)

-- Division by zero: ARM 4.5.5(11), Constraint_Error, again DEFINED.
#guard isRaise constraintError (divOp Int8 1 0)

-- Ada integer division TRUNCATES toward zero (ARM 4.5.5(5)), which is
-- `Int.tdiv` and NOT `Int.fdiv`. The two are named explicitly rather than
-- comparing against `/`: which instance `/` resolves to on `Int` has
-- differed between core and Mathlib, and a guard that is really about
-- instance resolution is not a guard about Ada. This is the divergence
-- class the ctwin README calls #1, met from the Ada side.
#guard okIs (.int Int8 (-3)) (divOp Int8 (-7) 2)
#guard okIs (.int Int8 3) (divOp Int8 7 2)
#guard adaDiv (-7) 2 == -3
#guard adaDiv 7 (-2) == -3
#guard adaDiv (-7) (-2) == 3

-- `rem` takes the sign of the LEFT operand (ARM 4.5.5(6)). Ada's `mod`
-- takes the right operand's, so the two differ on mixed signs -- the pair
-- is a classic divergence and both halves are pinned here.
#guard adaRem (-7) 2 == -1
#guard adaRem 7 (-2) == 1

-- Boolean IS an enumeration type (ARM 3.5.3), so it goes through the same
-- constructor and the same check as any user enumeration.
#guard Val.ofBool true == .enum booleanType 1
#guard Val.ofBool false == .enum booleanType 0
#guard isOk (constrainEnum booleanType 1)
#guard isRaise constraintError (constrainEnum booleanType 2)

-- A subtype of an enumeration narrows POSITIONS rather than relisting.
private def TrueOnly : EnumSubtype := { booleanType with first := 1, last := 1 }
#guard isRaise constraintError (constrainEnum TrueOnly 0)
#guard isOk (constrainEnum TrueOnly 1)

-- The refusal classes: all four PRESENT, per the ruling. `undefined` carries
-- the clause that defines erroneous execution rather than a loose string.
#guard erroneousExecution.toString == "1.1.5(9)"
#guard (RefusalCause.undefined erroneousExecution : Cause) matches .undefined _

-- THE GATE: `order-dependence` is present and expected empty. The predicate
-- is what inch 6 checks; it holds vacuously on an empty list, and FAILS the
-- moment a site emits one -- which is the point of gating rather than
-- omitting the constructor.
#guard orderDependenceGate []
#guard orderDependenceGate [.undefined erroneousExecution, .environment erroneousExecution]
#guard !orderDependenceGate [.orderDependence { clause := "1.1.4", para := "1" }]

end LeanModels.Ada.Ada2012
