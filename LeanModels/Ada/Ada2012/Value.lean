import LeanModels.Ada.Ast
import LeanModels.Core.Outcome

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

## SUBSTRATE: ADOPTED from `LeanModels/Core/Outcome.lean`

Inch 1 defined the outcome layer **by shape**, marked every such definition
`ADOPT`, and said adoption should be an import change rather than a redesign.
This is that change (`docs/backlog/ada.md` §2026-08-23-ada-2): the by-shape
`RefusalCause` / `Loud` / `Halt` / `SemM` are **gone**, and Core's are
imported. **π = `ArmRef`** (the paragraph a refusal cites), **σ = `Unit`**
(no diagnostic snapshot; the consumer is registered, not claimed — see the
ticket).

**THE TWO-CHANNEL MAPPING, which is the load-bearing content of the
adoption.** Core separates a state-RETAINING channel from a state-DISCARDING
one, and Ada needs both, on opposite sides of the line inch 1 drew:

* **`ρ` = `Abrupt`, via `raiseIn` — every Ada exception, `Constraint_Error`
  first among them.** ARM 11.4: an exception PROPAGATES, and the world it was
  raised in survives for a handler to see. State-retention here is the
  language, not an implementation nicety.
* **`π` = `ArmRef`, via `refuse` — constructs outside the modelled tier, and
  nothing else.** Never `Constraint_Error`, which the ARM defines completely.

Inch 1's load-bearing guard (`!okIs (.int Int8 (-128)) (constrain Int8 128)`)
is what makes the mapping legible: out-of-range RAISES, so it belongs on `ρ`.
Had `constrain` refused, this adoption would have wired Ada's most common
outcome into the give-up channel — irrecoverably, because every rule that can
produce a scalar would have to be revisited.

**THE PRICE, PAID KNOWINGLY.** Ada imported ZERO `Core` modules until this
line, which is why inch 1's green survived a 53-commit rebase untouched. That
property ends here: Core changes can now break this tier, and its greens stop
being base-independent. `Core/Order.lean` arrives in the closure as
`Core/Outcome.lean`'s own import — **in the closure is not in use**: nothing
here mentions `FlatLe`, and the `_mono` corollaries it backs are adopted by
the ticket that gives this tier recursion (inch 3+), not by this one.
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

/-- `3.5.4(10/3)` — the ARM's own citation spelling.

**An EMPTY `para` renders as the bare clause**, and that shape is load-bearing
rather than cosmetic: inch 2 was written with the ARM text absent from this
machine (`docs/backlog/ada.md` §2026-08-24-ada-2), so its citations can name
the clause the census verifies and must NOT invent a paragraph number the
lane cannot check. A citation that could not be checked to the paragraph
**says so by its shape** instead of guessing. -/
def ArmRef.toString (r : ArmRef) : String :=
  if r.para.isEmpty then r.clause else s!"{r.clause}({r.para})"

instance : ToString ArmRef := ⟨ArmRef.toString⟩

/-! ## The refusal classes — `Core.RefusalCause`, instantiated at `ArmRef`

The four §5.2 classes are family law and Core owns them; the payload is the
tier's. Inch 1's by-shape copy is deleted, and with it its one spelling
divergence: this tier's `unsupportedConstruct` is the family's **`unsupported`**.

**ADA DOES NOT NARROW THE CAUSE TYPE, and the contrast with Go is the reason
to say so.** The Go tier refuses only through a narrower `GoRefusal` that has
no `undefined` constructor, so its empty class is unreachable *by
construction* — the right gate for a language whose specification never says
"undefined". **Ada's `undefined` bucket is expected NON-empty**: ARM 1.1.5
defines erroneous execution as the class with no language-specified bound on
the possible effect, measured at 23 paragraphs in clauses 1-13 and
concentrated in ARM 11.5 (*Suppressing Checks*) and ARM 13.9.1 (*Data
Validity*). A narrowing type here would delete this tier's product. So Ada
refuses through Core's `refuse` directly, all four classes reachable, and its
expected-empty class is a different one — gated by predicate below. -/

/-- Ada's cause type: the family's four classes, carrying ARM paragraphs. -/
abbrev Cause := RefusalCause ArmRef

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

**The predicate is Core's** (`RefusalCause.isOrderDependence`), which Core
lifted so that the test is written once per family rather than once per tier;
what stays local is the tier's CLAIM about its own bucket, which is the part
that is Ada's.
-/
def orderDependenceGate (cs : List Cause) : Bool :=
  cs.all fun c => !c.isOrderDependence

/-- The erroneous-execution citation, so `undefined` always carries the
clause that defines it rather than an ad-hoc string. -/
def erroneousExecution : ArmRef := { clause := "1.1.5", para := "9" }

/-! ## The base outcome — `Core.HaltWith`, at THIS tier's payload

**`AdaHalt`, not `Halt`.** `Core.Halt` is `HaltWith Unit Unit`, the
payload-free instantiation a tier with no structured cause writes — and
adopting it here would typecheck, compile, and silently throw every ARM
reference away. Naming the instantiation is what makes the payload visible at
the use site; a local `abbrev Halt` would have shadowed Core's inside this
namespace and made the wrong one the one a reader sees.

The three by-shape definitions this replaces are gone: `Loud` (a bespoke
inductive with a hand-written `Monad` instance), `Halt`, and `SemM`. -/

/-- A run either produces a value or halts loudly, carrying the ARM paragraph
it halted on. `σ = Unit`, so `Loud`'s diagnostic snapshot is always `none`. -/
abbrev AdaHalt := HaltWith ArmRef Unit

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

/-- A scalar value.

**`univInt` is ARM 3.5.4's `universal_integer`, and it is the ARM's own
concept rather than a modelling convenience.** An integer literal is of type
*universal_integer* and is implicitly converted at its point of use; a tier
that gave `5` a subtype at the literal would have decided the conversion
before the semantics could see it, which is exactly the reason this file
keeps a literal's SOURCE SPELLING one layer down. Inch 2 needs it because
`X := 5` cannot be written without saying what `5` is, and ARM 5.2's answer
is *whatever the target's subtype makes it* — see `Stmt.lean`. -/
inductive Val where
  | int (sub : IntSubtype) (v : Int)
  | enum (sub : EnumSubtype) (pos : Nat)
  /-- ARM 3.5.4 — `universal_integer`: exact, unbounded, and converted at
  its point of use. -/
  | univInt (v : Int)
  /-- ARM 3.6.3, *String Types* — **a FRAGMENT of Ada's `String`, and the gap
  is named rather than blurred.** Ada's `String` is
  `array (Positive range <>) of Character`, so a faithful value carries
  BOUNDS; this one does not. What it supports is what inch 5a needs to run
  `Report`: literals (ARM 2.6) and catenation (ARM 4.5.3). **Indexing,
  slicing, `'Length`, `'First` and any constrained-subtype length check are
  therefore NOT modelled and must refuse** — a value that cannot say its
  bounds cannot answer them, and answering anyway would be the wrong kind of
  cheap. Bounds arrive with the array rung. -/
  | str (s : String)
  /-- **ARM 3.3.1 — DECLARED BUT NOT YET ASSIGNED**, carrying the subtype
  name it was declared with. Measured: **12 of 29 `ObjectDecl`s in the
  fixtures have no initialiser**, so this is the common case and not a corner.

  It exists so the model can tell *"never declared"* from *"declared, unset"*
  — two different faults with two different citations, which a store that
  simply omitted the object could not distinguish. **Reading one REFUSES**
  (ARM 13.9.1, *Data Validity*): Ada makes reading an uninitialised scalar a
  BOUNDED ERROR with a bounded set of outcomes, and this tier cannot yet
  enumerate that set — the ARM text is off this machine. So the refusal is a
  pending measurement, and the site becomes a `BoundedSite` with a real
  permitted set when the re-acquire rung lands. Assigning INTO one is
  ordinary and defined. -/
  | uninit (typeName : String)
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


/-- **The tier's monad**, and it is Core's `SemMWith` at Ada's four
parameters: the world is the caller's, `ρ = Abrupt`, `π = ArmRef`,
`σ = Unit`. `ExceptT` sits OUTSIDE `StateT` so the world survives a raise —
Core's layer order, decided there by `rfl` rather than by taste. Fuel is an
INDEX on the step function, never in state.

The Go tier's `GoM = SemMWith GoWorld Panic SpecRef Unit` is the same shape at
the same position, arrived at independently: **two tiers whose refusal payload
is a citation into their own standard.** -/
abbrev AdaM (W : Type) := SemMWith W Abrupt ArmRef Unit

/-- **CHECKED, not assumed** — the ticket's second check, made structural.
The tier's monad is built on the payload-CARRYING halt. Writing
`SemM W Abrupt` instead would elaborate, compile, and pin `π = Unit`, and
every ARM reference a refusal cites would be dropped at the type level with
nothing to notice it. -/
example (W : Type) : AdaM W = ExceptT Abrupt (StateT W AdaHalt) := rfl

/-! ## Refusing and raising — Core's named primitives, unaliased

`refuse` (out of tier, state-discarding), `refuseWith` (the same plus a
snapshot — unused here, `σ = Unit`), `exhausted` (fuel), `raiseIn` (the
language's own raise, state-retaining) are Core's and are used as Core spells
them. **No tier alias is defined**, because Ada would have nothing to add:
the Go tier's `refuseGo` earns its existence by NARROWING the cause type, and
Ada deliberately does not narrow. A pass-through wrapper would be surface
with no decision in it.

The inch-1 placeholder that rendered the cause into the message string
(`refuse (c : Cause)` prefixing `[unsupportedConstruct@3.5.4(10)]`) is
**deleted**: the class is a constructor and the clause is its payload, so
`Loud.observable` and `RefusalCause.className` bucket a refusal without any
consumer parsing prose. That was the whole reason the placeholder was named a
placeholder. -/



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
inherit it without asking. This needs only `BEq Val`, which is derived.

**RE-CHECKED AT ADOPTION, and it survives.** Core ships
`instance [BEq π] : BEq (Loud π σ)` — on `Loud`, which is the model's
give-up type, and NOT on `Except`. `constrain` returns `Except Abrupt Val`,
so the synthesis failure this helper exists for is untouched by the import,
and its three sites still need it. Checked by compiling rather than by
reading, because reading Core's instance list suggests the opposite answer:
a `BEq` does arrive with the adoption, on the type this helper is not
about. -/
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

-- A citation whose paragraph could not be checked cites the CLAUSE, and the
-- rendering says which kind it is. Inch 1 had the ARM text and cites to the
-- paragraph; inch 2 does not and cites to the clause.
#guard ({ clause := "5.2", para := "" } : ArmRef).toString == "5.2"

-- The refusal classes: all four PRESENT, per the ruling. `undefined` carries
-- the clause that defines erroneous execution rather than a loose string.
#guard erroneousExecution.toString == "1.1.5(9)"
#guard (RefusalCause.undefined erroneousExecution : Cause) matches .undefined _

-- The class name is the FAMILY's, emitted by Core, and a scoreboard buckets
-- on it. The by-shape spelling `unsupportedConstruct` is gone with the copy.
#guard (RefusalCause.undefined erroneousExecution : Cause).className == "undefined"
#guard (RefusalCause.unsupported erroneousExecution : Cause).className == "unsupported"

/-! ### THE TWO CHANNELS, MEASURED

The adoption is only correct if Ada's outcomes land on the right side of
Core's line, so the mapping is run rather than described. These three guards
are the ones that would have caught a wrong adoption, and each fails for a
different reason if the mapping slips. -/

/-- ARM 9.1, *Task Units* — tasking is outside the modelled tier, so it is
the honest example of something Ada refuses rather than raises. -/
private def tasking : ArmRef := { clause := "9.1", para := "1" }

/-- Did the run raise `name`, and what world came back? The world is the
point: a `ρ` channel that discarded state could not answer the second half. -/
private def raisedWith (name : String) (w' : Nat) (x : AdaM Nat Val) (w : Nat) : Bool :=
  match x w with
  | .ok (.error (.raised n _), wOut) => n == name && wOut == w'
  | _ => false

/-- The refusal's §5.2 class and its ARM paragraph, read as DATA — never
parsed back out of prose, which is exactly what the pre-adoption placeholder
forced a consumer to do. -/
private def refusedAt (cls : String) (r : ArmRef) (x : AdaM Nat Val) (w : Nat) : Bool :=
  match x w with
  | .error (.unsupported c _ _) => c.className == cls && c.detail == r
  | _ => false

/-- A world EFFECT and then a raise. The effect is what makes the retention
claim non-trivial: an initial world merely passing through would prove far
less than a WRITE performed before the raise still being visible after it. -/
private def effectThenRaise : AdaM Nat Val := do
  set (42 : Nat)
  raiseIn (.raised constraintError "value outside Int8 range")

/-- The same exception with no effect before it. -/
private def raiseAlone : AdaM Nat Val :=
  raiseIn (.raised constraintError "value outside Int8 range")

/-- Tasking: out of the modelled tier, so this one refuses. -/
private def refuseTasking : AdaM Nat Val :=
  refuse (.unsupported tasking) "task rendezvous is not modelled"

-- ρ IS STATE-RETAINING. The world goes in as 7, is written to 42, and comes
-- back 42 THROUGH the raise. ARM 11.4 -- an exception propagates and a
-- handler observes the state it was raised in.
#guard raisedWith constraintError 42 effectThenRaise 7
#guard raisedWith constraintError 7 raiseAlone 7

-- π IS STATE-DISCARDING, and structurally so: the `.error` arm has nowhere
-- to put a world. What it does carry is the class and the paragraph.
#guard refusedAt "unsupported" tasking refuseTasking 7

-- AND THE TWO ARE NOT INTERCHANGEABLE: a raise is not a refusal. This is the
-- inch-1 decision restated at the substrate, and it is the guard that fails
-- if `Constraint_Error` is ever wired onto the give-up channel.
#guard !refusedAt "unsupported" tasking raiseAlone 7
#guard !raisedWith constraintError 7 refuseTasking 7

-- THE GATE: `order-dependence` is present and expected empty. The predicate
-- is what inch 6 checks; it holds vacuously on an empty list, and FAILS the
-- moment a site emits one -- which is the point of gating rather than
-- omitting the constructor.
#guard orderDependenceGate []
#guard orderDependenceGate [.undefined erroneousExecution, .environment erroneousExecution]
#guard !orderDependenceGate [.orderDependence { clause := "1.1.4", para := "1" }]

end LeanModels.Ada.Ada2012
