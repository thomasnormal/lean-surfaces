import LeanModels.Go.Value
import LeanModels.Core.Outcome

/-!
# The Go tier's substrate, its refusals, and panic as ρ

M1 inch 1, second half. `docs/go-charter.md` §6 is the design; this is it
in Lean, with no evaluator attached beyond the first statement walker.

## The substrate, adopted BY SHAPE

`docs/family-architecture.md` §3.4 fixes the family's substrate as
`ExceptT ρ (StateT W Halt)`, in that order — `StateT` outside `ExceptT`
discards the state on a raise, and the tier's own error postcondition then
cannot be stated.

**ADOPTED, not defined.** This file first carried the shape locally with
an adoption note, per the ES lane's precedent. `LeanModels/Core/Outcome.lean`
landed at `376735e`, so the local copy was **REPLACED by the import** —
replaced, not wrapped. `SemM`, `Halt`, `Loud`, `refuse` and `exhausted`
all come from Core and this tier defines none of them.

Core's stack is `ExceptT ρ (StateT W (Except Loud))`, which is the same
layer order the local copy had and for the same stated reason: `StateT`
outside `ExceptT` discards the state on a raise.

## Why ρ is a PANIC, and why a panic has an identity

`docs/go-charter.md` §6.1 fixes ρ = panic. The Go specification, "Handling
panics", verbatim:

> While executing a function `F`, an explicit call to `panic` or a
> run-time panic terminates the execution of `F`. Any functions deferred
> by `F` are then executed as usual. Next, any deferred functions run by
> `F`'s caller are run, and so on up to any deferred by the top-level
> function in the executing goroutine. At that point, the program is
> terminated and the error condition is reported, including the value of
> the argument to `panic`.

That is `ExceptT`'s propagation exactly — unwinding that runs deferred
work at each frame and carries a value out — so `panic` in ρ makes the
correspondence mechanical rather than encoded.

**The identity is not decoration.** The spec's `recover` rule turns on
*which* panic is being recovered: a deferred function that itself panics
replaces the panic in flight, and `recover` stops the panicking sequence
only when called directly by a function deferred by the panicking frame.
A ρ carrying only a value cannot tell a re-panic from the panic it
replaced, and every later rule about `recover` would have to reconstruct
that distinction from context. So a `Panic` is `(id, value)`, and the
identity is minted at the point the panic starts.

Note that Go's zero-UB posture reaches even here: "Integer overflow" says
**"Overflow does not cause a run-time panic"**, so arithmetic never
produces one of these. `Spec.lean` gates that.
-/

namespace LeanModels.Go

/-- A pointer into the specification — the π every refusal carries.

A refusal that cannot name the clause it is refusing under is one a human
cannot act on, and one a scoreboard cannot bucket without parsing prose.
`doc` distinguishes the tier's TWO co-equal documents
(`docs/go-charter.md` §1): the language specification and the memory
model. -/
structure SpecRef where
  /-- `"spec"` for the Go Programming Language Specification, `"mem"` for
  the Go Memory Model. -/
  doc : String
  /-- The section's anchor, e.g. `"Integer_overflow"`. -/
  section_ : String
  deriving Repr, DecidableEq, Inhabited

namespace SpecRef
def spec (s : String) : SpecRef := ⟨"spec", s⟩
def mem (s : String) : SpecRef := ⟨"mem", s⟩
end SpecRef

/-! ## Refusal causes — CORE'S, and the local enum is RETIRED

This tier briefly carried its own four-class `RefusalCause` plus a
`renderRefusal` that wrote the class into Core's message as a `[tag|…]`
prefix, because Core's `Loud` then held only a `String`. Core's payload
landing (`f714f76`) records Go as the **third tier** to re-derive that
same taxonomy, and Core now holds it: `RefusalCause π` with the same four
classes, and `className` returning byte-identical strings to the ones this
tier had chosen.

**So the local enum is retired and the prefix with it.** Keeping either
would leave the class making a round trip through a string that exists
only because the typed field once did not — and Core's own rule is now
explicit that a scoreboard *"buckets on THIS, never by parsing the
payload's prose"*. The message is again just prose, and the class is read
as data.

What does NOT move is the gate below. `undefined` is PRESENT in Core's
type and expected to stay EMPTY here, which is the point:
`docs/go-charter.md`'s zero-UB finding is a claim about a document, and a
type without the constructor would make the emptiness unfalsifiable —
Core's own header says the same, that omitting it *"makes the emptiness a
fact about the TYPE, invisible to the scoreboard."* `GoRefusal` is still
this tier's own type, and it is still the reason cause 2 is unreachable
here. **A Go tier that ever emits `undefined` has a bug**, and
`Spec.lean` says so in a form that fails.
-/

/-- A panic in flight — ρ. See the header for why it carries an identity
as well as a value. -/
structure Panic where
  /-- Minted when the panicking sequence starts, so a re-panic raised by a
  deferred function is a DIFFERENT panic from the one it replaced. -/
  id : Nat
  /-- The argument to `panic`, reported when the program terminates. -/
  value : GoVal
  deriving Repr, Inhabited

/-- The language version in force for a file.

`docs/go-charter.md` §3 measured that this is not a label: Go 1.21 and Go
1.22 give the same `for` statement different variable scoping, and §3.2's
run showed ONE compiler invocation applying BOTH semantics to
byte-identical loop bodies in one package. So the version is carried
**per file**, which is the one place the Go envelope must differ
structurally from C's `profile_id`. -/
structure LangVersion where
  major : Nat
  minor : Nat
  deriving Repr, DecidableEq, Inhabited

namespace LangVersion
def go121 : LangVersion := ⟨1, 21⟩
def go122 : LangVersion := ⟨1, 22⟩
/-- The predicate the loop rule branches on: per-iteration scoping is
Go 1.22 and later. -/
def perIterationLoopVars (v : LangVersion) : Bool :=
  v.major > 1 || (v.major = 1 && v.minor ≥ 22)
end LangVersion

/-- The world — W. The envelope's store shape, plus the two things every
rule needs to read and nothing else yet.

`sched` is carried from the FIRST COMMIT even though `Schedule` is a
one-element type and no rule reads it. `docs/go-charter.md` §6.2 makes
this the tier's one non-negotiable structural commitment, on measured
grounds: `docs/c-tier-charter.md` §3.3 records that C's concurrency rung
"is the one rung that is not a widening — it replaces a state function
with a memory-ORDER relation, which would change the interpreter's TYPE".
Carrying the field means the type never changes; only the inhabitants of
`Schedule` grow. -/
structure Schedule where
  /-- A one-element type today. The choice oracle of §6.2 — goroutine
  interleaving, `select`'s uniform choice, and map iteration order all
  resolve here, because all three are choices made outside the program
  text and the model should have exactly one place for them. -/
  unit : Unit := ()
  deriving Repr, Inhabited

structure GoWorld where
  /-- The store: addresses to values. Go locals are addressable, so a
  binding is not enough (`docs/go-charter.md` §6.1). -/
  store : List (Addr × GoVal) := []
  /-- Next free address, so allocation is deterministic and the ledger is
  statable. -/
  nextAddr : Addr := 0
  /-- Locals: name to ADDRESS, not name to value. Go locals are
  addressable — `&x` on a local is legal and rung 1's fixture takes the
  address of one — so a binding that held a value directly could not
  model `&x` at all. This is the same reason `docs/go-charter.md` §6.1
  gives for not reusing the Python tier's `REnv`. -/
  locals : List (String × Addr) := []
  /-- Emitted bytes. Output is world data, per the family's
  effects-as-world-data treatment. -/
  stdout : List String := []
  /-- The language version of the file being executed. Per FILE, not per
  program — see `LangVersion`. -/
  lang : LangVersion := LangVersion.go122
  /-- The choice oracle. Unread at inch 1, by design. -/
  sched : Schedule := {}
  deriving Repr, Inhabited

/-- The Go tier's instantiation of the FAMILY monad: the world is
`GoWorld`, ρ is a panic, and **the refusal payload π is a `SpecRef`** — the
clause the refusal cites, carried as DATA. `SemMWith` is Core's.

**Why π is no longer `Unit`.** This tier adopted Core when `Loud.unsupported`
carried a bare `String`, so it encoded its cause and its clause into a PREFIX
(`renderRefusal`) and told a scoreboard to parse it. Core's `RefusalCause π`
landing removes the reason for that: the cause is a constructor and the clause
is its payload, so `Loud.observable` buckets without reading prose.

The payload landing kept the prefix in the message byte-for-byte so that
nothing downstream of the text moved — the conservative choice, and the right
one at that moment. **This lane has since removed it.** Keeping it would have
left the class making a round trip through a string that exists only because
the typed field once did not, and the only consumer of the text was this
tier's own guards, which now read the class and the clause as data. The
message is prose again. -/
abbrev GoM := SemMWith GoWorld Panic SpecRef Unit

/-- **The zero-UB gate, as a TYPE rather than a convention.**

`docs/go-charter.md` measured that "undefined" appears zero times in the
Go specification. `RefusalCause` nonetheless CARRIES `undefined`, because
the family taxonomy is one taxonomy and a lane that deleted the
constructor could not state that its bucket is empty.

The gate is this narrower type. Every refusal the Go tier emits goes
through `SemM.refuseGo`, whose cause argument is a `GoRefusal` — and
`GoRefusal` has no `undefined`. So the emptiness of cause 2 is not a
promise a reviewer checks by reading, nor a grep that a new call site can
slip past: **it is unreachable by construction, and `Spec.lean` proves the
image excludes it.** A future rung that genuinely found undefined
behaviour in Go would have to widen this type on purpose, which is
exactly the deliberate act it should be. -/
inductive GoRefusal where
  | unsupportedConstruct
  | environment
  | orderDependence
  deriving Repr, DecidableEq, Inhabited

/-- **The image of `GoRefusal` in the FAMILY's cause type**, carrying the
cited clause as the payload. `undefined` is not in the image, and that is
the theorem `Spec.lean` records — now stated against Core's
`RefusalCause.isUndefined`, which Core lifted from the ES lane precisely
so the gate is written once per family rather than once per tier. -/
def GoRefusal.toCore (r : GoRefusal) (π : SpecRef) : RefusalCause SpecRef :=
  match r with
  | .unsupportedConstruct => .unsupported π
  | .environment          => .environment π
  | .orderDependence      => .orderDependence π

/-- The Go tier's refusal, and the ONLY way this tier refuses. Narrower
than Core's `refuse` on purpose — see `GoRefusal`. The message is prose
only: the class travels as a typed field, not as a prefix. -/
def refuseGo {W ρ α : Type} (r : GoRefusal) (π : SpecRef) (msg : String) :
    SemMWith W ρ SpecRef Unit α :=
  LeanModels.refuse (r.toCore π) msg

/-- Start a panicking sequence with a fresh identity. State-RETAINING, per
Core's ρ channel. -/
def panicWith (id : Nat) (v : GoVal) : GoM α := LeanModels.raiseIn ⟨id, v⟩

end LeanModels.Go
