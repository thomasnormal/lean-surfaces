import LeanModels.Python.Surface

/-!
# Delaborators for the spec surface (`LeanModels.Python`)

For an AI prover the goal state IS the interface: a judgment that *elaborates*
from `add(a, b) ==> a + b` but *displays* as
`CallsTo add "add" #[ToVal.toVal a, ToVal.toVal b] (ToVal.toVal (a + b))`
leaks the entire deep embedding right back into every proof. This file closes
the loop with `app_unexpander`s, so goals and `#check` output print in the
same surface notation the theorems are written in (docs/spec-surface.md).

What unexpands (registered on the judgment heads, display-only):

* `CallsTo m "f" #[…] v`  → `f(…) ==> v`
* `Raises m "f" #[…] e`   → `f(…) ==>! e`
* `PartialTo m "f" #[…] v` → `f(…) ~~> v`

Callee reconstruction inverts `splitCallee` (Surface.lean): when the module
ident is exactly the single-component name of the function string (the
`load_program add` / `"add"` convention) it prints bare — `add(a, b)`;
otherwise it prints dotted — `m.f(a)`, `arith.floordiv(a, b)` — which
`splitCallee` splits back to the same (module, function) pair, so every
rendering re-elaborates to the proposition it displays. If the module is not
an ident, the function name is not a string literal, or the argument array is
not an `#[…]` literal, the unexpander bails and the raw judgment shows.

`ToVal.toVal x` is stripped to `x` **only inside these judgment positions**
(arguments and result slot). There is deliberately no global `toVal`
unexpander: outside the arrows, marshalling stays visible.

What still leaks (by design or by Lean's rules — documented, not hidden):

* Below the judgment boundary nothing is sugared: after `unfold CallsTo`,
  `refine ⟨32, ?_⟩`, or `obtain ⟨fuel, hf⟩ := h`, goals show the raw
  `∃ fuel, callFunction … = Res.ok (ToVal.toVal …)` — fuel and interpreter
  are *supposed* to be visible once you step below the surface.
* `f(a) ⇓ r` prints as `f(a) ==> r`: both arrows target `CallsTo`, and the
  unexpander cannot know which was written. (`⇓` is hypothesis-position
  sugar; the meaning is identical.)
* Raw `Val` arguments print as themselves inside the parens —
  `m.f(Val.int 1) ==> Val.int 1` — still arrow-shaped, and re-elaborates via
  the `ToVal Val = id` instance.
* `set_option pp.explicit true` bypasses all app unexpanders (standard Lean
  behaviour) and shows the fully explicit term.
* The `Obs` spine (`Obs m f args (.returns v)` etc.) is not sugared: it is
  proof machinery, not the theorem surface.

Pinned renderings: the regression tests at the bottom of this file (bound-
variable modules, self-contained) and `#guard_msgs`-checked `#check
add_total` / `#check add_partial` in `Examples/python/add/add.py`'s lean block.
-/

namespace LeanModels.Python

open Lean PrettyPrinter

/-- Strip a delaborated `ToVal.toVal x` application down to `x`. Matches any
ident whose last component is `toVal` (covers `ToVal.toVal`,
`LeanModels.Python.ToVal.toVal`, and bare `toVal` under `open`), applied to
exactly one explicit argument. Anything else is returned unchanged — used
only inside the judgment positions below, never registered globally. -/
private def stripToVal (stx : Term) : Term :=
  match stx with
  | `($f:ident $x:term) =>
    match f.getId.eraseMacroScopes with
    | .str _ "toVal" => x
    | _ => stx
  | _ => stx

/-- Invert `splitCallee` (Surface.lean): rebuild the surface callee ident
from the delaborated module term and function-name string literal. A module
ident that *is* the function name (single component) prints bare (`add`);
any other ident prints dotted (`m.f`, `arith.floordiv`), which `splitCallee`
splits back to the same pair. Non-ident module terms yield `none` (caller
falls back to the raw judgment). -/
private def calleeIdent? (m : Term) (s : StrLit) : Option Ident :=
  match m with
  | `($mid:ident) =>
    let mn := mid.getId.eraseMacroScopes
    let fn := s.getString
    if mn == Name.mkSimple fn then some mid
    else if mn.isAnonymous then none
    else some (mkIdentFrom mid (Name.mkStr mn fn))
  | _ => none

/-- Display `CallsTo m "f" #[…] v` as `f(…) ==> v` (dotted `m.f(…)` when the
module ident does not match the function string). `ToVal.toVal` is stripped
in the argument and result slots. -/
@[app_unexpander LeanModels.Python.CallsTo]
def unexpandCallsTo : Unexpander
  | `($_ $m $s:str #[$args,*] $v) => do
    let some f := calleeIdent? m s | throw ()
    let args : Array Term := args.getElems.map stripToVal
    let v := stripToVal v
    `($f:ident($args,*) ==> $v)
  | _ => throw ()

/-- Display `Raises m "f" #[…] e` as `f(…) ==>! e`. -/
@[app_unexpander LeanModels.Python.Raises]
def unexpandRaises : Unexpander
  | `($_ $m $s:str #[$args,*] $e) => do
    let some f := calleeIdent? m s | throw ()
    let args : Array Term := args.getElems.map stripToVal
    `($f:ident($args,*) ==>! $e)
  | _ => throw ()

/-- Display `PartialTo m "f" #[…] v` as `f(…) ~~> v`. -/
@[app_unexpander LeanModels.Python.PartialTo]
def unexpandPartialTo : Unexpander
  | `($_ $m $s:str #[$args,*] $v) => do
    let some f := calleeIdent? m s | throw ()
    let args : Array Term := args.getElems.map stripToVal
    let v := stripToVal v
    `($f:ident($args,*) ~~> $v)
  | _ => throw ()

/-! ## Pinned renderings (regression tests)

Bound-variable modules keep these self-contained; the loaded-program
renderings (`add_total`, `add_partial`) are pinned in
`Examples/python/add/add.py`'s lean block. Each rendering also re-elaborates to
the proposition it displays — the `rfl` roundtrips at the end. -/

section DelabTests

/-- info: ∀ (prog : Module) (a : PyInt), prog(a) ==> a : Prop -/
#guard_msgs in
#check ∀ (prog : Module) (a : PyInt), CallsTo prog "prog" #[ToVal.toVal a] (ToVal.toVal a)

/-- info: ∀ (m : Module) (a b : PyInt), m.f(a, b) ==> a + b : Prop -/
#guard_msgs in
#check ∀ (m : Module) (a b : PyInt),
  CallsTo m "f" #[ToVal.toVal a, ToVal.toVal b] (ToVal.toVal (a + b))

/-- info: ∀ (m : Module) (a : PyInt), m.f(a) ==>! PyErr.zeroDivisionError : Prop -/
#guard_msgs in
#check ∀ (m : Module) (a : PyInt), Raises m "f" #[ToVal.toVal a] .zeroDivisionError

/-- info: ∀ (m : Module) (a : PyInt), m.f(a) ~~> a : Prop -/
#guard_msgs in
#check ∀ (m : Module) (a : PyInt), PartialTo m "f" #[ToVal.toVal a] (ToVal.toVal a)

/-- info: ∀ (m : Module), m.f() ==> 3 : Prop -/
#guard_msgs in
#check ∀ (m : Module), CallsTo m "f" #[] (ToVal.toVal (3 : PyInt))

/-- info: ∀ (m : Module), m.f(Val.int 1) ==> Val.int 1 : Prop -/
#guard_msgs in
#check ∀ (m : Module), CallsTo m "f" #[Val.int 1] (Val.int 1)

/-- info: ∀ (m : Module) (args : Array Val), CallsTo m "f" args (Val.int 1) : Prop -/
#guard_msgs in
#check ∀ (m : Module) (args : Array Val), CallsTo m "f" args (Val.int 1)

/-- info: fun n => ToVal.toVal n : PyInt → Val -/
#guard_msgs in
#check fun (n : PyInt) => ToVal.toVal n

-- Roundtrip: every rendering above re-elaborates to the judgment it displays.
example (m : Module) (a : PyInt) :
    (m.f(a) ==> a) = CallsTo m "f" #[ToVal.toVal a] (ToVal.toVal a) := rfl
example (prog : Module) (a : PyInt) :
    (prog(a) ==> a) = CallsTo prog "prog" #[ToVal.toVal a] (ToVal.toVal a) := rfl
example (m : Module) (a : PyInt) :
    (m.f(a) ~~> a) = PartialTo m "f" #[ToVal.toVal a] (ToVal.toVal a) := rfl
example (m : Module) (a : PyInt) :
    (m.f(a) ==>! .zeroDivisionError)
      = Raises m "f" #[ToVal.toVal a] .zeroDivisionError := rfl

end DelabTests

end LeanModels.Python
