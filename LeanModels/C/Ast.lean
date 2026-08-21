import LeanModels.Core.Basic

/-!
# The C tier's deep-embedded AST (`LeanModels.C`)

The Lean image of the `c-0.1` envelope (`docs/c-envelope-schema.md`). One
constructor per node kind in the pinned vocabulary, plus an `unsupported`
leaf for everything outside it.

**This file is a TYPE, not a semantics.** Nothing here evaluates
anything; the interpreter, the memory model and the UB refusals are
milestone M2 and later (`docs/c-tier-charter.md` §3). A term of type
`TranslationUnit` is what `load_c_program` produces at elaboration time,
and what the `#guard`s of `Examples/c/sunfish/` are stated about.

Three shapes are worth reading before the constructors, because each is a
decision the census or the schema forced rather than a convenience:

* **`CType` is a `String`.** clang's `-ast-dump=json` gives `qualType`
  strings, not a type tree, and the 7 structured type kinds appear only
  under the corpus's 7 `TypedefDecl`s (measured: 22 nodes, all there).
  Parsing the string into a tree would be writing the C type parser the
  frontend decision exists to avoid, so the tier carries the frontend's
  own spelling and keeps the structured form where clang volunteers it
  (`TypeNode`, used by `Decl.typedef`).
* **`Span.macro` is an `Option`.** Six function-like macros produce
  corpus constructs, and a refusal that cannot name the macro is one a
  human cannot act on. It is `none` for source written directly, so
  macro-free files carry no extra weight.
* **Every literal keeps its SOURCE SPELLING as a `String`.** An
  `IntegerLiteral`'s value is `"2147483648"`, not a `Nat` — because the
  tier's whole product is refusing what C leaves undefined, and a
  literal that overflowed its type during ingestion would have been
  silently decided before the semantics ever saw it.
-/

namespace LeanModels.C

open LeanModels (Span)

/-- A type, as clang spells it (`"int"`, `"const char[121]"`,
`"int (*)(Move, void *)"`). See the module docstring: this is the
frontend's string, deliberately unparsed. -/
abbrev CType := String

/-- A source span, with the macro that produced the construct when one did.
`line`/`col` are the EXPANSION location — where a reader sees it. -/
structure CSpan where
  line : Nat
  col : Nat
  endLine : Nat
  endCol : Nat
  /-- The SPELLING location, present only when it differs from the
  expansion location — i.e. the node came out of a macro body. -/
  macroLine : Option Nat := none
  macroCol : Option Nat := none
deriving Repr, Inhabited, BEq, DecidableEq

/-- The structured type tree, emitted only under a `TypedefDecl`. -/
inductive TypeNode where
  | builtin (name : CType)
  | pointer (inner : TypeNode)
  | paren (inner : TypeNode)
  | elaborated (inner : TypeNode)
  | record (ty : CType)
  | typedefRef (ty : CType)
  | funcProto (ret : TypeNode) (params : List TypeNode)
  | unsupported (cKind : String) (text : String)
deriving Repr, Inhabited, BEq

/-! ## The three layers

C's grammar makes the layering, not us: a function DEFINITION is the only
declaration that contains statements, and C has no nested functions — so
`Expr`, `Decl` and `Stmt` form no cycle, and `FunctionDefn` sits on top as
a structure. That is the same shape the Python lane's `FunctionDefn` has,
arrived at from the language rather than borrowed. -/

/-- C expressions — the 19 expression kinds of the pinned vocabulary. -/
inductive Expr where
  /-- Literals keep their SOURCE SPELLING; see the module docstring. -/
  | intLit (value : String) (ty : CType) (span : CSpan)
  | charLit (value : String) (ty : CType) (span : CSpan)
  | strLit (value : String) (ty : CType) (span : CSpan)
  | floatLit (value : String) (ty : CType) (span : CSpan)
  /-- A name, with the kind of declaration it resolved to. -/
  | declRef (name : String) (declKind : String) (ty : CType) (span : CSpan)
  | member (base : Expr) (field : String) (arrow : Bool) (ty : CType) (span : CSpan)
  | index (base : Expr) (idx : Expr) (ty : CType) (span : CSpan)
  /-- A call. An INDIRECT call is one whose callee is not a `declRef` to a
  function — all 19 in the corpus go through the `movecb` parameter. -/
  | call (callee : Expr) (args : List Expr) (ty : CType) (span : CSpan)
  | binop (op : String) (lhs rhs : Expr) (ty : CType) (span : CSpan)
  | compoundAssign (op : String) (lhs rhs : Expr) (ty : CType) (span : CSpan)
  | unop (op : String) (sub : Expr) (isPostfix : Bool) (ty : CType) (span : CSpan)
  | cond (c t e : Expr) (ty : CType) (span : CSpan)
  | paren (sub : Expr) (ty : CType) (span : CSpan)
  /-- An implicit conversion, carrying clang's `castKind`. The 8 kinds are
  the whole conversion lattice and they arrive PRE-SOLVED — the tier never
  re-derives a promotion, it reads one off. -/
  | implicitCast (cast : String) (sub : Expr) (ty : CType) (span : CSpan)
  | cast (cast : String) (sub : Expr) (ty : CType) (span : CSpan)
  | initList (inits : List Expr) (ty : CType) (span : CSpan)
  | compoundLit (init : Expr) (ty : CType) (span : CSpan)
  /-- `sizeof`/`alignof`, over a type or over an expression. -/
  | typeTrait (trait : String) (argType : Option CType) (sub : Option Expr)
      (ty : CType) (span : CSpan)
  | constExpr (value : String) (sub : Option Expr) (ty : CType) (span : CSpan)
  /-- Outside the pinned vocabulary: clang's own class name and ≤200 chars
  of source. Never silently dropped, never guessed at. -/
  | unsupported (cKind : String) (text : String) (span : CSpan)
deriving Repr, Inhabited

/-- C declarations that can appear at BLOCK scope as well as file scope —
everything but a function definition. -/
inductive Decl where
  | var (name : String) (ty : CType) (storage : Option String)
      (init : Option Expr) (span : CSpan)
  | param (name : String) (ty : CType) (span : CSpan)
  | field (name : String) (ty : CType) (span : CSpan)
  | record (name : Option String) (fields : List Decl) (span : CSpan)
  | typedef (name : String) (ty : CType) (underlying : Option TypeNode) (span : CSpan)
  | enum (name : Option String) (constants : List Decl) (span : CSpan)
  /-- The value is the FOLDED integer as a decimal string; clang's
  `ConstantExpr` wrapper is flattened here (schema §3.1). -/
  | enumConst (name : String) (value : String) (span : CSpan)
  | unsupported (cKind : String) (text : String) (span : CSpan)
deriving Repr, Inhabited


/-- C statements — the 11 statement kinds. `SwitchStmt` is deliberately
absent (measured 0 in the corpus); it arrives with rung R1 and until then
ingests as `unsupported`, which is what makes R1 a rung and not a hole. -/
inductive Stmt where
  | compound (body : List Stmt) (span : CSpan)
  | decl (decls : List Decl) (span : CSpan)
  | ifS (cond : Expr) (thenS : Stmt) (elseS : Option Stmt) (span : CSpan)
  | forS (init : Option Stmt) (cond : Option Expr) (inc : Option Expr)
      (body : Stmt) (span : CSpan)
  | whileS (cond : Expr) (body : Stmt) (span : CSpan)
  | doS (body : Stmt) (cond : Expr) (span : CSpan)
  | ret (value : Option Expr) (span : CSpan)
  | breakS (span : CSpan)
  | continueS (span : CSpan)
  | goto (label : String) (span : CSpan)
  | label (name : String) (body : Stmt) (span : CSpan)
  /-- An expression in statement position. -/
  | expr (e : Expr) (span : CSpan)
  | unsupported (cKind : String) (text : String) (span : CSpan)
deriving Repr, Inhabited

/-- A function DEFINITION (or prototype, when `body = none`). `storage` is
clang's `storageClass` — `"static"`, or `none` for external linkage. -/
structure FunctionDefn where
  name : String
  ty : CType
  storage : Option String
  params : List Decl
  body : Option Stmt
  span : CSpan
deriving Repr, Inhabited

/-- A file-scope item. -/
inductive TopLevel where
  | fn (f : FunctionDefn)
  | decl (d : Decl)
deriving Repr, Inhabited

/-- One translation unit: the top-level items attributed to the censused
source, in document order. -/
structure TranslationUnit where
  items : List TopLevel
deriving Repr, Inhabited

/-- A declared-but-not-defined name the unit references, with its
prototype. The corpus has exactly 27 (the libc slice). -/
structure External where
  name : String
  ty : Option CType
deriving Repr, Inhabited, BEq

/-- The `c-0.1` envelope. `frontend` is accepted and NOT retained, exactly
as the Python lane does; `profileId` IS retained, because unlike a
frontend stamp the profile is an input to the AST and a mismatch has to be
refusable. -/
structure Envelope where
  schemaVersion : String
  language : String
  profileId : String
  profileFlags : List String
  sourceFile : String
  sourceSha256 : String
  unit : TranslationUnit
  externals : List External
deriving Repr, Inhabited

/-! ## Structural queries

These exist so the ingester can be checked against
`harness/c_construct_census.py` — two instruments, two paths, one answer.
They are counts over the TERM, not claims about C. -/

/-- Sub-expressions, including the expression itself. -/
def Expr.subexprs : Expr → List Expr
  | e@(.member b _ _ _ _) => e :: b.subexprs
  | e@(.index b i _ _) => e :: (b.subexprs ++ i.subexprs)
  | e@(.call c args _ _) => e :: (c.subexprs ++ args.flatMap Expr.subexprs)
  | e@(.binop _ l r _ _) => e :: (l.subexprs ++ r.subexprs)
  | e@(.compoundAssign _ l r _ _) => e :: (l.subexprs ++ r.subexprs)
  | e@(.unop _ s _ _ _) => e :: s.subexprs
  | e@(.cond c t f _ _) => e :: (c.subexprs ++ t.subexprs ++ f.subexprs)
  | e@(.paren s _ _) => e :: s.subexprs
  | e@(.implicitCast _ s _ _) => e :: s.subexprs
  | e@(.cast _ s _ _) => e :: s.subexprs
  | e@(.initList xs _ _) => e :: xs.flatMap Expr.subexprs
  | e@(.compoundLit i _ _) => e :: i.subexprs
  | e@(.typeTrait _ _ (some s) _ _) => e :: s.subexprs
  | e@(.constExpr _ (some s) _ _) => e :: s.subexprs
  | e => [e]

/-- The expressions a block-scope declaration contains. -/
def Decl.exprs : Decl → List Expr
  | .var _ _ _ (some i) _ => i.subexprs
  | _ => []

/-- Statements nested inside a statement, including itself. -/
def Stmt.substmts : Stmt → List Stmt
  | s@(.compound body _) => s :: body.flatMap Stmt.substmts
  | s@(.ifS _ t none _) => s :: t.substmts
  | s@(.ifS _ t (some e) _) => s :: (t.substmts ++ e.substmts)
  | s@(.forS (some i) _ _ b _) => s :: (i.substmts ++ b.substmts)
  | s@(.forS none _ _ b _) => s :: b.substmts
  | s@(.whileS _ b _) => s :: b.substmts
  | s@(.doS b _ _) => s :: b.substmts
  | s@(.label _ b _) => s :: b.substmts
  | s => [s]

/-- The expressions a statement holds DIRECTLY (its own operands), not
those of its nested statements — `substmts` already reaches those. -/
def Stmt.ownExprs : Stmt → List Expr
  | .decl ds _ => ds.flatMap Decl.exprs
  | .ifS c _ _ _ => c.subexprs
  | .forS _ c inc _ _ =>
      (c.map Expr.subexprs).getD [] ++ (inc.map Expr.subexprs).getD []
  | .whileS c _ _ => c.subexprs
  | .doS _ c _ => c.subexprs
  | .ret (some v) _ => v.subexprs
  | .expr e _ => e.subexprs
  | _ => []

namespace TranslationUnit

/-- Functions WITH a body — definitions, not prototypes. -/
def functionDefns (u : TranslationUnit) : List FunctionDefn :=
  u.items.filterMap fun i => match i with
    | .fn f => if f.body.isSome then some f else none
    | .decl _ => none

/-- File-scope objects: the top-level `var` declarations. -/
def fileScopeObjects (u : TranslationUnit) : List Decl :=
  u.items.filterMap fun i => match i with
    | .decl d@(.var ..) => some d
    | _ => none

/-- Every statement in the unit (function bodies only — C has no
statements outside one). -/
def stmts (u : TranslationUnit) : List Stmt :=
  u.functionDefns.flatMap fun f => (f.body.map Stmt.substmts).getD []

/-- Every expression in the unit: file-scope initializers, plus every
statement's own operands. -/
def exprs (u : TranslationUnit) : List Expr :=
  (u.items.flatMap fun i => match i with
      | .decl d => d.exprs
      | .fn _ => []) ++ u.stmts.flatMap Stmt.ownExprs

/-- Peel the conversions clang wraps a callee in. -/
def calleeHead : Expr → Expr
  | .implicitCast _ s _ _ => calleeHead s
  | .paren s _ _ => calleeHead s
  | e => e

/-- Call sites whose callee is NOT a direct function reference — the
callback protocol. All 19 in the corpus go through `movecb`. -/
def indirectCalls (u : TranslationUnit) : List Expr :=
  u.exprs.filter fun e => match e with
    | .call callee _ _ _ =>
        match calleeHead callee with
        | .declRef _ "FunctionDecl" _ _ => false
        | _ => true
    | _ => false

/-- Statements the tier does not model — `switch` today, and nothing else. -/
def unsupportedStmts (u : TranslationUnit) : List Stmt :=
  u.stmts.filter fun s => match s with
    | .unsupported .. => true
    | _ => false

end TranslationUnit

end LeanModels.C
