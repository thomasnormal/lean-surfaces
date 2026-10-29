import LeanModels.Sv.Param2

/-!
# Module hierarchy in the semantic tier (`PDesign.instantiateH`, F3)

An sv-0.2 envelope of a hierarchical design carries the top module and,
after it, the DEFINITIONS of every module it instantiates (transitively),
each elaborated alone at its own defaults by the extractor
(`docs/sv-envelope-schema.md`, "Module instances"). A module instance is a
`GenItem.inst` — at module level or inside a generate body — naming its
definition, its parameter overrides (symbolic constant expressions of the
instantiating scope), its port connections and its lexical generate path.

`PDesign.instantiateH d lib args` FLATTENS at instantiation time: it is
`instantiate2` (`Param2.lean`) with the generate walk extended by one case.
At each instance, at the CURRENT parameter and genvar values:

1. the overrides are evaluated in the instantiating scope and the child
   definition is brought to that parameter point (`PDesign.atPoint` — the
   not-overridden parameters keep their defaults, exactly as the
   differential runner treats a top-level point);
2. the child is instantiated RECURSIVELY (its own instances flattened), to
   a `Design2` over its own names;
3. every child declaration is hoisted into the parent under the
   hierarchical name `<path>.<inst>.<signal>` — the generate blocks the
   instance sits in, with their indices (`g_bit[3].fa.s`, IEEE 1800-2023
   §23.6/§27.6) — its port flags cleared, and every child process is
   renamed the same way (`Process2.rename`);
4. each port connection becomes a continuous assignment (IEEE 1800-2023
   §23.3.3: a port connection is a continuous assignment from source to
   sink): an input `<pfx>port = actual` with the actual instantiated in the
   parent at the port's width (`fitExpr2`), an output `target = <pfx>port`
   resized to the target's width; an unconnected input NET reads z
   (`net`), an unconnected input variable keeps its initial x.

## Port-width coercion (the measured rule)

A port connection is a continuous assignment, so the LRM evaluates an
input actual at the wider of the port and the actual — slang binds it that
way and Verilator 5.042 agrees (`p + q` of two 2-bit operands into a 4-bit
port: `0101` at `p = 2, q = 3`). Icarus 12.0 and Yosys 0.53 instead
evaluate the actual SELF-determined and zero-pad (`0001`; `~p` pads zeros
where the context reading inverts them). The two readings agree whenever
the actual is at least as wide as the port (truncation commutes with the
operators) and whenever widening cannot change a bit (`PExpr.portSafe`:
rigid operands, `& | ^` and `?:` over them, comparisons, unsigned implicit
conversions). Every other input actual narrower than its port is LOUD
(`PortConn:context-width`) — never one reading silently chosen
(`docs/sv-oracle-disagreements.md`, "Port connection width context").

NET TO NET (round 6, H1, 2026-10-29). The rule above reads a port connection
as the continuous assignment of IEEE 1800-2023 §23.3.3 and zero-extends a
narrower actual (§10.7): Icarus 12.0, Verilator 5.042, Yosys 0.53 and slang
agree. Xcelium 24.03-s004 does NOT, in exactly one shape: a NET formal (an
`input logic [W-1:0] i` without `var` is a net, §23.2.2.3) bound to a bare
reference to a NET actual (a `wire`, or an input port of the instantiating
module, which is a net too) is connected bit for bit, and the formal's high
bits stay undriven — z (warning `CUVMPW`; §23.3.3.7 permits collapsing the
two nets). The extractor marks that shape on the connection (`PConn.input
… net := true`, `_sym_net_bound_actual`: net formal, bare whole-net actual,
widths not provably fixed-and-not-narrower), and when the actual is
narrower than the port at the instance's own point `connProcs` is loud
(`PortConn:net-width`). Unchanged, because every tool agrees (Xcelium
included): variable actuals, proper part-selects, constants and expressions,
variable (`var`) and 2-state formals, equal or wider actuals. Not covered,
listed as gaps: a full-range part-select or a constant bit-select of a net
actual (Xcelium z-fills those too), and the output direction (a narrower
output formal into a wider whole NET target leaves z in Xcelium).

Integer actuals (`.i(5)`, `.i(-1)`, `.i(g)`, `.i(N*3-1)`) arrive as their
UNCONVERTED INT-class tree (the extractor peels slang's conversion to the
port type of the instance it bound, which had folded the constant at that
one width): at a port of at most 32 bits it is at least as wide as the port
and `fitExpr2` materializes it there exactly (`.int` is `LVec.ofInt` at the
context width); at a wider port it is loud (`PortConn:context-width` here,
`PortConnection:int-width` from the extractor when the bound port was
already wider).

Unbased-unsized fills (`'0 '1 'x 'z`) are admitted anywhere in such an
actual and take the LRM reading — a fill is as wide as its context
(§5.7.1), so `a ^ '1` into a 4-bit port is `{2'b11, ~a}` — which is also
Verilator 5.042's and Yosys 0.53's. Icarus 12.0 alone sizes a fill NESTED
under an operator self-determined and zero-pads (`{2'b00, ~a}`): a
declared Icarus disagreement (row `hier_fill_ctx`). A bare fill, and fills
whose widened bits are masked (`a & '1`, `s ? '0 : a`), agree in every
tool (row `hier_fill`).

## Clocks

`Sem2`'s edge phase runs every posedge process once per cycle whatever its
clock name: the cycle semantics has ONE clock. (A top-level `always_ff
@(posedge g)` on a derived `g` is admitted and runs on that clock — the
inherited single-clock gap of the flat tier, recorded in
`docs/sv-charter.md`; flattening does not widen it.) A flattened child flop
must therefore be clocked by what is, through bare connections, an input
port of the TOP module: a child edge process is admitted only when its
clock is one of the child's INPUT ports (`clockGuardProc`) connected to a
bare signal of the same width (`instBodyProc`) that is itself an INPUT port
of the instantiating module (`clockGuardProc`). The clock (and
asynchronous reset) name is then substituted by that signal — the
flattened process is literally a process of the instantiating module, and
the same rule applies to it one level up. Any other clock — a child-internal
signal, an expression, a derived or gated parent signal (`assign gclk = clk
& en`) — is loud (`Instance:clock`).

## Drivers

Flattening ADDS continuous assignments (the port connections) after the
extractor's overlapping-driver guard has run on each module alone, and
`Sem2` gives several writers of one bit process order (last write wins) —
never IEEE net resolution (§28.12) nor the multiple-driver error of a
variable (§10.3.2). So at every level of the hierarchy, at the instance's
own parameter point, a module's OWN signals have one driver per bit
(`driversOk`), checked at WINDOW granularity — a constant select drives its
own bits, a whole-signal target or a run-time index the whole signal
(exactly the longest static prefix, §11.5.3):
* the windows its continuous assignments drive — its own `assign`s and the
  output-port connections of its instances alike — are pairwise disjoint;
* none of them is one of its INPUT ports, or shares a bit with a window a
  procedural process of the module writes (the continuous/procedural
  mixture IEEE 1800-2023 §6.5 forbids on one longest static prefix:
  `always_comb y[0] = a; assign y[1] = b;` is legal and admitted,
  `assign y[0] = b;` instead is refused);
* no procedural process writes an input port (§23.3.3.2: an input port's
  one driver is its connection, or the testbench at the top);
* no window an `always_comb` or `always_ff` process writes shares a bit
  with a window ANY other process writes (§9.2.2.2/§9.2.2.4, applied per
  longest static prefix as slang's `-Wmultiple-always-assigns` does,
  `procExclusiveOk`) — so two `always_comb` blocks writing `y[0]` are
  refused (Icarus 12.0 gives the bit the FIRST block's value, `Sem2`'s
  process order the second's; row `drv_pw_lit`), while the
  generate-indexed `always_ff` writers of distinct constant elements of
  `cv32e40p_register_file_ff`'s `mem` stay admitted. `alwaysFFR` counts as
  exclusive although it does not record whether it came from `always_ff`
  or from a plain `always @(posedge clk or negedge rn)` — a conservative,
  LOUD over-refusal of the plain form. Two plain `always @(posedge clk)`
  writers of one bit (`alwaysPlain`) are legal and stay admitted.
A violation appends a loud `PortConn:driver` process
(`Design2.driverGuard`) whose message names the signal and the clause, so
`run2`, the differential runner and `load_design_sv2` refuse. Every CHILD
is checked (`childInstOf`, instance-free children included), and so is
EVERY TOP, at every parameter point: a top holding an instance by
`PDesign.topGuard` inside `instantiateH`, an instance-free (flat) top by
`PDesign.instantiateG2` / `PDesign.instantiateGD2` — `instantiate2` under
the same `PDesign.driverGuard`, the family `name.sem` of a flat envelope,
the differential runner and `load_design_sv2`'s defaults gate use
(2026-10-28, WP2). `instantiateH` itself stays the flat tier's on an
instance-free design (`PDesign.instantiateH_flat`): the guard is applied
once, by the caller that knows the top is flat. Before WP2 a flat top was
not checked at all, and the extractor's overlap guard
(`_symbolic_target_windows`) sees literal-index windows only, so
`for (genvar i = 0; i < 4; i++) assign y[i/2] = a[i];` loaded and resolved
the two drivers of each bit by issue order (`y = xx00` at `a = 0101`, where
Icarus and Yosys report multiple drivers); procedural writers were not
checked at all, so `always_comb y[0] = a[0]; always_comb y[0] = a[1];`
loaded and ran with the second block's value (2026-10-28, WP2 repair).
Hoisted signals (`<prefix><name>`) are each driven by their own module's
processes, checked one level down, and by their input connection, which
the child-level input rule protects. Instance outputs on DISJOINT bits of
one signal are admitted (the verifier's `pair` shape).

## Out of scope (loud)

`inout`/`ref` ports, interface ports and instances, instance arrays,
`defparam`, `bind`, port default values, type-parameter overrides, an
untyped child parameter overridden by a non-integer expression, a TYPED
child parameter overridden by a parameter expression that needs a
narrowing conversion (`.P(LP)` with `int LP` into `parameter logic [3:0] P`
is `ConversionExpression:width`; a literal override such as `.P(3)` is
admitted), a child definition with a parameter that has no default (slang
cannot elaborate it alone: `ModuleDefinition:elaboration`; its definition is
absent from the library and the instance is loud), an instance inside a
generate branch not taken at the DEFAULT parameters (slang does not bind
it: `UninstantiatedDefSymbol`) — and since the extractor binds each
generate-for body from its FIRST iteration, an instance in a branch inside a
generate-for that the first iteration does not take, even where later
iterations take it — recursive instantiation (the hierarchy depth is
bounded by the size of the module library), an integer constant actual into
a port wider than 32 bits (above), signed and 2-state ports
(`PortSymbol:signed`/`:2state`; integer-typed variables are themselves out
of the tier, so no integer-typed SIGNAL is an actual), several drivers of
one bit ("Drivers"), and — a flat-tier gap — a child declaring a `wire [..]`
net or non-ANSI ports (`input [3:0] a;`), whose declarations the load gate
refuses as "unrecoverable packed dimensions".

## Names

Hierarchical names contain `.`/`[`/`]`, which no simple identifier does,
and the extractor refuses escaped identifiers containing them on a path;
block names are slang's (`genblk<n>` for unnamed blocks, unique per scope),
instance names are unique per scope — so hoisted names never collide
(`Design2.namesNodup` re-checks it at the load gate and the differential
runner).

Instance-free designs: `PDesign.instantiateRec` agrees with
`instantiate2From` (`Hier2Gen.lean`, `PDesign.instantiateH_flat`) — the
walk takes the flat expansion verbatim on every instance-free item list.
-/

namespace LeanModels.Sv

/-! ## Renaming (the flattening substitution) -/

mutual
/-- Rename every signal an expression reads. -/
def Expr2.rename (f : String → String) : Expr2 → Expr2
  | .resizeSigned w a => .resizeSigned w (a.rename f)
  | .squash2 a => .squash2 (a.rename f)
  | .lit v => .lit v
  | .ident n => .ident (f n)
  | .unary op a => .unary op (a.rename f)
  | .binary op l r => .binary op (l.rename f) (r.rename f)
  | .scmp op l r => .scmp op (l.rename f) (r.rename f)
  | .logical b l r => .logical b (l.rename f) (r.rename f)
  | .ternary c t e => .ternary (c.rename f) (t.rename f) (e.rename f)
  | .concat ps => .concat (Expr2.renameList f ps.toList).toArray
  | .slice b lo w => .slice (b.rename f) lo w
  | .index b i ew => .index (b.rename f) (i.rename f) ew
  | .repl n a => .repl n (a.rename f)
  | .reduce op a => .reduce op (a.rename f)
  | .resize w a => .resize w (a.rename f)
  | .unsupported k t => .unsupported k t
termination_by structural e => e

/-- `Expr2.rename`, elementwise. -/
def Expr2.renameList (f : String → String) : List Expr2 → List Expr2
  | [] => []
  | e :: es => e.rename f :: Expr2.renameList f es
termination_by structural es => es
end

mutual
/-- Rename every signal an assignment target writes (and its index reads). -/
def Lhs2.rename (f : String → String) : Lhs2 → Lhs2
  | .ident n => .ident (f n)
  | .slice n lo w => .slice (f n) lo w
  | .index n i ew => .index (f n) (i.rename f) ew
  | .concat ps => .concat (Lhs2.renameList f ps)
termination_by structural t => t

/-- `Lhs2.rename`, elementwise. -/
def Lhs2.renameList (f : String → String) : List Lhs2 → List Lhs2
  | [] => []
  | t :: ts => t.rename f :: Lhs2.renameList f ts
termination_by structural ts => ts
end

mutual
/-- Rename every signal a statement reads or writes. -/
def Stmt2.rename (f : String → String) : Stmt2 → Stmt2
  | .blockingAssign t e => .blockingAssign (t.rename f) (e.rename f)
  | .nbaAssign t e => .nbaAssign (t.rename f) (e.rename f)
  | .ifStmt c t e => .ifStmt (c.rename f) (t.rename f) (Stmt2.renameOpt f e)
  | .block body => .block (Stmt2.renameList f body.toList).toArray
  | .caseStmt subj items dflt inside check =>
      .caseStmt (subj.rename f) (CaseItem2.renameList f items.toList).toArray
        (Stmt2.renameOpt f dflt) inside check
  | .unsupported k t => .unsupported k t
termination_by structural s => s

/-- `Stmt2.rename` of an optional statement. -/
def Stmt2.renameOpt (f : String → String) : Option Stmt2 → Option Stmt2
  | none => none
  | some s => some (s.rename f)
termination_by structural o => o

/-- `Stmt2.rename`, elementwise. -/
def Stmt2.renameList (f : String → String) : List Stmt2 → List Stmt2
  | [] => []
  | s :: ss => s.rename f :: Stmt2.renameList f ss
termination_by structural ss => ss

/-- `Stmt2.rename` of a case arm (patterns and body). -/
def CaseItem2.rename (f : String → String) : CaseItem2 → CaseItem2
  | .mk pats body => .mk (Expr2.renameList f pats.toList).toArray (body.rename f)
termination_by structural it => it

/-- `CaseItem2.rename`, elementwise. -/
def CaseItem2.renameList (f : String → String) : List CaseItem2 → List CaseItem2
  | [] => []
  | it :: rest => it.rename f :: CaseItem2.renameList f rest
termination_by structural its => its
end

/-- Rename a process: every signal through `f`; the clock and reset NAMES of
an edge-phase process through `g` (the clock-identity substitution of a
flattened instance — see the module docstring). -/
def Process2.rename (f g : String → String) : Process2 → Process2
  | .alwaysFF c b => .alwaysFF (g c) (b.rename f)
  | .alwaysPlain c b => .alwaysPlain (g c) (b.rename f)
  | .alwaysComb b => .alwaysComb (b.rename f)
  | .assign t e => .assign (t.rename f) (e.rename f)
  | .alwaysFFR c rn b => .alwaysFFR (g c) (g rn) (b.rename f)
  | .unsupported k t => .unsupported k t

/-- The clock name of an edge-phase process. -/
def Process2.clock? : Process2 → Option String
  | .alwaysFF c _ | .alwaysPlain c _ | .alwaysFFR c _ _ => some c
  | _ => none

/-- A child declaration hoisted into the instantiating module: prefixed name,
port flags cleared (a child port is an internal signal of the parent). -/
def Decl.hoist (pfx : String) (dc : Decl) : Decl :=
  { dc with name := pfx ++ dc.name, isInput := false, isOutput := false }

/-! ## Instances: path, overrides, port connections -/

/-- The generate-block part of a hierarchical prefix: `label.` per if-block,
`label[v].` per loop block with its genvar's CURRENT value. -/
def PInst.pathPrefix (env : IEnv) : List PPathSeg → Except String String
  | [] => .ok ""
  | s :: rest => do
      let here ← match s.genvar with
        | none => pure (s.label ++ ".")
        | some g =>
            match env.vals.lookup g with
            | some v => pure (s.label ++ "[" ++ toString v ++ "].")
            | none => throw s!"genvar '{g}' of generate block '{s.label}' is unbound"
      let tl ← PInst.pathPrefix env rest
      pure (here ++ tl)

/-- The hierarchical prefix of an instance's signals: `<path><inst>.`
(`g_bit[3].fa.`). -/
def PInst.prefix (env : IEnv) (i : PInst) : Except String String := do
  let p ← PInst.pathPrefix env i.path
  pure (p ++ i.name ++ ".")

/-- An expression whose constant type is `int` (32-bit signed): the INT
class (`PExpr.isInt`), or — under `IEnv.int32`, where INT parameters are
bound in `nvals` at `(32, signed)` — an expression `ctype` types so. -/
def PExpr.intTyped (env : IEnv) (e : PExpr) : Bool :=
  e.isInt env ||
    match ctype env e with
    | .ok (w, s) => w == 32 && s
    | .error _ => false

/-- The parameter point of a child instance (`PDesign.atPoint`'s `given`):
per child parameter, declaration order, the override's value evaluated in
the instantiating scope `env`, or `none` (its default). An override naming
no parameter of the child, or overriding an UNTYPED parameter with an
expression outside the INT class (whose type would become the
override's, §6.20.2), is refused. -/
def PInst.given (env : IEnv) (c : PDesign) (i : PInst) :
    Except String (List (Option Int)) := do
  match i.params.find? (fun (n, _) => !c.params.any (·.name == n)) with
  | some (n, _) => throw s!"'{n}' is not a parameter of module '{c.name}'"
  | none => pure ()
  c.params.mapM fun p =>
    match i.params.lookup p.name with
    | none => pure none
    | some e =>
        if p.type?.isNone && !e.intTyped env then
          throw s!"parameter '{p.name}' has no declared type and its override is not an integer expression (it would take the override's type, IEEE 1800-2023 §6.20.2)"
        else
          match evalInt env e with
          | .ok v => pure (some v)
          | .error m => throw s!"parameter '{p.name}' override: {m}"

/-- Operators whose 1-bit result is self-determined in every context
(comparisons, logical connectives): widening never changes a bit. -/
def SymBinOp.bitResult : SymBinOp → Bool
  | .m0 .eq | .m0 .ne | .m0 .caseEq | .m0 .caseNe | .m0 .wildEq | .m0 .wildNe
  | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge
  | .m0 .land | .m0 .lor
  | .slt | .sle | .sgt | .sge | .ceq | .cne | .land | .lor => true
  | _ => false

/-- An input actual admitted NARROWER than its port (module docstring,
"Port-width coercion"). Rigid operands, `& | ^` and `?:` over such operands,
comparison results, and unsigned implicit conversions of these: the
context-determined value at the wider port equals the self-determined value
zero-extended, so the LRM reading and the Icarus/Yosys reading agree.
Unbased-unsized fills among them take the LRM (port-width) reading, which
Verilator 5.042 and Yosys 0.53 share; Icarus 12.0 alone pads a fill NESTED
under an operator with zeros (`a ^ '1`: `{2'b00, ~a}` against the LRM's
`{2'b11, ~a}`) — a declared Icarus disagreement, row `hier_fill_ctx`.
Signed casts are not admitted. -/
def PExpr.portSafe : PExpr → Bool
  | .resize _ a => a.portSafe
  | .binary (.m0 .and) l r | .binary (.m0 .or) l r | .binary (.m0 .xor) l r =>
      l.portSafe && r.portSafe
  | .binary op _ _ => op.bitResult
  | .unary (.m0 .lnot) _ => true
  | .ternary _ t e => t.portSafe && e.portSafe
  | .fill _ => true
  | .cast _ _ => false
  | e => rigidExpr e

/-- An input actual admitted at a port of width `wp` (at THESE parameters):
port-safe, or at least as wide as the port. -/
def portInOk (env : IEnv) (elems : List (String × Nat)) (wp : Nat) (e : PExpr) : Bool :=
  e.portSafe ||
    match selfWidth2 env elems e with
    | some w => decide (wp ≤ w)
    | none => false

/-- An output port's value brought to its target's width: a child port is an
unsigned declared signal, so the LRM's assignment rule is zero-extension or
truncation (§11.8.2 / §23.3.3). -/
def portOut (n : String) (wp wt : Nat) : Expr2 :=
  if wp == wt then .ident n else .resize wt (.ident n)

/-- Whether an input actual of self-determined width `w` (when known) is
strictly NARROWER than the port it feeds (`wp` bits). -/
def netNarrower (w : Option Nat) (wp : Nat) : Bool :=
  match w with
  | some w => decide (w < wp)
  | none => false

/-- The refusal text of `PortConn:net-width` (round 6, H1, 2026-10-29): a
bare NET actual narrower than the NET input formal it feeds. IEEE 1800-2023
§23.3.3/§23.3.3.8/§10.7 read the connection as a continuous assignment that
zero-extends the source — what the model computed until then and what Icarus
12.0, Verilator 5.042, Yosys 0.53 and slang do — but Xcelium 24.03-s004 binds
the two nets bit for bit and leaves the formal's high bits undriven (z,
warning CUVMPW; §23.3.3.7 permits collapsing). Variable actuals, proper
part-selects, constants and expressions (Xcelium zero-extends those too),
variable and 2-state formals, and equal or wider actuals are unchanged. -/
def netWidthMsg (port : String) (wp : Nat) : String :=
  s!"input port '{port}' ({wp} bits) is a net bound to a bare, narrower net actual: IEEE 1800-2023 §23.3.3/§10.7 zero-extend it (Icarus, Verilator, Yosys and slang agree), Xcelium 24.03 leaves the formal's high bits undriven (z, CUVMPW); refused rather than one reading chosen"

/-- The continuous assignments realizing one child port `dc`'s connection
(`[]` for an unconnected output or variable input). -/
def connProcs (env : IEnv) (elems : List (String × Nat)) (pfx : String)
    (conns : List PConn) (dc : Decl) : List Process2 :=
  let n := pfx ++ dc.name
  match conns.find? (·.port == dc.name) with
  | none => [.unsupported "PortConn:missing" s!"port '{dc.name}' has no connection"]
  | some (.unsupported _ k t) => [.unsupported k t]
  | some (.input _ actual net) =>
      if !dc.isInput then
        [.unsupported "PortConn:direction" s!"port '{dc.name}' is not an input"]
      else
        match actual with
        | some e =>
            -- Round 6 (H1, 2026-10-29): a CONNECTED input with `net` set is a
            -- net formal bound to a bare reference to a NET (the extractor's
            -- `_sym_net_bound_actual`); when that actual is narrower than the
            -- port here, the tools split (`netWidthMsg`).
            match net with
            | true =>
                if netNarrower (selfWidth2 env elems e) dc.width then
                  [.unsupported "PortConn:net-width" (netWidthMsg dc.name dc.width)]
                else if portInOk env elems dc.width e then
                  [.assign (.ident n) (fitExpr2 env elems (some dc.width) e)]
                else
                  [.unsupported "PortConn:context-width"
                    s!"input port '{dc.name}' ({dc.width} bits) connected to a narrower context-sensitive expression: Icarus/Yosys zero-pad its self-determined value, the LRM evaluates it at the port width"]
            | false =>
                if portInOk env elems dc.width e then
                  [.assign (.ident n) (fitExpr2 env elems (some dc.width) e)]
                else
                  [.unsupported "PortConn:context-width"
                    s!"input port '{dc.name}' ({dc.width} bits) connected to a narrower context-sensitive expression: Icarus/Yosys zero-pad its self-determined value, the LRM evaluates it at the port width"]
        | none =>
            if net then [.assign (.ident n) (.lit (LVec.replicate dc.width .lz))] else []
  | some (.output _ target) =>
      if !dc.isOutput then
        [.unsupported "PortConn:direction" s!"port '{dc.name}' is not an output"]
      else
        match target with
        | none => []
        | some t =>
            match instLhs2 env elems t with
            | .ok (l2, wt) => [.assign l2 (portOut n dc.width wt)]
            | .error e => [.unsupported "PortConn:target" e]

/-- The bare-signal connections of a child's input ports: `(port, parent
signal)` when the actual is a parent identifier of the port's width (the
clock-identity substitution). -/
def bareInputs (env : IEnv) (ports : List Decl) (conns : List PConn) :
    List (String × String) :=
  ports.filterMap fun dc =>
    if !dc.isInput then none
    else
      match conns.find? (·.port == dc.name) with
      | some (.input _ (some (.ident m)) _) =>
          if env.widths.lookup m == some dc.width then some (dc.name, m) else none
      | _ => none

/-- A connection naming no port of the child (`none` when it names one): a
loud connection keeps its own kind; any other is `PortConn:port`. -/
def strayConn (c : Design2) (ports : List Decl) (cn : PConn) : Option Process2 :=
  if ports.any (·.name == cn.port) then none
  else
    match cn with
    | .unsupported _ k t => some (.unsupported k t)
    | _ => some (.unsupported "PortConn:port"
        s!"connection '{cn.port}' names no port of module '{c.name}'")

/-- A child's `always_comb` self-read refusal (`AlwaysComb:self-read`,
`CombGuard2.lean`) names the instance it was flattened from (WP4 round 3,
2026-10-28): the guard runs on the child's own instantiation, where the
instance, the child module and the flattened signal names are not known,
so its message names the child-local signal. Every other process, and
every other refusal, is unchanged. Nested instances prepend their own
clause, so the message reads outermost instance first. Each clause's
prefix is RELATIVE to the module that instantiates that instance (round 4
Lane A, 2026-10-28: the round-3 wording read as if a nested instance's
level-local prefix were its flattened one — for `top → m → l` the leaf's
signals are under `m.l.`, the clauses' prefixes concatenated outermost
first, not under `l.`). -/
@[simp] def Process2.inInstance (pfx : String) (i : PInst) : Process2 → Process2
  | .alwaysFF c b => .alwaysFF c b
  | .alwaysPlain c b => .alwaysPlain c b
  | .alwaysComb b => .alwaysComb b
  | .assign t e => .assign t e
  | .alwaysFFR c rn b => .alwaysFFR c rn b
  | .unsupported k t =>
      .unsupported k (if k = "AlwaysComb:self-read" then
        s!"in instance '{i.name}' of module '{i.module}' (its signals flatten under the prefix '{pfx}' inside the module that instantiates it): {t}"
      else t)

/-- One child process inside the instantiating module: renamed under the
prefix, its clock/reset names through the bare-signal substitution — and
loud when its clock is a child input port without a bare connection (module
docstring, "Clocks"). A child's self-read refusal names the instance
(`Process2.inInstance`). -/
def instBodyProc (pfx : String) (i : PInst) (ports : List Decl)
    (bare : List (String × String)) (p : Process2) : Process2 :=
  let f : String → String := (pfx ++ ·)
  let g : String → String := fun x => (bare.lookup x).getD (pfx ++ x)
  match p.clock? with
  | some clk =>
      if ports.any (fun dc => dc.isInput && dc.name == clk) && (bare.lookup clk).isNone then
        .unsupported "Instance:clock"
          s!"instance '{i.name}': clock port '{clk}' is not connected to a bare signal of the instantiating module"
      else p.rename f g
  | none => (p.rename f g).inInstance pfx i

/-- The input-port names of a declaration list: the admissible clock
sources of a child flop instantiated in that module (module docstring,
"Clocks"). -/
def Decl.inputNames (ds : List Decl) : List String :=
  (ds.filter (·.isInput)).map (·.name)

/-- One process of a child design `c` under the clock-source rule (module
docstring, "Clocks"), given `clocks`, the input ports of the instantiating
module: an edge process must be clocked by one of `c`'s INPUT ports, and
when that port is connected to a bare signal of the instantiating module,
the signal must be one of `clocks`; otherwise the process is loud
(`Instance:clock`). A non-bare clock connection passes here and is refused
by `instBodyProc`. -/
def clockGuardProc (clocks : List String) (i : PInst) (c : Design2) (p : Process2) :
    Process2 :=
  match p.clock? with
  | none => p
  | some k =>
      if !c.decls.toList.any (fun dc => dc.isInput && dc.name == k) then
        .unsupported "Instance:clock"
          s!"instance '{i.name}' of '{c.name}': a flop is clocked by '{k}', which is not an input port of '{c.name}' (a flattened flop must be clocked, through bare input-port connections, by an input port of the top module)"
      else
        match i.conns.find? (·.port == k) with
        | some (.input _ (some (.ident m)) _) =>
            if clocks.contains m then p
            else .unsupported "Instance:clock"
              s!"instance '{i.name}': clock port '{k}' is connected to '{m}', which is not an input port of the instantiating module (a derived or gated clock is outside the single-clock cycle semantics)"
        | _ => p

/-- A child's flattened design under the clock-source rule
(`clockGuardProc`, every process). -/
def Design2.clockGuard (clocks : List String) (i : PInst) (c : Design2) : Design2 :=
  { c with processes := c.processes.map (clockGuardProc clocks i c) }

/-- **One instance, flattened** (given the child's own flattened design
`c`): the child's declarations hoisted under the instance prefix, then the
port-connection assignments (child port order) followed by the child's
processes, renamed. A connection naming no port of the child is loud. -/
def flattenInst (env : IEnv) (elems : List (String × Nat)) (pfx : String) (i : PInst)
    (c : Design2) : List Decl × List Process2 :=
  let ports := c.decls.toList.filter fun dc => dc.isInput || dc.isOutput
  let bare := bareInputs env ports i.conns
  (c.decls.toList.map (Decl.hoist pfx),
    i.conns.filterMap (strayConn c ports)
      ++ ports.flatMap (connProcs env elems pfx i.conns)
      ++ c.processes.toList.map (instBodyProc pfx i ports bare))

/-- A child instantiator: the instantiating scope's environment and the
instance ↦ the child's flattened design over its own names. -/
abbrev ChildInst := IEnv → PInst → Res Design2

/-- `flattenInst` at the instance's current prefix, with the child from the
instantiator. -/
def instExpandH (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (i : PInst) :
    Res (List Decl × List Process2) :=
  match i.prefix env with
  | .error e => .unsupported s!"instance '{i.name}': {e}"
  | .ok pfx => do
      let c ← cb env i
      .ok (flattenInst env elems pfx i c)

/-! ## The generate walk with instances -/

mutual
/-- Generate items without a module instance anywhere. -/
def GenItem.instFree : GenItem → Bool
  | .inst _ => false
  | .genIf _ t e => GenItem.listInstFree t && GenItem.listInstFree e
  | .genFor _ _ _ _ _ _ body => GenItem.listInstFree body
  | .process _ | .unsupported .. => true
termination_by structural it => it

/-- `GenItem.instFree`, for every item of a list. -/
def GenItem.listInstFree : List GenItem → Bool
  | [] => true
  | it :: rest => it.instFree && GenItem.listInstFree rest
termination_by structural l => l
end

mutual
/-- `GenItem.expand2` extended by the instance case: expansion yields the
hoisted declarations alongside the processes. -/
def GenItem.expandH (cb : ChildInst) (env : IEnv) (elems : List (String × Nat))
    (F : Nat) : GenItem → Res (List Decl × List Process2)
  | .process p => .ok ([], [instProcess2 env elems p])
  | .unsupported k t => .ok ([], [.unsupported k t])
  | .inst i => instExpandH cb env elems i
  | .genIf cond thenB elseB =>
      match evalInt env cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v =>
          if v != 0 then expandListH cb env elems F thenB
          else expandListH cb env elems F elseB
  | .genFor _label g initE bound step _rc body =>
      match evalInt env initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env g bound δ F i0
          expandItersH cb env elems F g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- An item list: the flat `expandList2` verbatim when no item holds an
instance, else item by item (concatenation, source order). -/
def expandListH (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat) :
    List GenItem → Res (List Decl × List Process2)
  | [] => .ok ([], [])
  | it :: rest =>
      if GenItem.listInstFree (it :: rest) then do
        let ps ← expandList2 env elems F (it :: rest)
        .ok ([], ps)
      else do
        let (ds, ps) ← it.expandH cb env elems F
        let (ds', qs) ← expandListH cb env elems F rest
        .ok (ds ++ ds', ps ++ qs)
  termination_by l => (sizeOf l, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- A generate-for body at each genvar value. -/
def expandItersH (cb : ChildInst) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (g : String) : List Int → List GenItem → Res (List Decl × List Process2)
  | [], _ => .ok ([], [])
  | v :: vs, body => do
      let (ds, ps) ← expandListH cb (env.bindVal g v) elems F body
      let (ds', qs) ← expandItersH cb env elems F g vs body
      .ok (ds ++ ds', ps ++ qs)
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

/-! ## One driver per bit after flattening (`PortConn:driver`) -/

/-- A continuous-driver window on a signal: `(base, some (lo, w))` drives
bits `[lo, lo + w)`, `(base, none)` the whole signal (a whole-signal target,
or a run-time index — conservatively everything it may reach). -/
abbrev DrvWin := String × Option (Nat × Nat)

/-- The bits an element select `n[idx]` of element width `ew` drives: a
LITERAL index `k` (no x/z bit) is element `k`'s window `[k·ew, k·ew + ew)`
(the window `resolveLhs2` writes and `Comb2Base`'s `Lhs2.window?` names);
any other index — a run-time one — may reach every element (`none`). -/
def Lhs2.indexWin? : Expr2 → Nat → Option (Nat × Nat)
  | .lit c, ew => c.toNat?.map fun k => (k * ew, ew)
  | _, _ => none

mutual
/-- The windows an assignment target drives. -/
def Lhs2.drvWins : Lhs2 → List DrvWin
  | .ident n => [(n, none)]
  | .slice n lo w => [(n, some (lo, w))]
  | .index n idx ew => [(n, Lhs2.indexWin? idx ew)]
  | .concat ps => Lhs2.drvWinsList ps
termination_by structural t => t

/-- `Lhs2.drvWins`, concatenated over a list. -/
def Lhs2.drvWinsList : List Lhs2 → List DrvWin
  | [] => []
  | t :: ts => t.drvWins ++ Lhs2.drvWinsList ts
termination_by structural ts => ts
end

mutual
/-- The windows a statement assigns (any branch): `Lhs2.drvWins` of every
assignment target it holds — a run-time index covers the whole signal,
which is exactly its longest static prefix (IEEE 1800-2023 §11.5.3). -/
def Stmt2.drvWins : Stmt2 → List DrvWin
  | .blockingAssign t _ | .nbaAssign t _ => t.drvWins
  | .ifStmt _ t e => t.drvWins ++ Stmt2.drvWinsOpt e
  | .block body => Stmt2.drvWinsList body.toList
  | .caseStmt _ items dflt _ _ =>
      CaseItem2.drvWinsList items.toList ++ Stmt2.drvWinsOpt dflt
  | .unsupported _ _ => []
termination_by structural s => s

/-- `Stmt2.drvWins` of an optional statement. -/
def Stmt2.drvWinsOpt : Option Stmt2 → List DrvWin
  | none => []
  | some s => s.drvWins
termination_by structural o => o

/-- `Stmt2.drvWins`, concatenated over a list. -/
def Stmt2.drvWinsList : List Stmt2 → List DrvWin
  | [] => []
  | s :: ss => s.drvWins ++ Stmt2.drvWinsList ss
termination_by structural ss => ss

/-- `Stmt2.drvWins` of a case arm's body. -/
def CaseItem2.drvWins : CaseItem2 → List DrvWin
  | .mk _ body => body.drvWins
termination_by structural it => it

/-- `CaseItem2.drvWins`, concatenated over a list. -/
def CaseItem2.drvWinsList : List CaseItem2 → List DrvWin
  | [] => []
  | it :: rest => it.drvWins ++ CaseItem2.drvWinsList rest
termination_by structural its => its
end

/-- The signals a statement assigns (any branch). -/
def Stmt2.writes (s : Stmt2) : List String := s.drvWins.map (·.1)

/-- The windows a continuous assignment drives (`[]` for any other
process). -/
def Process2.drvWins : Process2 → List DrvWin
  | .assign t _ => t.drvWins
  | _ => []

/-- The windows a procedural process assigns (`[]` for a continuous
assignment or a loud process). -/
def Process2.procWins : Process2 → List DrvWin
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysComb b | .alwaysFFR _ _ b => b.drvWins
  | _ => []

/-- The signals a procedural process assigns (`[]` for a continuous
assignment or a loud process). -/
def Process2.procWrites (p : Process2) : List String := p.procWins.map (·.1)

/-- A procedure whose variables NO other process may write (IEEE 1800-2023
§9.2.2.2 `always_comb`, §9.2.2.4 `always_ff`): `alwaysComb`, `alwaysFF`,
and — conservatively — `alwaysFFR`, which does not record whether it came
from `always_ff` or from a plain `always @(posedge clk or negedge rn)`.
A plain `always @(posedge clk)` (`alwaysPlain`) is not exclusive. -/
def Process2.exclusive : Process2 → Bool
  | .alwaysComb _ | .alwaysFF _ _ | .alwaysFFR _ _ _ => true
  | _ => false

/-- Two windows share a bit: same signal, and either covers the whole
signal or the bit ranges intersect. -/
def DrvWin.overlaps (a b : DrvWin) : Bool :=
  a.1 == b.1 &&
    match a.2, b.2 with
    | some (l₁, w₁), some (l₂, w₂) => decide (l₁ < l₂ + w₂) && decide (l₂ < l₁ + w₁)
    | _, _ => true

/-- No two windows of the list share a bit. -/
def drvWinsDisjoint : List DrvWin → Bool
  | [] => true
  | w :: ws => ws.all (fun v => !w.overlaps v) && drvWinsDisjoint ws

/-- The continuous-driver windows of `ps` on the signals `names` (one
module's own declarations). -/
def driverWins (names : List String) (ps : List Process2) : List DrvWin :=
  ps.flatMap fun p => p.drvWins.filter fun w => names.contains w.1

/-- The procedural windows of `p` on the signals `names`. -/
def Process2.procWinsOn (names : List String) (p : Process2) : List DrvWin :=
  p.procWins.filter fun w => names.contains w.1

/-- Two procedural processes violate the `always_comb`/`always_ff`
exclusivity on `names`: one of them is exclusive (`Process2.exclusive`)
and some window of one shares a bit with some window of the other. -/
def Process2.exclClash (names : List String) (p q : Process2) : Bool :=
  (p.exclusive || q.exclusive) &&
    (p.procWinsOn names).any fun a => (q.procWinsOn names).any fun b => a.overlaps b

/-- No two processes of the list violate the `always_comb`/`always_ff`
exclusivity (`Process2.exclClash`) — a process may write its own windows
as often as it likes. -/
def procExclusiveOk (names : List String) : List Process2 → Bool
  | [] => true
  | p :: ps => ps.all (fun q => !p.exclClash names q) && procExclusiveOk names ps

/-- **One driver per bit** on a module's own signals `names` (module
docstring, "Drivers"), at window granularity (a constant select drives its
own bits; a whole-signal target or a run-time index the whole signal):
* the continuous assignments of `ps` — its own `assign`s and the
  output-port connections of its instances alike — drive pairwise disjoint
  windows;
* none of them is one of the module's INPUT ports `inputs` or shares a bit
  with a window a procedural process writes (IEEE 1800-2023 §6.5);
* no procedural process writes an input port (§23.3.3.2);
* no window an `always_comb`/`always_ff` process writes shares a bit with a
  window another process writes (§9.2.2.2/§9.2.2.4, `procExclusiveOk`). -/
def driversOk (names inputs : List String) (ps : List Process2) : Bool :=
  let ws := driverWins names ps
  let vs := ps.flatMap Process2.procWins
  let pw := ps.flatMap Process2.procWrites
  drvWinsDisjoint ws &&
    ws.all (fun w => !inputs.contains w.1 && vs.all (fun v => !w.overlaps v)) &&
    pw.all (fun n => !inputs.contains n) && procExclusiveOk names ps

/-- The signal of the first window that overlaps a later one. -/
def firstOverlap : List DrvWin → Option String
  | [] => none
  | w :: ws => if ws.any (w.overlaps ·) then some w.1 else firstOverlap ws

/-- The signal of the first `always_comb`/`always_ff` exclusivity
violation of the list (`Process2.exclClash`; diagnostics only). -/
def firstExclClash (names : List String) : List Process2 → Option String
  | [] => none
  | p :: ps =>
      let hit := ps.findSome? fun q =>
        if p.exclusive || q.exclusive then
          (p.procWinsOn names).findSome? fun a =>
            if (q.procWinsOn names).any (a.overlaps ·) then some a.1 else none
        else none
      match hit with
      | some n => some n
      | none => firstExclClash names ps

/-- The message of a failed `driversOk` (diagnostics only): the first
violated clause, naming its signal and the rule. -/
def driversMsg (mname : String) (names inputs : List String) (ps : List Process2) : String :=
  let ws := driverWins names ps
  let vs := ps.flatMap Process2.procWins
  let pw := ps.flatMap Process2.procWrites
  let tail := "net resolution (IEEE 1800-2023 §28.12) and the multiple-driver rules (§10.3.2) are outside the tier, so several drivers of one bit are never ordered"
  match firstOverlap ws with
  | some n =>
      s!"signal '{n}' of module '{mname}' has two continuous drivers on one bit at this parameter point (its own `assign`s, generate-loop ones included, and its instances' output ports count alike): {tail}"
  | none =>
      match ws.find? (fun w => vs.any (w.overlaps ·)) with
      | some w =>
          s!"signal '{w.1}' of module '{mname}' is driven both continuously (an `assign` or an instance output port) and by a procedural process on one bit at this parameter point (IEEE 1800-2023 §6.5 forbids the mixture on one longest static prefix): {tail}"
      | none =>
          match (ws.map (·.1) ++ pw).find? (inputs.contains ·) with
          | some n =>
              s!"input port '{n}' of module '{mname}' is driven inside the module (its connection, or the testbench at the top, already drives it): {tail}"
          | none =>
              match firstExclClash names ps with
              | some n =>
                  s!"signal '{n}' of module '{mname}' is written on one bit by an `always_comb`/`always_ff` procedure and by another process at this parameter point (IEEE 1800-2023 §9.2.2.2/§9.2.2.4: no other process may write such a procedure's variables, per longest static prefix §11.5.3; a run-time index covers the whole signal): the semantics would order the writes by process order, which no simulator is bound to"
              | none => s!"a signal of module '{mname}' has more than one driver after flattening: {tail}"

/-- A module's flattened design `m` under the one-driver rule for the
module's own signals (`names`, input ports `inputs`): `m` itself when
`driversOk`, otherwise `m` with a loud `PortConn:driver` process appended
(so `run2`, the differential runner and `load_design_sv2` all refuse). -/
def Design2.driverGuard (names inputs : List String) (m : Design2) : Design2 :=
  if driversOk names inputs m.processes.toList then m
  else
    let loud : Process2 :=
      .unsupported "PortConn:driver" (driversMsg m.name names inputs m.processes.toList)
    { m with processes := m.processes.push loud }

/-- A module's input-port names (before flattening; its own declaration
names are `PDesign.declNames`). -/
def PDesign.inputNames (d : PDesign) : List String :=
  (d.decls.filter (·.isInput)).map (·.name)

/-- `Design2.driverGuard` at the module's own signals. -/
def PDesign.driverGuard (d : PDesign) (m : Design2) : Design2 :=
  m.driverGuard d.declNames d.inputNames

/-- **A flat top under the one-driver rule** (module docstring, "Drivers";
2026-10-28, WP2): `instantiate2` at `args`, then `PDesign.driverGuard` at
the module's own signals — a design with two continuous drivers of one bit
at THIS parameter point (a genvar- or parameter-dependent overlap the
extractor's literal-window guard cannot see, a continuous driver of a
procedurally written variable, an input port written inside the module)
carries the loud `PortConn:driver` process. The differential runner and
`load_design_sv2`'s defaults gate instantiate a flat envelope through it;
`PDesign.instantiateGD2` is its total family (`name.sem`). -/
def PDesign.instantiateG2 (d : PDesign) (args : List Int) (iterFuel : Nat := 4096) :
    Res Design2 := do
  let m ← d.instantiate2 args iterFuel
  .ok (d.driverGuard m)

/-- **The total family of a flat envelope** (`name.sem` of a single-module
`load_design_sv2`, 2026-10-28, WP2): `PDesign.instantiateG2` at the surface
fuel, errors collapsed to the loud error design (the `instantiateD2`
twin). A proof about `name.sem` removes the guard with
`PDesign.instantiateGD2_of_ok` (`Hier2Gen.lean`) from the one-driver rule
on the instantiated process list. -/
def PDesign.instantiateGD2 (d : PDesign) (args : List Int) : Design2 :=
  match d.instantiateG2 args (PDesign.surfaceFuel args) with
  | .ok m => m
  | .timeout => .errorDesign d.name "generate expansion fuel exhausted"
  | .unsupported msg => .errorDesign d.name msg

/-! ## `instantiateH` -/

/-- `Gen2.lean`'s `PDesign.paramEnv2` from an initial environment `envI`
(the `int32` flag rides on it): parameters, localparams, enum tables, typed
parameter widths, packed-array geometry. -/
def PDesign.paramEnvH (envI : IEnv) (d : PDesign) (args : List Int) : Res IEnv := do
  let env0 ← bindParamsRes envI d.params args
  let env1 ← bindLocals env0 d.localParams
  let env2 ← bindEnums env1 d.enums
  let pws ← (d.params.map (fun p => (p.name, p.type?))
              ++ d.localParams.map (fun lp => (lp.name, lp.type?))).filterMapM
    fun (n, ty?) =>
      match ty? with
      | none => pure none
      | some ty =>
          match ty.width env2 with
          | .ok w => pure (some (n, w))
          | .error e => Res.unsupported s!"parameter '{n}' type: {e}"
  let env2 := { env2 with pwidths := pws }
  .ok { env2 with dims := dimTable env2 d.decls }

/-- The child instantiator of `instantiateRec`: the definition from the
library, the instance's parameter point (`PInst.given`, `PDesign.atPoint`),
then `rec` — the recursive instantiation one level down — under the
one-driver rule for the child's own signals (`PDesign.driverGuard`, at the
child's parameter point: instance-free children included) and the
clock-source rule with `clocks`, the instantiating module's input ports
(`Design2.clockGuard`). -/
def childInstOf (rec : PDesign → List Int → Res Design2) (lib : List PDesign)
    (clocks : List String) : ChildInst :=
  fun e i =>
    match lib.find? (·.name == i.module) with
    | none => .unsupported s!"instance '{i.name}': module '{i.module}' is not in the envelope's module library"
    | some c =>
        match i.given e c with
        | .error m => .unsupported s!"instance '{i.name}' of '{c.name}': {m}"
        | .ok given =>
            match c.atPoint given with
            | .error m => .unsupported s!"instance '{i.name}' of '{c.name}': {m}"
            | .ok (c', cargs) => do
                let cd ← rec c' cargs
                .ok ((c'.driverGuard cd).clockGuard clocks i)

/-- **The hierarchical instantiation core.** `depth` bounds the instance
nesting (exhausted = loud: only a recursive instantiation can exhaust
`lib.length + 1`); `lib` is the envelope's module library; children
instantiate at their own parameter point (`PInst.given`, `PDesign.atPoint`)
with the same initial environment (`int32` mode reaches every level). -/
def PDesign.instantiateRec : Nat → List PDesign → IEnv → PDesign → List Int → Nat →
    Res Design2
  | 0, _, _, d, _, _ =>
      .unsupported s!"module '{d.name}': instance hierarchy deeper than its module library (recursive instantiation is outside the tier)"
  | depth + 1, lib, envI, d, args, F =>
      if args.length != d.params.length then
        .unsupported s!"parameter arity: got {args.length}, want {d.params.length}"
      else do
        let env ← d.paramEnvH envI args
        let decls ← buildDecls env d.decls
        let elems ← buildElems env d.decls
        let envP := { env with widths := decls.map fun dc => (dc.name, dc.width) }
        let cb := childInstOf (fun c cargs => PDesign.instantiateRec depth lib envI c cargs F) lib
          (Decl.inputNames decls)
        let (idecls, gens) ← expandListH cb envP elems F d.generates
        .ok { name := d.name
              decls := (decls ++ idecls).toArray
              processes :=
                ((d.processes.map (instProcess2 envP elems)) ++ gens
                  ++ d.others.map fun (k, t) => Process2.unsupported k t).toArray }

/-- The top's one-driver rule (module docstring, "Drivers"): a top holding
an instance gets `PDesign.driverGuard`; an instance-free top is the flat
tier's, unchanged. -/
def PDesign.topGuard (d : PDesign) (m : Design2) : Design2 :=
  if GenItem.listInstFree d.generates then m else d.driverGuard m

/-- `instantiateRec` at the library's depth bound, from `envI`, under the
top's one-driver rule. -/
def PDesign.instantiateHFrom (envI : IEnv) (d : PDesign) (lib : List PDesign)
    (args : List Int) (iterFuel : Nat := 4096) : Res Design2 := do
  let m ← PDesign.instantiateRec (lib.length + 1) lib envI d args iterFuel
  .ok (d.topGuard m)

/-- **THE hierarchical semantic-tier instantiation** (`name.sem` of a
hierarchical envelope): `instantiate2` with every module instance flattened
(module docstring). On an instance-free design it IS `instantiate2`
(`Hier2Gen.lean`, `PDesign.instantiateH_flat`). -/
def PDesign.instantiateH (d : PDesign) (lib : List PDesign) (args : List Int)
    (iterFuel : Nat := 4096) : Res Design2 :=
  d.instantiateHFrom {} lib args iterFuel

/-- Total `Design2` family of a hierarchical envelope (the `load_design_sv2`
binder encoding's `name.sem`): errors collapse to the loud error design. -/
def PDesign.instantiateHD2 (d : PDesign) (lib : List PDesign) (args : List Int) : Design2 :=
  match d.instantiateH lib args (PDesign.surfaceFuel args) with
  | .ok m => m
  | .timeout => .errorDesign d.name "generate expansion fuel exhausted"
  | .unsupported msg => .errorDesign d.name msg

/-- `PDesign.int32Agrees` for a hierarchical design (the `int32` mode
reaches every level of the hierarchy). -/
def PDesign.int32AgreesH (d : PDesign) (lib : List PDesign) (args : List Int) : Bool :=
  let F := PDesign.surfaceFuel args
  match d.instantiateHFrom {} lib args F, d.instantiateHFrom { int32 := true } lib args F with
  | .ok m₁, .ok m₂ =>
      m₁.decls.toList == m₂.decls.toList &&
        toString (repr m₁.processes) == toString (repr m₂.processes)
  | .unsupported a, .unsupported b => a == b
  | .timeout, .timeout => true
  | _, _ => false

/-- Declared names are pairwise distinct (the load gate's and the
differential runner's re-check of the hierarchical naming — module
docstring, "Names"). -/
def Design2.namesNodup (d : Design2) : Bool :=
  go d.decls.toList []
where
  go : List Decl → List String → Bool
    | [], _ => true
    | dc :: rest, seen => !seen.contains dc.name && go rest (dc.name :: seen)

/-! ## Hand-built smoke (the acceptance designs live in `Examples/`) -/

/-- A full adder (no parameters). -/
private def pFA : PDesign :=
  { name := "fa", params := [], localParams := [], enums := []
    decls := [{ name := "a", type := .packed [] (some 1), isInput := true },
              { name := "b", type := .packed [] (some 1), isInput := true },
              { name := "ci", type := .packed [] (some 1), isInput := true },
              { name := "s", type := .packed [] (some 1), isOutput := true },
              { name := "co", type := .packed [] (some 1), isOutput := true }]
    processes :=
      [.assign "s" (.binary (.m0 .xor) (.binary (.m0 .xor) (.ident "a") (.ident "b")) (.ident "ci")),
       .assign "co" (.binary (.m0 .or) (.binary (.m0 .and) (.ident "a") (.ident "b"))
          (.binary (.m0 .and) (.ident "ci") (.binary (.m0 .xor) (.ident "a") (.ident "b"))))]
    generates := [] }

private def wN : PDim := ⟨.binary (.m0 .sub) (.paramRef "N" none) (.int 1), .int 0⟩

/-- An `N`-bit ripple adder of `fa` instances in a generate loop. -/
private def pRip : PDesign :=
  { name := "rip", params := [{ name := "N", default? := some (.int 4), resolved? := some 4 }]
    localParams := [], enums := []
    decls := [{ name := "x", type := .packed [wN] none, isInput := true },
              { name := "y", type := .packed [wN] none, isInput := true },
              { name := "z", type := .packed [wN] none, isOutput := true },
              { name := "c", type := .packed [⟨.paramRef "N" none, .int 0⟩] none }]
    processes := [.assignL (.bitSel "c" (.int 0)) (.lit (.lit "0"))]
    generates :=
      [.genFor (some "g") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
        (.unary .inc (.genvarRef "i")) none
        [.inst { name := "u", module := "fa", path := [⟨"g", some "i"⟩]
                 conns := [.input "a" (some (.bitSel (.ident "x") (.genvarRef "i"))) true,
                           .input "b" (some (.bitSel (.ident "y") (.genvarRef "i"))) true,
                           .input "ci" (some (.bitSel (.ident "c") (.genvarRef "i"))) true,
                           .output "s" (some (.bitSel "z" (.genvarRef "i"))),
                           .output "co" (some (.bitSel "c"
                              (.binary (.m0 .add) (.genvarRef "i") (.int 1))))] }]] }

private def ripAt (n : Nat) (x y : Nat) : Option String :=
  match pRip.instantiateH [pFA] [n] with
  | .ok d =>
      match run2 d σ_src 1000 [[("x", .ofNat n x), ("y", .ofNat n y)]] with
      | .ok [st] => (SvState.lookup st "z").map LVec.toBinString
      | _ => none
  | _ => none

-- The ripple of instances adds (3 + 5 = 8 at N = 4; 13 + 7 = 20 ≡ 4 at N = 4).
#guard ripAt 4 3 5 == some "1000"
#guard ripAt 4 13 7 == some "0100"
#guard ripAt 1 1 1 == some "0"
-- Hierarchical names, hoisted after the parent's declarations.
#guard (match pRip.instantiateH [pFA] [2] with
        | .ok d => d.decls.toList.map (·.name) ==
            ["x", "y", "z", "c", "g[0].u.a", "g[0].u.b", "g[0].u.ci", "g[0].u.s", "g[0].u.co",
             "g[1].u.a", "g[1].u.b", "g[1].u.ci", "g[1].u.s", "g[1].u.co"]
            && d.namesNodup
            && (d.decls.toList.filter (·.name.startsWith "g[")).all
                 (fun dc => !dc.isInput && !dc.isOutput)
        | _ => false)
-- Without the library the instance is loud, never silently dropped.
#guard (match pRip.instantiateH [] [2] with
        | .unsupported m => m.startsWith "instance 'u'"
        | _ => false)
-- The flat instantiation keeps the instance as a loud process.
#guard (match pRip.instantiate2 [2] with
        | .ok d => d.hasUnsupported
        | _ => false)
-- Recursive instantiation exhausts the depth bound loudly.
private def pSelf : PDesign :=
  { pFA with name := "self", generates := [.inst { name := "me", module := "self" }] }
#guard (match pSelf.instantiateH [pSelf] [] with
        | .unsupported m => (m.splitOn "recursive").length > 1
        | _ => false)
-- An instance-free design instantiates exactly as `instantiate2`.
#guard (match pFA.instantiateH [pRip] [], pFA.instantiate2 [] with
        | .ok a, .ok b => a.decls.toList == b.decls.toList &&
            toString (repr a.processes) == toString (repr b.processes)
        | _, _ => false)

-- Port-width coercion (module docstring): a context-sensitive input actual
-- narrower than its port is loud; at least as wide, or port-safe, it is an
-- assignment; an unconnected input net reads z, a variable keeps its x.
private def cwEnv : IEnv := { widths := [("p", 2), ("q", 2)] }
private def cwElems : List (String × Nat) := [("p", 1), ("q", 1)]
private def cwPort (w : Nat) : Decl := { name := "x", width := w, isInput := true }
private def cwConn (e : PExpr) : List PConn := [.input "x" (some e) false]
private def loudKind : List Process2 → Option String
  | [.unsupported k _] => some k
  | _ => none
private def pPlus : PExpr := .binary (.m0 .add) (.ident "p") (.ident "q")
private def pAnd : PExpr := .binary (.m0 .and) (.ident "p") (.ident "q")
#guard loudKind (connProcs cwEnv cwElems "u." (cwConn pPlus) (cwPort 4)) == some "PortConn:context-width"
#guard loudKind (connProcs cwEnv cwElems "u." (cwConn (.unary (.m0 .bnot) (.ident "p"))) (cwPort 4))
  == some "PortConn:context-width"
#guard (match connProcs cwEnv cwElems "u." (cwConn pPlus) (cwPort 2) with
        | [.assign (.ident "u.x") _] => true | _ => false)
#guard (match connProcs cwEnv cwElems "u." (cwConn pAnd) (cwPort 4) with
        | [.assign (.ident "u.x") _] => true | _ => false)
#guard (match connProcs cwEnv cwElems "u." (cwConn (.ident "p")) (cwPort 4) with
        | [.assign (.ident "u.x") (.resize 4 (.ident "p"))] => true | _ => false)
#guard (match connProcs cwEnv cwElems "u." [.input "x" none true] (cwPort 3) with
        | [.assign (.ident "u.x") (.lit v)] => v.toBinString == "zzz" | _ => false)
#guard (connProcs cwEnv cwElems "u." [.input "x" none false] (cwPort 3)).isEmpty
#guard loudKind (connProcs cwEnv cwElems "u." [] (cwPort 3)) == some "PortConn:missing"
-- Round 6 (H1): a CONNECTED input with `net` set (a net formal bound to a bare
-- net actual) is loud when the actual is narrower than the port, and
-- unchanged otherwise — equal or wider actual, `net` unset (a variable
-- actual or formal, an expression: every tool zero-extends those).
private def cwNetConn (e : PExpr) : List PConn := [.input "x" (some e) true]
#guard loudKind (connProcs cwEnv cwElems "u." (cwNetConn (.ident "p")) (cwPort 4))
  == some "PortConn:net-width"
#guard (match connProcs cwEnv cwElems "u." (cwNetConn (.ident "p")) (cwPort 2) with
        | [.assign (.ident "u.x") (.ident "p")] => true | _ => false)
#guard (match connProcs cwEnv cwElems "u." (cwNetConn (.ident "p")) (cwPort 1) with
        | [.assign (.ident "u.x") (.resize 1 (.ident "p"))] => true | _ => false)
#guard (match connProcs cwEnv cwElems "u." (cwConn (.ident "p")) (cwPort 4) with
        | [.assign (.ident "u.x") (.resize 4 (.ident "p"))] => true | _ => false)

-- Fills in a narrower input actual take the LRM (port-width) reading
-- anywhere, Verilator 5.042 and Yosys 0.53 agreeing (module docstring);
-- Icarus 12.0 pads the nested ones with zeros (declared row
-- `hier_fill_ctx`). A 2-bit `p` into a 4-bit pass-through port:
private def pPass : PDesign :=
  { name := "pass", params := [], localParams := [], enums := []
    decls := [{ name := "x", type := .packed [⟨.int 3, .int 0⟩] (some 4), isInput := true },
              { name := "y", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true }]
    processes := [.assign "y" (.ident "x")]
    generates := [] }
private def pFillTop (e : PExpr) : PDesign :=
  { name := "ft", params := [], localParams := [], enums := []
    decls := [{ name := "p", type := .packed [⟨.int 1, .int 0⟩] (some 2), isInput := true },
              { name := "s", type := .packed [] (some 1), isInput := true },
              { name := "y", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true }]
    processes := []
    generates :=
      [.inst { name := "u", module := "pass"
               conns := [.input "x" (some e) false, .output "y" (some (.ident "y"))] }] }
private def fillAt (e : PExpr) (p s : Nat) : Option String :=
  match (pFillTop e).instantiateH [pPass] [] with
  | .ok d =>
      match run2 d σ_src 1000 [[("p", .ofNat 2 p), ("s", .ofNat 1 s)]] with
      | .ok [st] => (SvState.lookup st "y").map LVec.toBinString
      | _ => none
  | _ => none
-- `p ^ '1` at p = 01: `1110` (Icarus: `0010`).
#guard fillAt (.binary (.m0 .xor) (.ident "p") (.fill .l1)) 1 0 == some "1110"
-- `p | '1` at p = 00: `1111` (Icarus: `0011`).
#guard fillAt (.binary (.m0 .or) (.ident "p") (.fill .l1)) 0 0 == some "1111"
-- `s ? '1 : p` at s = 1: `1111` (Icarus: `0011`).
#guard fillAt (.ternary (.ident "s") (.fill .l1) (.ident "p")) 0 1 == some "1111"
-- Masked widened bits agree in every tool: `p & '1`, `s ? '0 : p`, bare `'1`.
#guard fillAt (.binary (.m0 .and) (.ident "p") (.fill .l1)) 1 0 == some "0001"
#guard fillAt (.ternary (.ident "s") (.fill .l0) (.ident "p")) 2 0 == some "0010"
#guard fillAt (.fill .l1) 0 0 == some "1111"

-- Clocks: a child flop clocked through a bare connection IS the parent's
-- flop (clock name substituted); any other clock connection is loud.
private def pReg : PDesign :=
  { name := "reg1", params := [], localParams := [], enums := []
    decls := [{ name := "ck", type := .packed [] (some 1), isInput := true },
              { name := "d", type := .packed [] (some 1), isInput := true },
              { name := "q", type := .packed [] (some 1), isOutput := true }]
    processes := [.alwaysFF "ck" (.nbaAssign "q" (.ident "d"))]
    generates := [] }
private def pTop (ck : PExpr) : PDesign :=
  { name := "top", params := [], localParams := [], enums := []
    decls := [{ name := "clk", type := .packed [] (some 1), isInput := true },
              { name := "en", type := .packed [] (some 1), isInput := true },
              { name := "d", type := .packed [] (some 1), isInput := true },
              { name := "q", type := .packed [] (some 1), isOutput := true }]
    processes := []
    generates :=
      [.inst { name := "r", module := "reg1"
               conns := [.input "ck" (some ck) false, .input "d" (some (.ident "d")) false,
                         .output "q" (some (.ident "q"))] }] }
#guard (match (pTop (.ident "clk")).instantiateH [pReg] [] with
        | .ok d => d.processes.toList.any fun p =>
            match p with
            | .alwaysFF "clk" (.nbaAssign (.ident "r.q") (.ident "r.d")) => true
            | _ => false
        | _ => false)
#guard (match (pTop (.binary (.m0 .and) (.ident "clk") (.ident "en"))).instantiateH [pReg] [] with
        | .ok d => d.processes.toList.any fun p =>
            match p with
            | .unsupported "Instance:clock" _ => true
            | _ => false
        | _ => false)
-- A bare connection to a DERIVED parent signal (`assign gclk = clk & en`)
-- is loud: the single-clock cycle semantics would fire it while en = 0.
private def pTopG : PDesign :=
  { pTop (.ident "gclk") with
    decls := (pTop (.ident "gclk")).decls ++ [{ name := "gclk", type := .packed [] (some 1) }]
    processes := [.assign "gclk" (.binary (.m0 .and) (.ident "clk") (.ident "en"))] }
#guard (match pTopG.instantiateH [pReg] [] with
        | .ok d => d.processes.toList.any fun p =>
            match p with
            | .unsupported "Instance:clock" _ => true
            | _ => false
        | _ => false)
-- A child flop on a child-INTERNAL signal is loud.
private def pRegI : PDesign :=
  { pReg with
    decls := pReg.decls ++ [{ name := "ick", type := .packed [] (some 1) }]
    processes := [.assign "ick" (.ident "ck"), .alwaysFF "ick" (.nbaAssign "q" (.ident "d"))] }
#guard (match (pTop (.ident "clk")).instantiateH [pRegI] [] with
        | .ok d => d.processes.toList.any fun p =>
            match p with
            | .unsupported "Instance:clock" _ => true
            | _ => false
        | _ => false)
-- Two levels: the top's `clk` through `mid`'s input port `ck` to `reg1`'s.
private def pMid : PDesign :=
  { pReg with
    name := "mid"
    processes := []
    generates :=
      [.inst { name := "r", module := "reg1"
               conns := [.input "ck" (some (.ident "ck")) false,
                         .input "d" (some (.ident "d")) false,
                         .output "q" (some (.ident "q"))] }] }
#guard (match ({ pTop (.ident "clk") with
                 generates :=
                   [.inst { name := "m", module := "mid"
                            conns := [.input "ck" (some (.ident "clk")) false,
                                      .input "d" (some (.ident "d")) false,
                                      .output "q" (some (.ident "q"))] }] } : PDesign).instantiateH
          [pMid, pReg] [] with
        | .ok d => !d.hasUnsupported && d.processes.toList.any fun p =>
            match p with
            | .alwaysFF "clk" (.nbaAssign (.ident "m.r.q") (.ident "m.r.d")) => true
            | _ => false
        | _ => false)
-- The flattened flop runs: d = 1 sampled at the first posedge.
#guard (match (pTop (.ident "clk")).instantiateH [pReg] [] with
        | .ok d =>
            match run2 d σ_src 1000 [[("clk", .ofNat 1 0), ("en", .ofNat 1 0), ("d", .ofNat 1 1)]] with
            | .ok [st] => (SvState.lookup st "q").map LVec.toBinString == some "1"
            | _ => false
        | _ => false)

-- An UNTYPED child parameter overridden by the parent's `int` parameter:
-- admitted, and identical under exact 32-bit `int` constants (`int32AgreesH`
-- — the INT parameters live in `nvals` there); a sized override is refused.
private def pUnt : PDesign :=
  { name := "unt", params := [{ name := "W", default? := some (.int 2), resolved? := some 2 }]
    localParams := [], enums := []
    decls := [{ name := "y", type := .packed [⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1),
                                               .int 0⟩] none, isOutput := true }]
    processes := [.assign "y" (.fill .l1)]
    generates := [] }
private def pUser (ov : PExpr) : PDesign :=
  { name := "user", params := [{ name := "N", default? := some (.int 3), resolved? := some 3 }]
    localParams := [], enums := []
    decls := [{ name := "o", type := .packed [wN] none, isOutput := true }]
    processes := []
    generates :=
      [.inst { name := "u", module := "unt", params := [("W", ov)]
               conns := [.output "y" (some (.ident "o"))] }] }
#guard (pUser (.paramRef "N" none)).int32AgreesH [pUnt] [5]
#guard (match (pUser (.paramRef "N" none)).instantiateH [pUnt] [5] with
        | .ok d => d.decls.toList.map (·.width) == [5, 5]
        | _ => false)
#guard (match (pUser (.lit (.lit "101"))).instantiateH [pUnt] [5] with
        | .unsupported m => (m.splitOn "no declared type").length > 1
        | _ => false)

-- Drivers (module docstring, "Drivers"): after flattening, a bit of a
-- module's own signal has ONE driver. Two instance outputs on one signal
-- (verifier repro `w_multi1`: Icarus resolves the wire), a parent `assign`
-- and an instance output on the same bit (`w_multi2`; `w_inval`, illegal
-- for a variable), an instance output into a signal a procedural process
-- writes, an instance output into the module's own input port, and a
-- child writing its own input port are all loud (`PortConn:driver`);
-- instance outputs on DISJOINT bits are admitted.
private def pDrv : PDesign :=
  { name := "drv", params := [], localParams := [], enums := []
    decls := [{ name := "en", type := .packed [] (some 1), isInput := true },
              { name := "y", type := .packed [] (some 1), isOutput := true }]
    processes := [.assign "y" (.ident "en")]
    generates := [] }
private def pBus (extra : List PProcess) (t1 t2 : PLhs) : PDesign :=
  { name := "bus", params := [], localParams := [], enums := []
    decls := [{ name := "e1", type := .packed [] (some 1), isInput := true },
              { name := "e2", type := .packed [] (some 1), isInput := true },
              { name := "o", type := .packed [⟨.int 1, .int 0⟩] (some 2), isOutput := true }]
    processes := extra
    generates :=
      [.inst { name := "d1", module := "drv"
               conns := [.input "en" (some (.ident "e1")) false, .output "y" (some t1)] },
       .inst { name := "d2", module := "drv"
               conns := [.input "en" (some (.ident "e2")) false, .output "y" (some t2)] }] }
private def driverLoud (d : PDesign) (lib : List PDesign) : Bool :=
  match d.instantiateH lib [] with
  | .ok m => m.processes.toList.any fun p =>
      match p with
      | .unsupported "PortConn:driver" _ => true
      | _ => false
  | _ => false
private def o0 : PLhs := .bitSel "o" (.int 0)
private def o1 : PLhs := .bitSel "o" (.int 1)
-- Two instance outputs on one signal, on one bit, or a bit and the whole.
#guard driverLoud (pBus [] (.ident "o") (.ident "o")) [pDrv]
#guard driverLoud (pBus [] o1 o1) [pDrv]
#guard driverLoud (pBus [] o0 (.ident "o")) [pDrv]
-- A parent `assign` and an instance output on one bit.
#guard driverLoud (pBus [.assignL o1 (.ident "e1")] o0 o1) [pDrv]
#guard driverLoud (pBus [.assign "o" (.ident "e1")] o0 o1) [pDrv]
-- A parent procedural write and an instance output.
#guard driverLoud (pBus [.alwaysComb (.blockingAssignL o1 (.ident "e1"))] o0 o1) [pDrv]
-- An instance output into the module's own input port.
#guard driverLoud (pBus [] o0 (.ident "e1")) [pDrv]
-- The message names the violated clause and its signal.
private def driverMsgOf (d : PDesign) (lib : List PDesign) : String :=
  match d.instantiateH lib [] with
  | .ok m => (m.processes.toList.findSome? fun p =>
      match p with
      | .unsupported "PortConn:driver" t => some t
      | _ => none).getD ""
  | _ => ""
#guard (driverMsgOf (pBus [] o1 o1) [pDrv]).startsWith
  "signal 'o' of module 'bus' has two continuous drivers on one bit"
#guard (driverMsgOf (pBus [.alwaysComb (.blockingAssignL o1 (.ident "e1"))] o0 o1) [pDrv]).startsWith
  "signal 'o' of module 'bus' is driven both continuously"
#guard (driverMsgOf (pBus [] o0 (.ident "e1")) [pDrv]).startsWith
  "input port 'e1' of module 'bus' is driven inside the module"
-- Disjoint bits: admitted, and the flattened design runs (o = {e2, e1}).
#guard !driverLoud (pBus [] o0 o1) [pDrv]
#guard (match (pBus [] o0 o1).instantiateH [pDrv] [] with
        | .ok d =>
            match run2 d σ_src 1000 [[("e1", .ofNat 1 1), ("e2", .ofNat 1 0)]] with
            | .ok [st] => (SvState.lookup st "o").map LVec.toBinString == some "01"
            | _ => false
        | _ => false)
-- A child writing its own input port (its connection drives it too), and
-- a child whose own `assign`s overlap at its parameter point: loud even
-- though the child holds no instance (the child-level rule).
private def pDrvIn : PDesign :=
  { pDrv with processes := [.assign "y" (.ident "en"), .assign "en" (.int 0)] }
#guard driverLoud (pBus [] o0 o1) [pDrvIn]
private def pDrvTwice : PDesign :=
  { pDrv with processes := [.assign "y" (.ident "en"), .assign "y" (.int 0)] }
#guard driverLoud (pBus [] o0 o1) [pDrvTwice]
-- An instance-free TOP: `instantiateH` itself stays the flat tier's,
-- guard-free (`instantiateH_flat`); the rule is applied by the callers that
-- know the top is flat — `instantiateG2`/`instantiateGD2` (`name.sem`, the
-- differential runner, `load_design_sv2`'s defaults gate; WP2).
#guard (match pDrvTwice.instantiateH [] [] with
        | .ok m => !m.hasUnsupported
        | _ => false)
private def flatLoud (d : PDesign) (args : List Int) : Bool :=
  match d.instantiateG2 args with
  | .ok m => m.processes.toList.any fun p =>
      match p with
      | .unsupported "PortConn:driver" _ => true
      | _ => false
  | _ => false
#guard flatLoud pDrvTwice []
#guard flatLoud pDrvIn []
#guard !flatLoud pDrv []
-- WP2's probe: `for (genvar i = 0; i < 4; i++) assign y[i/2] = a[i];` — the
-- windows depend on the genvar, so the extractor's literal-window guard
-- never sees the two drivers of `y[0]` and `y[1]`; before WP2 it ran with
-- the drivers ordered by issue (`y = xx00` at `a = 0101`, where Icarus and
-- Yosys report multiple drivers). The total family carries the loud process.
private def pGv (div : Int) (yw : Nat) : PDesign :=
  { name := "gvov", params := [], localParams := [], enums := []
    decls := [{ name := "a", type := .packed [⟨.int 3, .int 0⟩] (some 4), isInput := true },
              { name := "y", type := .packed [⟨.int (yw - 1 : Nat), .int 0⟩] (some yw),
                isOutput := true }]
    processes := []
    generates :=
      [.genFor (some "g") "i" (.int 0) (.binary .slt (.genvarRef "i") (.int 4))
        (.unary .inc (.genvarRef "i")) none
        [.process (.assignL (.bitSel "y" (.binary .div (.genvarRef "i") (.int div)))
          (.bitSel (.ident "a") (.genvarRef "i")))]] }
#guard flatLoud (pGv 2 2) []
#guard (pGv 2 2).instantiateGD2 [] |>.processes.toList.any fun p =>
  match p with
  | .unsupported "PortConn:driver" t =>
      t.startsWith "signal 'y' of module 'gvov' has two continuous drivers on one bit"
  | _ => false
-- `y[i/1]` over a 4-bit `y`: one bit per genvar value, admitted.
#guard !flatLoud (pGv 1 4) []
-- A parameter-dependent overlap: `y[1:0] = a; y[K+1:K] = b;` — disjoint at
-- `K = 2` (admitted, guard-free), overlapping at `K = 1` and `K = 0` (loud).
private def pParOv : PDesign :=
  { name := "parov"
    params := [{ name := "K", default? := some (.int 2), resolved? := some 2 }]
    localParams := [], enums := []
    decls := [{ name := "a", type := .packed [⟨.int 1, .int 0⟩] (some 2), isInput := true },
              { name := "b", type := .packed [⟨.int 1, .int 0⟩] (some 2), isInput := true },
              { name := "y", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true }]
    processes :=
      [.assignL (.partSel "y" (.int 1) (.int 0)) (.ident "a"),
       .assignL (.partSel "y" (.binary (.m0 .add) (.paramRef "K" none) (.int 1)) (.paramRef "K" none))
         (.ident "b")]
    generates := [] }
#guard !flatLoud pParOv [2]
#guard flatLoud pParOv [1]
#guard flatLoud pParOv [0]
#guard (match pParOv.instantiateG2 [2], pParOv.instantiate2 [2] with
        | .ok m, .ok m' => toString (repr m.processes) == toString (repr m'.processes)
        | _, _ => false)
-- Procedural writers (WP2 repair), at window granularity. Two
-- `always_comb` (or `always_ff`) writers of one bit break §9.2.2.2/§9.2.2.4
-- and are loud — including at one parameter point only (`y[K]` against
-- `y[0]` at `K = 0`) and through a run-time index (`y[s]` is the whole
-- signal); a continuous driver of a procedurally written BIT is the §6.5
-- mixture, but a continuous driver of ANOTHER bit of the variable is legal
-- and admitted; two plain `always @(posedge clk)` writers are legal and
-- admitted.
private def pPw (ps : List PProcess) : PDesign :=
  { name := "pw"
    params := [{ name := "K", default? := some (.int 1), resolved? := some 1 }]
    localParams := [], enums := []
    decls := [{ name := "clk", type := .packed [] (some 1), isInput := true },
              { name := "s", type := .packed [] (some 1), isInput := true },
              { name := "a", type := .packed [⟨.int 1, .int 0⟩] (some 2), isInput := true },
              { name := "y", type := .packed [⟨.int 1, .int 0⟩] (some 2), isOutput := true }]
    processes := ps
    generates := [] }
private def pwA (i : Int) : PExpr := .bitSel (.ident "a") (.int i)
private def pwY (i : PExpr) : PLhs := .bitSel "y" i
private def pwComb (i : PExpr) (j : Int) : PProcess := .alwaysComb (.blockingAssignL (pwY i) (pwA j))
#guard flatLoud (pPw [pwComb (.int 0) 0, pwComb (.int 0) 1]) [1]
#guard (pPw [pwComb (.int 0) 0, pwComb (.int 0) 1]).instantiateGD2 [1]
  |>.processes.toList.any fun p =>
  match p with
  | .unsupported "PortConn:driver" t =>
      t.startsWith "signal 'y' of module 'pw' is written on one bit by an `always_comb`/`always_ff` procedure"
  | _ => false
#guard !flatLoud (pPw [pwComb (.int 0) 0, pwComb (.int 1) 1]) [1]
#guard !flatLoud (pPw [pwComb (.int 0) 0, pwComb (.paramRef "K" none) 1]) [1]
#guard flatLoud (pPw [pwComb (.int 0) 0, pwComb (.paramRef "K" none) 1]) [0]
#guard flatLoud (pPw [pwComb (.ident "s") 0, pwComb (.int 1) 1]) [1]
#guard flatLoud (pPw [.alwaysFF "clk" (.nbaAssignL (pwY (.int 0)) (pwA 0)),
                      .alwaysFF "clk" (.nbaAssignL (pwY (.int 0)) (pwA 1))]) [1]
#guard flatLoud (pPw [.alwaysPlain "clk" (.nbaAssignL (pwY (.int 0)) (pwA 0)),
                      .alwaysFF "clk" (.nbaAssignL (pwY (.int 0)) (pwA 1))]) [1]
#guard !flatLoud (pPw [.alwaysPlain "clk" (.nbaAssignL (pwY (.int 0)) (pwA 0)),
                       .alwaysPlain "clk" (.nbaAssignL (pwY (.int 0)) (pwA 1))]) [1]
-- One process writing a bit twice (default, then override) is one writer.
#guard !flatLoud (pPw [.alwaysComb (.block [.blockingAssignL (.ident "y") (.int 0),
                                            .blockingAssignL (pwY (.int 0)) (pwA 1)])]) [1]
-- The §6.5 mixture, at window granularity.
#guard !flatLoud (pPw [pwComb (.int 0) 0, .assignL (pwY (.int 1)) (pwA 1)]) [1]
#guard flatLoud (pPw [pwComb (.int 0) 0, .assignL (pwY (.paramRef "K" none)) (pwA 1)]) [0]
#guard (pPw [pwComb (.int 0) 0, .assignL (pwY (.int 0)) (pwA 1)]).instantiateGD2 [1]
  |>.processes.toList.any fun p =>
  match p with
  | .unsupported "PortConn:driver" t =>
      t.startsWith "signal 'y' of module 'pw' is driven both continuously"
  | _ => false

end LeanModels.Sv
