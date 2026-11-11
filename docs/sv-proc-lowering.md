# Procedural and Verilog-2001 lowerings of the symbolic tier (WP-PROC)

Contract of the extractor lowerings that give the sv-0.2 tier the constructs real code is written in: typeless declarations,
`wire` and implicit nets, `always @*`, block-local declarations, compound assignment, more loop headers. Design, evidence and
the plan: `svgolf/design/real-world-sv/PROC-NOTE.md`. Code: `extractors/sv/extract.py` (one-line or few-line hooks) and
`extractors/sv/lower_proc.py` (the logic); tests `extractors/sv/test_lower_proc.py`; differential rows `proc_*` in
`harness/sv/cases2.json` (Xcelium-pinned in `harness/sv/xcelium_golden.json`).

The principles every item follows:

1. **Refuse when in doubt.** A lowering is trusted code: it admits a precisely stated shape and leaves every other spelling
   the loud `Unsupported` node it had (same `sv_kind` tags, same register rows, the refusal text says which rule failed).
2. **Monotone.** A source that was admitted before gets the same envelope byte for byte. `harness/sv/regress_envelopes.py`
   checks it: it re-extracts the committed symbolic envelopes and the svGolf designs with the old and the new extractor and
   fails if an envelope that had no `Unsupported` node changed (below).
3. **No decision at the default point.** A lowering never reads a parameter's value to decide; shapes are the same at every
   point (the `--probe-points` cross-check would otherwise report a difference).
4. **4-state faithful.** The lowered tree is executed by Lean's own semantics: `if (x)` takes the else branch, `case` is exact
   equality; nothing is rewritten to `?:`.

## N1. Typeless declarations

`input [N-1:0] a`, `output wire [7:0] y`, `wire [N-1:0] x`, a Verilog-2001 header's `input [N-1:0] a, b;` have the
ImplicitType syntax; `_dtype_sym` recovers its dimensions like those of a `logic` declaration. The declaration is a well-formed
`PackedType`; whether a NET declaration is admitted is a separate question (N2, register `dc-net-z`).

## N3. `--top` of an instantiated module

`_sym_top_compilation` passes `topModules = {T}` at every point. A module that another module of the same sources
instantiates can be the top.

## C1. Compound assignment

`x op= e` in a procedural body of the symbolic tier is the blocking assignment `x = x op e` (IEEE 1800-2023 11.4.1) with the
selectors of the target evaluated once. slang binds the statement as `x = (<lvalue reference> op e)`: the right-hand side is
the converted expression with a placeholder where the target is read, and `_convert_selected_leaf` puts the converted READ of
the target there (`_COMPOUND_READ`), so the operand widths, the signedness and the context sizing are exactly slang's. Reading
the target's selectors twice (once for the read, once for the write) is reading them once only when the target and the
right-hand side are source-pure, so that is the admission test (`_case_source_expression_ok`); a read whose width differs
from the target's is refused. Admitted: whole variables, constant and run-time bit selects, constant part selects, fixed
unpacked cells, inside unrolled loops; operators `+ - * / % & | ^ << >> <<< >>>`. Refused (tag `AssignmentExpression:compound`
as before): nonblocking and timed forms, an effectful target or right-hand side, any other operator, a target the tier does
not take. Statement-position `x++` / `x--` were already lowered by master.

Rows: `proc_compound` (whole, bit, part, run-time index, a clmul accumulate, a popcount) and `proc_compound_param_n3/n4/n8`
(the same inside a parametric family).

For source-structure audits, `extract.py --top T --retain-proc-rewrites` keeps
the compound statement as a `CompoundAssign` envelope node with its target,
operator and right-hand side. `Ingest2` maps that retained node to the named
`AssignmentExpression:compound` `Unsupported` PStmt because frozen `Stmt2` has
no compound constructor. The default lowering and all existing rows are
unchanged; this mode is a loud source-preserving boundary until the retained
Sv AST is available.

## USERFN. User-function calls

The established symbolic path inlines only the narrow pure automatic-function
shapes covered by the function-call tests: input-only formals, source-pure
expressions, and the admitted straight-line, conditional, and case local-return
forms. With `--retain-proc-rewrites`, a call to a source-declared function is
kept as a `FunctionCall` envelope node with its name and converted actuals;
`Ingest2` reports `CallExpression:user-function` because frozen `PExpr` has no
call constructor. System calls and the default pure inliner are unchanged.

## X1. Loop header forms

The retained `For` path takes a source-pure counted loop whose header declares ONE `int` iterator with a literal
initializer, compares it with a literal and steps it by a literal. X1 admits the spellings real Verilog-2001 code uses for
the same loops: the iterator declared OUTSIDE the header (`integer i; ... for (i = 0; i < 8; i = i + 1)`), the step `i += c` /
`i -= c`, and the comparisons `<=` and `>=`.

The source iterator and its declaration stay in the retained header; no
compile-time binding or declaration erasure is performed. A parameter-bound
header is instantiated by the semantic tier's trip schema, while a literal
header is represented by the same `For` node and has no extraction cap.

Rows: `proc_loop_forms` (module-level `integer` shared by several loops, `<=`, `>=`, `+=`, `i--`), `proc_loop_forms_local` (a
block-local iterator), `proc_loop_forms2` (declared headers refused by master only for the operator name, a stride-2 loop), and
`symbolic_parameter_for_external` (an external iterator with a parameter bound and the point cross-check).

An admitted parameter-bound loop may contain another admitted parameter-bound
loop whose bound reads the enclosing iterator. The inner header retains that
read as the enclosing `GenvarRef`, so its trip list is derived per outer trip
after parameter binding. A nested loop's block shell therefore contains the
inner `For` directly; its `LocalDecl` is erased with the header declaration.
`symbolic_nested_parameter_for` differentially matches Icarus at `N = 5` and
the point cross-check covers `N = 3`, `5`, and `8`.

The loop boundary matrix also covers `N = 0`, `1`, `126`, and `127` on the
200-bit family, plus a nested iterator-shadowing source in both default and
`--retain-loops` forms. The four parameter rows exercise the structural fuel
edge around the former 128-trip boundary; the shadowing rows check that the
inner binding does not capture the outer iterator.

`symbolic_parameter_for_header_shapes` adds one differential row covering an
inclusive `<=` bound, a descending `>=` loop with `-=`, and a positive `+=`
stride at parameter point `N = 5`.

### Retaining literal loops

The extractor emits the same `For` node used by parameter-bound loops by
default. `extract.py --top T --retain-loops` remains a compatibility spelling;
no literal iteration cap is consulted by either path. Differential rows use
the retained source structure directly.

`Param2.forValues2` now derives structural fuel from the instantiated linear
comparison and step, including the final false-condition check. It therefore
does not impose a fixed trip-count cap on admitted monotone headers; malformed,
non-monotone, and non-reaching `!=` headers remain loud.

## L1. Block-local declarations

`always_comb begin logic [7:0] t; t = a ^ b; y = t & a; end` declares `t` in the block; the Lean loader has no `LocalDecl`
statement and refused the whole envelope. A STATIC block variable (the default for a procedure of a module) lives for the whole
simulation, is written only by its block and starts at x: exactly a module variable that only this process writes. The
declaration is hoisted to a module `Var` (`hoisted_local`) and every reference is renamed BY SYMBOL (`storage_name`, reached
through `_storage_name`), never by name, so a block-local `t` that shadows a module `t` is unambiguous. The new name is unique among
all names of the module (`<block label>__<name>`, `blk<k>__<name>` for an unnamed block, a trailing `_` on a clash). The same
declaration converted again by an unrolled loop body resolves to the same variable.

Closed initializers are now admitted when the converted initializer is a literal, an exact fill, or a closed parameter/enum value
that the declaration tier can materialize. The initializer remains on the hoisted module `Var`, so it runs once before the process,
with the same width and four-state conversion as a module declaration. Runtime reads, calls, timing, automatic variables, and
other effectful initializers remain loud. A type the module-level variable conversion does not take (`convert_var_sym`), a
multi-dimensional or unpacked variable, every block of a generate scope (the variable would be one per instance), and every
process other than a module-level `always_comb` / E1 block also remain refused.

Rows: `proc_local` (named and nested blocks, one shadowing a module variable, selects of a local, a local in an unrolled loop
body), `proc_local_initializer`, `proc_local_initializer_param` (a
parameter-point value), and `proc_local_param_n3/n4/n8`.

The same `--retain-proc-rewrites` mode keeps a block declaration as its
lexical `LocalDecl` envelope node and leaves references under the original
symbol name. `Ingest2` reports the frozen scoped-storage boundary as
`Unsupported` instead of hoisting the declaration into module storage; the
hoisting path remains the default.

## E1. `always @*` and level-sensitive event lists

IEEE 1800-2023 9.2.2.2.2 lists exactly three differences between `always_comb` and `always @*`: `always_comb` runs once at time
zero, is sensitive to the contents of the functions it calls, and forbids every other process to write its targets. R3, R4 and R6
below are those three; R1, R2 and R5 are the shape of the block. A block that satisfies all six computes, after every settle,
what `always_comb` computes, and becomes an `AlwaysComb` (`always_star_lowered` on the node). The forms: `@*`, `@(*)`, `@(a or b)`,
`@(a, b)`, `@a`. Edge terms (`posedge`/`negedge`, including mixed lists) are not decided here and keep their paths.

Every rule is decided on the CONVERTED body (unrolled loops, hoisted locals, inlined functions: what the Lean loader reads) and
on slang's own symbols. A failure keeps the process-level `Unsupported` with the tag it always had (`TimedStatement:ImplicitEventControl`,
`TimedStatement:EventListControl`, `SignalEventControl:None_`, so the register rows and the census count it) and names the rule in its
text. A body that already contains an `Unsupported` node is returned as the `AlwaysComb` with that node inside (the refusal is the inner
one, exactly as the same body of an `always_comb`).

| rule | statement |
|---|---|
| R1 | no edge term and no `iff` in the event control; the body is `Block`/`If`/`Case`/blocking assignments only (a nonblocking assignment, a delay, a system task, a nested event control is refused) |
| R2 | an explicit list names every signal the body reads, as a plain signal (a select or an expression in the list is refused); a signal that a COMPLETE earlier assignment of the body defines is not an input and need not be listed. The simulators wake on the list, Yosys synthesizes the function: a list that misses a read is a tools split |
| R3 | the body reads at least one signal it does not write, and every such signal is 4-state, integral and a module signal: an `@*` block does not run at time zero, so a block whose inputs are 2-state (driven to the initial value: no event) or reads nothing would leave its targets x in a simulator while the model computes them. A continuous time-zero driver is retained as the parser's `AlwaysEvent` node for the E source view; its startup ordering remains a scheduler boundary rather than a lowered `AlwaysComb` meaning. A source-shaped unpacked-array cell read is also retained as `AlwaysEvent`; the array remains structured and its E execution is a separate scheduler/storage boundary. |
| R4 | a called function reads no module signal it does not receive as an argument (Verilog-2001 `@*` does not wake on those reads, `always_comb` does); decided on slang's tree, transitively through the called functions |
| R5 | every target is assigned on every path (Yosys `proc` infers a latch SILENTLY for `@*`, where `always_comb` is an error), and no target, or window of one, is read before a complete assignment defines it. Coverage is by bit window for a target of literal width whose range is `[W-1:0]` (the windows an unrolled loop leaves), by whole assignment otherwise; an `if` covers what both arms cover, a `case` only with a `default` |
| R6 | no other process writes a target (slang's `MultipleAlwaysAssigns` does not fire for `@*`: slang's driver table is asked, `AnalysisManager.getDrivers`) and no target has a declaration initializer |

Recorded over-refusals: a `case` that covers every value without a `default`, a read of a partly written target through a non-literal
index, a target written in two processes on disjoint bits. A continuous driver
feeding an `@*` input is retained as `TimedStatement:ImplicitEventControl`
for E, with its source-shaped body and raw sensitivity. The clean-room
fixture `Examples/system-verilog/sem2/always_star_timezero_e/` records the
Icarus/Xcelium first-row split; E's `σ_src` receipt is not asserted as the
unique result while the time-zero registration order is still modelled.

Rows: `proc_star` (implicit, an explicit list, a single-event list, a `case` with a default, a temporary written first, a ripple chain
through the windows an unrolled loop wrote) and `proc_star_param_n3/n4/n8` (whole assignments at every width).

Under `--retain-proc-rewrites`, an event-controlled plain `always` remains an
`AlwaysEvent` envelope node with its event-control kind and body. `Ingest2`
reports the frozen event-list process boundary as Unsupported; the default E1
conversion to `AlwaysComb` remains unchanged.

## N2. Nets with one continuous driver

A net reads z where no driver drives it (IEEE 1800-2023 6.6) and resolves several drivers; the semantic tier stores variables, so
every net was refused (`NetSymbol:net-z`, `PortSymbol:net-z`). A plain `wire` whose every bit has EXACTLY ONE continuous driver,
without a drive strength or delay, has neither effect: the resolution of one driver is the identity and no bit is undriven. It is
declared as the variable the driver assigns (`Var`; an `output wire` or an implicit-type `output` is an `out` `Port`; both carry
`net_as_variable`). A net declaration assignment `wire [w] x = e;` is the driver `assign x = e;` (10.3.1), queued as an `Assign`
process at the declaration's position (`net_declaration_assign`), never as an initializer (the net's value before its first
evaluation). Implicit nets (`assign y = a;` with `y` undeclared) are 1-bit wires of the same kind.

The decision is made on slang's driver table (`AnalysisManager.getDrivers`) at the default point and holds at every point of a
parametric family because it is one of two point-independent shapes: (A) ONE driver that is the whole net by its source text (a
whole-net `assign`, a declaration assignment, an instance output connected to the whole net), whatever the width; (B) a net of
literal width whose drivers' source texts select literal windows that tile the net exactly. Refused with the old tags: no driver or a
partial cover (z), two drivers on a bit (resolution), a declaration assignment plus another driver, a driver inside a generate scope
(it may not exist at every point), windows of a net whose width is a parameter, a drive strength or delay, a net in a generate scope,
a net type other than `wire`, a 2-state or signed net.

Rows: `proc_net` (declaration assignment, whole assign, literal windows tiling an `output wire`, implicit-type outputs, a scalar net,
an implicit net, a child output connected to a whole net), `proc_net_param_n3/n4/n8`. The loud rows `net_width_outwire` and
`net_width_outwire1` (a NET formal fed by a narrower output net: the extractor's `"net": true` marker was always the intended guard)
and `acg_alias_wire` now reach the Lean guards; the undriven / partial / two-driver rows (`net_z_*`, `vg_initn`) are unchanged.

With `--retain-proc-rewrites`, a single-driver net that N2 would convert to a
variable remains a `Net` declaration with `net_rewrite_retained` metadata. The
loader preserves the net flag and keeps the unresolved net semantics loud; the
default one-driver conversion is unchanged.

Finding, closed by the follow-up (changelog, register row `st-cont-strength`): in symbolic mode `_continuous_assignment_has_strength`
reads source bytes that only the M0 path loads, so a strength on an `assign` was invisible: `assign (strong0, highz1) y = a;` on a `logic
y` was extracted as a plain assignment (Icarus 12 reads z where a = 1, Xcelium ignores the strength on a variable, Yosys cannot read it).
Every strength-qualified `assign` is refused now (`ContinuousAssignSymbol:strength`, from the syntax tree); N2 also refuses a net with
a strength.

## Regression recipe

```
git archive <base rev> extractors | tar -x -C /tmp/base
python3.12 harness/sv/regress_envelopes.py /tmp/base/extractors extractors . --jobs 4
```

Output: `envelopes N: identical I, extractor errors (same both) E, refusal moved M, ADMITTED CHANGED B`; exit status 1 iff B > 0.
The envelopes are the 455 committed symbolic `Examples/system-verilog/**/*.json` whose sources are present and the references and
tests of the svGolf tasks. A `moved` entry is a source that carried an `Unsupported` node before and now differs (the construct
being lowered); read each one.
