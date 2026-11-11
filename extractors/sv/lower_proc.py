"""WP-PROC (2026-11-01): the procedural and Verilog-2001 lowerings of the sv-0.2 symbolic tier.

The logic of the lowerings lives here; `extract.py` calls it through a few lines at the sites named below, in symbolic
mode only (`_SYM is not None`). Every function takes the extractor module as its first argument (`ex`: no import cycle,
and it is the very module object whose globals `_SYM`, `_COMPOUND_READ`, ... are live) and returns either the lowered
envelope node(s) or `None`, in which case the caller keeps the refusal it had: a lowering is trusted code and every
shape it does not state exactly stays the loud `Unsupported` node (docs/sv-proc-lowering.md, "refuse when in doubt").

  C1  compound assignment `x op= e` and its read of the target     -> compound_assignment
  X1  loop headers the off-prem unroll refuses: an iterator declared outside the header, `i += c`,
      `<=` / `>=` bounds, and the erasure of the iterator's dead declaration
                                                                      -> loop_header, compound_step,
                                                                         erased_iterator
  L1  block-local declarations of an `always_comb` body: hoisted to module-level variables
                                                                      -> begin_module, always_comb_body,
                                                                         hoist_local, storage_name,
                                                                         hoisted_decls
  E1  `always @*`, `always @(a or b)`, `always @(a, b)`, `always @a` as `always_comb` under the rules R1 to R6
                                                                      -> star_block
  N2  a `wire` / `output wire` / implicit net that has exactly one continuous driver on every bit is a variable
                                                                      -> net_driver_reason, net_variable,
                                                                         take_pending
  ...

The design, the evidence and the plan are in svgolf/design/real-world-sv/PROC-NOTE.md.
"""

# `x op= e` is `x = x op e` (IEEE 1800-2023 11.4.1) with the target's selectors evaluated ONCE; the operators of the M0 path
_COMPOUND_OPS = ("+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "<<<", ">>>")


def _contains_unsupported(node):
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            if n.get("kind") == "Unsupported":
                return True
            stack.extend(n.values())
        elif isinstance(n, list):
            stack.extend(n)
    return False


def compound_assignment(ex, sm, expression, span_node=None):
    """C1. `x op= e` as the blocking assignment `x = x op e` of the symbolic tier.

    slang binds the statement as `x = (<lvalue reference> op e)`: the right-hand side is the converted
    expression with the placeholder `LValueReferenceExpression` where the target is read, and
    `_convert_selected_leaf` puts the converted READ of the target there (`ex._COMPOUND_READ`), so the operand
    widths, the signedness and the context sizing are exactly slang's. The lowering is exact when the target and
    the right-hand side are source-pure (no call, increment or other effect): then reading the target's selectors
    twice (once for the read, once for the write) is reading them once. Anything else (an effectful selector or
    right-hand side, a target the tier does not take, a nonblocking or timed assignment, an unlisted operator)
    returns `None` and the statement stays `AssignmentExpression:compound`."""
    if ex._SYM is None or expression.isNonBlocking or expression.timingControl is not None:
        return None
    if ex.BINARY_OPS.get(expression.op) not in _COMPOUND_OPS:
        return None
    lhs = expression.left
    if getattr(ex, "_sym_runtime_unpacked_lhs", lambda _: False)(lhs):
        return None
    references = []
    ex._visit_selected_expression(
        expression.right,
        lambda node: references.append(node) if type(node).__name__ == "LValueReferenceExpression" else None)
    if len(references) != 1:
        return None
    if not (ex._case_source_expression_ok(lhs)
            and ex._case_source_expression_ok(ex._compound_rhs(expression.right))):
        return None
    target, ok = ex.select_target(sm, lhs)
    if not ok or _contains_unsupported(target):
        return None
    value = ex._compound_value(sm, expression, target)
    if value is None or value.get("kind") == "Unsupported" or ex.width_of(value) != ex.width_of(target):
        return None
    return {"kind": "BlockingAssign", "span": ex.node_span(sm, span_node or expression), "target": target,
            "value": value, "symbolic_compound_lowered": True}


# ---------------------------------------------------------------------------------------------------------------
# X1. loop headers
# ---------------------------------------------------------------------------------------------------------------
#
# Master's `_sym_for_values` unrolls a source-pure `for` whose header declares ONE `int` iterator with a literal
# initializer, compares it with a literal and steps it by a literal (7f7c1e02). Real Verilog-2001 code declares the
# iterator OUTSIDE the header (`integer i; ... for (i = 0; i < 8; i = i + 1)`), steps it with `i += 1`, and uses `<=` and
# `>=`. These are the same loops. What is different is that the iterator is then a VARIABLE of the module (or of the
# block): the unrolled body binds it to an `Int` per iteration (`_SymLoopBinding`), so the variable itself is never
# written. That is exact only if nothing else can observe the variable: every reference to it must lie inside a loop
# that iterates it (a read after the loop sees the loop's final value, which the unroll does not compute; a read
# before it sees x). `_iterator_census` checks exactly that and, when it holds, the iterator's declaration is dead and
# erased (`erased_iterator`); otherwise the header is refused and the loop keeps its loud `ForLoopStatement`.

_CENSUS = {}


def _strip(node):
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return None
    return node


def _init_form(ex, statement):
    """(symbol, initial) of an init-form header `for (i = <literal>; ...)`, structure only, or None."""
    if list(getattr(statement, "loopVars", ())):
        return None
    inits = list(getattr(statement, "initializers", ()))
    if len(inits) != 1:
        return None
    init = inits[0]
    if (type(init).__name__ != "AssignmentExpression" or init.op is not None or init.isNonBlocking
            or init.timingControl is not None):
        return None
    left = _strip(init.left)
    if left is None or type(left).__name__ != "NamedValueExpression":
        return None
    symbol = left.symbol
    if str(symbol.kind).split(".")[-1] != "Variable":
        return None
    initial = ex._literal_integral_value(init.right)
    if initial is None:
        return None
    return symbol, initial


def _int_iterator(symbol):
    """`int` / `integer`: the only iterator types whose 32-bit signed trace master's unroll computes (a `byte` or a
    `logic [7:0]` iterator wraps at another point)."""
    try:
        t = symbol.type
        return (t.bitWidth == 32 and bool(t.isSigned)
                and type(t.canonicalType).__name__ == "PredefinedIntegerType")
    except Exception:
        return False


def _iterator_census(ex, symbol):
    """Whether every reference to `symbol` in the module lies inside an init-form `for` that iterates it, and the
    symbol is not a port. Cached per symbol."""
    key = id(symbol)
    hit = _CENSUS.get(key)
    if hit is not None and hit[0] is symbol:
        return hit[1]
    ok = False
    try:
        scope = ex._SYM.scope
        if (scope is not None and _int_iterator(symbol)
                and not any(str(m.kind).split(".")[-1] == "Port" and m.name == symbol.name for m in scope)):
            extents = []          # (start, end) offsets of every init-form loop on this symbol
            refs = []             # offsets of every reference
            def visit(node):
                kind = type(node).__name__
                if kind == "ForLoopStatement":
                    form = _init_form(ex, node)
                    if form is not None and form[0] is symbol:
                        r = node.sourceRange
                        extents.append((r.start.offset, r.end.offset))
                elif kind in ("NamedValueExpression", "HierarchicalValueExpression"):
                    if getattr(node, "symbol", None) is symbol:
                        refs.append(node.sourceRange.start.offset)
            scope.visit(visit)
            ok = bool(extents) and all(any(a <= o < b for a, b in extents) for o in refs)
    except Exception:
        ok = False
    _CENSUS[key] = (symbol, ok)
    return ok


def loop_header(ex, statement):
    """X1. `(symbol, initial)` of a counted `for` header, or `None` (the loop stays loud).

    The declared form (`for (int i = 0; ...)`, one `loopVars` entry) is master's and is returned unchanged; the init
    form is admitted only when the iterator is dead outside its loops (`_iterator_census`)."""
    loop_vars = list(getattr(statement, "loopVars", ()))
    if loop_vars:
        if len(loop_vars) != 1 or list(getattr(statement, "initializers", ())):
            return None
        symbol = loop_vars[0]
        initial = ex._literal_integral_value(getattr(symbol, "initializer", None))
        return None if initial is None else (symbol, initial)
    form = _init_form(ex, statement)
    if form is None or not _iterator_census(ex, form[0]):
        return None
    return form


def compound_step(ex, step, symbol):
    """X1. The literal step of `i += c` / `i -= c` (c > 0), else `None`."""
    if not ex._sym_same_symbol(getattr(step, "left", None), symbol):
        return None
    # slang binds `i += c` as `i = (<lvalue reference> + c)`: the user's operand is what `_compound_rhs` peels out
    amount = ex._literal_integral_value(ex._compound_rhs(getattr(step, "right", None)))
    if amount is None or amount <= 0:
        return None
    op = str(getattr(step, "op", "")).split(".")[-1]
    if op in ("Add", "Plus"):
        return amount
    if op in ("Subtract", "Minus"):
        return -amount
    return None


def erased_iterator(ex, symbol):
    """X1. Whether the declaration of `symbol` is the dead declaration of an unrolled loop iterator (module-level
    `integer i;` or a block-local one) and is therefore erased."""
    try:
        if str(symbol.kind).split(".")[-1] != "Variable" or getattr(symbol, "initializer", None) is not None:
            return False
    except Exception:
        return False
    return _iterator_census(ex, symbol)


# ---------------------------------------------------------------------------------------------------------------
# L1. block-local declarations
# ---------------------------------------------------------------------------------------------------------------
#
# `always_comb begin logic [7:0] t; t = a ^ b; y = t & a; end` declares `t` in the block; the Lean loader has no
# `LocalDecl` statement and refused the whole envelope. A STATIC block variable (the default for a procedure of a
# module) lives for the whole simulation, is written only by its block and starts at x: exactly a module variable that
# only this process writes, so the declaration is hoisted to the module and every reference is renamed. The rename is
# BY SYMBOL (`storage_name`, reached through `_storage_name`), never by name, so a block-local `t` that shadows a module
# `t` is unambiguous; the new name is unique among all module names (`<block label>__<name>`, `blk<k>__<name>` for an
# unnamed block, a trailing `_` on a clash). Refused (the `LocalDecl` stays, loud): a runtime or effectful declaration
# initializer (a static initializer runs once at time 0, an automatic one at each entry), an automatic variable (it is x again at each entry;
# the hoisted variable would hold its previous value), a type the module-level variable conversion does not take
# (`convert_var_sym`), a multi-dimensional or unpacked variable (their selects are built from the symbol's own name),
# and every block of a generate scope (the variable would be one per instance).

_MODULES = []        # stack of per-module states


class _ModuleState:
    def __init__(self, used):
        self.decls = []          # hoisted `Var` nodes, in hoisting order
        self.bound = {}          # id(symbol) -> (symbol, hoisted name)
        self.used = used         # every name in the module, hoisted ones included
        self.region = 0          # index of the always_comb region being converted (1-based, module order)
        self.active = False      # converting the body of a module-level always_comb
        self.pending = []        # processes a declaration queued (N2: the assignment of a net declaration assignment)


def begin_module(ex, body):
    """Open the state of one module conversion (`convert_module_sym`)."""
    _MODULES.append(_ModuleState({m.name for m in body if m.name}))


def hoisted_decls():
    """Close the state of the module conversion and return the hoisted `Var` declarations."""
    return _MODULES.pop().decls if _MODULES else []


def always_comb_body(ex, sm, m, module_level):
    """The converted body of an `always_comb` (the hook of `convert_procedural_block`): a module-level block converts its
    declarations through `hoist_local`; any other block converts exactly as before."""
    return _convert_body(ex, sm, m.body, module_level)


def _convert_body(ex, sm, stmt, module_level):
    state = _MODULES[-1] if _MODULES else None
    if state is None or not module_level:
        return ex.convert_stmt(sm, stmt)
    state.region += 1
    state.active = True
    try:
        return ex.convert_stmt(sm, stmt)
    finally:
        state.active = False


def storage_name(symbol):
    """The name a reference to `symbol` has in the envelope: the hoisted name of a hoisted local, else its own."""
    for state in reversed(_MODULES):
        hit = state.bound.get(id(symbol))
        if hit is not None and hit[0] is symbol:
            return hit[1]
    return symbol.name


def _hoisted_name(state, symbol):
    parts = [q for q in str(symbol.hierarchicalPath).split(".")[1:-1] if q]
    base = ("__".join(parts) if parts else "blk%d" % state.region) + "__" + symbol.name
    name = base
    while name in state.used:
        name += "_"
    return name


def hoist_local(ex, sm, stmt):
    """L1. The statement that replaces the declaration `stmt` of a block-local variable, or `None` (the declaration is
    converted as before and stays a loud `LocalDecl`)."""
    state = _MODULES[-1] if _MODULES else None
    if state is None or not state.active:
        return None
    symbol = stmt.symbol
    hit = state.bound.get(id(symbol))
    if hit is not None and hit[0] is symbol:           # the body of an unrolled loop converts the declaration again
        return {"kind": "Empty", "span": ex.node_span(sm, stmt), "symbolic_local_hoisted": hit[1]}
    initializer = getattr(symbol, "initializer", None)
    if initializer is not None and not ex._case_source_expression_ok(
            initializer, packed_members=True):
        return None
    if str(symbol.lifetime).split(".")[-1] != "Static":
        return None
    try:
        ct = symbol.type.canonicalType
        if type(ct).__name__ == "PackedArrayType":
            if type(ct.elementType.canonicalType).__name__ != "ScalarType":
                return None
        elif type(ct).__name__ not in ("ScalarType", "PredefinedIntegerType"):
            return None
    except Exception:
        return None
    node = ex.convert_var_sym(sm, symbol)
    if not isinstance(node, dict) or node.get("kind") != "Var" or _contains_unsupported(node):
        return None
    # Param2's declaration path evaluates only closed initial values.  Keep
    # this lowering aligned with that boundary: known literals become `Int`,
    # fixed-width x/z values remain `Literal`, an unbased fill is exact at
    # every parameter point, and a parameter/enum reference is materialized
    # by the point instantiator. A converted signal read or effectful
    # expression would otherwise leave a hoisted declaration that the loader
    # rejects later, losing the useful LocalDecl refusal at the source boundary.
    if initializer is not None:
        init = node.get("init")
        if not isinstance(init, dict) or init.get("kind") not in (
                "Int", "Literal", "Fill", "ParamRef", "EnumRef"):
            return None
        if ex._case_expression_ok(init) is False:
            return None
    name = _hoisted_name(state, symbol)
    node = dict(node)
    node["name"] = name
    node["hoisted_local"] = True
    state.used.add(name)
    state.bound[id(symbol)] = (symbol, name)
    state.decls.append(node)
    return {"kind": "Empty", "span": ex.node_span(sm, stmt), "symbolic_local_hoisted": name}


# ---------------------------------------------------------------------------------------------------------------
# E1. `always @*` and level-sensitive event lists
# ---------------------------------------------------------------------------------------------------------------
#
# IEEE 1800-2023 9.2.2.2.2 lists exactly three differences between `always_comb` and `always @*`: `always_comb`
# runs once at time zero, is sensitive to the contents of the functions it calls, and forbids every other process to
# write its targets. The three rules R3, R4 and R6 below are those; R1, R2 and R5 are the shape of the block. A block
# that satisfies all six computes, after every settle, what `always_comb` computes, and is converted as an
# `AlwaysComb`. Every rule is decided on the CONVERTED body (what the Lean loader reads: unrolled loops, inlined
# functions, hoisted locals) and on slang's own symbols, and a failure keeps the process-level `Unsupported` it always
# had (same `sv_kind`, so the register row and the census still count it), with the rule in its text.
#
#   R1  no edge term and no `iff` in the event control; the body is `Block`/`If`/`Case`/blocking assignments only (no
#       nonblocking assignment, no delay or event control, which the converter refuses anyway).
#   R2  an explicit list names every signal the body reads (a signal that a COMPLETE earlier assignment of the body
#       defines is not an input and need not be listed); a select or an expression in the list is refused. The
#       simulators wake on the list, Yosys synthesizes the function: a list that misses a read is a tools split.
#   R3  the body reads at least one signal it does not write, and every such signal is 4-state: an `@*` block does
#       not run at time zero, so a block whose inputs can never change (or are 2-state and driven to their initial
#       value, which is no event) would leave its targets x in a simulator while the model computes them.
#   R4  a called function reads no module signal it does not receive as an argument (Verilog-2001 `@*` does not wake
#       on those reads, `always_comb` does).
#   R5  every target is assigned on every path (no latch: Yosys `proc` infers one silently for `@*`), and no target
#       (or window of one) is read before a complete assignment defines it. Coverage is by bit window for a target of
#       fixed width whose range is `[W-1:0]`, by whole assignment otherwise; a `case` covers only with a `default`.
#   R6  no other process writes a target, and no target has a declaration initializer (slang's MultipleAlwaysAssigns
#       does not fire for `@*`; slang's own driver table is asked).
#
# Over-refusals are recorded in docs/sv-proc-lowering.md; a residue is recorded there too: an input that is driven
# only at time zero and never changes again.

_STAR_STMTS = ("Block", "If", "Case", "BlockingAssign", "Empty")


def _star_events(ex, body):
    """`(sv_kind, form, listed names, reason)` of the event control of a `TimedStatement` the star lowering takes a
    decision on, or `None` for every other control (edge terms stay on the sequential paths). `reason` is a refusal."""
    timing = body.timing
    kind = type(timing).__name__
    if kind == "ImplicitEventControl":
        return "TimedStatement:ImplicitEventControl", "implicit", [], None
    if kind == "EventListControl":
        events, tag = list(timing.events), "TimedStatement:EventListControl"
    elif kind == "SignalEventControl":
        events, tag = [timing], "SignalEventControl:None_"
    else:
        return None
    if not events or any(type(e).__name__ != "SignalEventControl" or e.edge != ex.EdgeKind.None_ for e in events):
        return None
    names = []
    for e in events:
        if e.iffCondition is not None:
            return tag, "list", names, "R1: an `iff` condition in the event list"
        expr = e.expr
        if type(expr).__name__ != "NamedValueExpression" or str(expr.symbol.kind).split(".")[-1] not in ("Variable", "Net"):
            return tag, "list", names, "R2: an event-list entry that is not a plain signal (a select or an expression)"
        names.append(storage_name(expr.symbol))
    return tag, "list", names, None


def _node_kinds(node):
    found = set()
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            if "kind" in n:
                found.add(n["kind"])
            stack.extend(n.values())
        elif isinstance(n, list):
            stack.extend(n)
    return found


def _const_int(node):
    """The value of a literal-only index expression (an unrolled loop leaves `0 + 1` unfolded), else `None`."""
    if not isinstance(node, dict):
        return None
    k = node.get("kind")
    if k == "Int":
        return node.get("value")
    if k == "Binary" and node.get("op") in ("+", "-", "*"):
        a, b = _const_int(node.get("left")), _const_int(node.get("right"))
        if a is None or b is None:
            return None
        return a + b if node["op"] == "+" else a - b if node["op"] == "-" else a * b
    return None


class _Info:
    """What the rules need to know about one name of the body."""

    def __init__(self, ex, sm, symbol):
        self.symbol = symbol
        self.kind = str(symbol.kind).split(".")[-1]
        self.hoisted = any(s.bound.get(id(symbol), (None,))[0] is symbol for s in _MODULES)
        self.width, self.fixed, self.win_ok = None, False, False
        try:
            t = symbol.type
            self.fourstate = bool(t.isFourState)
            self.integral = bool(t.isIntegral)
            dtype, _reason = ex._dtype_sym(sm, t, ex._decl_type_syntax(symbol))
        except Exception:
            self.fourstate, self.integral, dtype = False, False, None
        if isinstance(dtype, dict) and dtype.get("kind") == "PackedType" and ex._sym_dtype_fixed(dtype):
            width = dtype.get("resolved")
            if isinstance(width, int) and width > 0:
                self.width, self.fixed = width, True
                packed = dtype["packed"]
                self.win_ok = (len(packed) == 1 and packed[0]["msb"].get("value") == width - 1
                               and packed[0]["lsb"].get("value") == 0)
        self.full = ((1 << self.width) - 1) if self.fixed else -1


class _Star:
    """The decision state of one block: names, coverage flow, reads."""

    def __init__(self, ex, sm, listed, form):
        self.ex, self.sm, self.listed, self.form = ex, sm, listed, form
        self.symbols = {}        # storage name -> symbol
        self.infos = {}
        self.writes = set()
        self.ext = []            # names read and not written (the inputs), first-read order
        self.why = None

    def info(self, name):
        hit = self.infos.get(name)
        if hit is None:
            hit = self.infos[name] = _Info(self.ex, self.sm, self.symbols[name])
        return hit

    def fail(self, why):
        if self.why is None:
            self.why = why

    # window of a read/write selection: a bit mask in the declaration's coordinates, or None (not a literal window)
    def window(self, node, info):
        if not info.win_ok:
            return None
        k = node["kind"]
        if k == "BitSel":
            idx = _const_int(node["index"])
            if idx is not None and 0 <= idx < info.width:
                return 1 << idx
        elif k == "PartSel":
            hi, lo = _const_int(node["msb"]), _const_int(node["lsb"])
            if hi is not None and lo is not None and 0 <= lo <= hi < info.width:
                return ((1 << (hi - lo + 1)) - 1) << lo
        elif k == "ArraySel" and node.get("part") is None and len(node.get("indices") or ()) == 1:
            idx = _const_int(node["indices"][0])
            if idx is not None and 0 <= idx < info.width:
                return 1 << idx
        return None

    def need(self, name, mask, cov):
        """A read of `name` (window `mask`, `None` = whole): checked against the coverage `cov`."""
        info = self.info(name)
        if name in self.writes:
            required = info.full if mask is None else mask
            if (cov.get(name, 0) & required) != required:
                self.fail("R5: `%s` is read before every bit read is assigned" % name)
        elif name not in self.ext:
            self.ext.append(name)

    def reads(self, node, cov):
        if isinstance(node, list):
            for n in node:
                self.reads(n, cov)
            return
        if not isinstance(node, dict):
            return
        k = node.get("kind")
        if k == "Ident":
            name = node.get("name")
            if name not in self.symbols:
                self.fail("R5: the name `%s` is not a signal of the module" % name)
            else:
                self.need(name, None, cov)
            return
        if k in ("BitSel", "PartSel") and isinstance(node.get("value"), dict) and node["value"].get("kind") == "Ident":
            name = node["value"].get("name")
            if name not in self.symbols:
                self.fail("R5: the name `%s` is not a signal of the module" % name)
            else:
                self.need(name, self.window(node, self.info(name)), cov)
            for key in ("index", "msb", "lsb"):
                self.reads(node.get(key), cov)
            return
        if k == "ArraySel":
            name = node.get("name")
            if name not in self.symbols:
                self.fail("R5: the name `%s` is not a signal of the module" % name)
            else:
                self.need(name, self.window(node, self.info(name)), cov)
            self.reads(node.get("indices"), cov)
            self.reads(node.get("part"), cov)
            return
        for key, value in node.items():
            if key != "span":
                self.reads(value, cov)

    def target(self, node):
        """`(name, mask or None)` of a blocking-assignment target: whole (`mask` is `-1`), a literal window, or a
        dynamic select (`None`); the selectors of the target are returned too, for the reads."""
        k = node.get("kind")
        if k == "Ident":
            return node.get("name"), -1, []
        if k in ("BitSel", "PartSel") and isinstance(node.get("value"), dict) and node["value"].get("kind") == "Ident":
            name = node["value"].get("name")
            if name not in self.symbols:
                return None
            mask = self.window(node, self.info(name))
            return name, mask, [node.get(key) for key in ("index", "msb", "lsb")]
        if k == "ArraySel":
            name = node.get("name")
            if name not in self.symbols:
                return None
            return name, self.window(node, self.info(name)), [node.get("indices"), node.get("part")]
        return None

    def collect_writes(self, stmt):
        k = stmt.get("kind") if isinstance(stmt, dict) else None
        if k not in _STAR_STMTS:
            self.fail("R1: a `%s` statement in the body" % k)
            return
        if k == "Block":
            for s in stmt["stmts"]:
                self.collect_writes(s)
        elif k == "If":
            self.collect_writes(stmt["then"])
            if stmt.get("else") is not None:
                self.collect_writes(stmt["else"])
        elif k == "Case":
            for item in stmt["items"]:
                self.collect_writes(item["body"])
            if stmt.get("default") is not None:
                self.collect_writes(stmt["default"])
        elif k == "BlockingAssign":
            t = self.target(stmt["target"])
            if t is None:
                self.fail("R5: an assignment target the lowering does not take")
            else:
                self.writes.add(t[0])

    def flow(self, stmt, cov):
        k = stmt["kind"]
        if k == "Empty":
            return cov
        if k == "Block":
            for s in stmt["stmts"]:
                cov = self.flow(s, cov)
            return cov
        if k == "If":
            self.reads(stmt["cond"], cov)
            then = self.flow(stmt["then"], cov)
            other = self.flow(stmt["else"], cov) if stmt.get("else") is not None else cov
            return {n: then.get(n, 0) & other.get(n, 0) for n in set(then) | set(other)}
        if k == "Case":
            self.reads(stmt["subject"], cov)
            arms = []
            for item in stmt["items"]:
                self.reads(item["patterns"], cov)
                arms.append(self.flow(item["body"], cov))
            arms.append(self.flow(stmt["default"], cov) if stmt.get("default") is not None else cov)
            names = set().union(*arms)
            return {n: _and_all(a.get(n, 0) for a in arms) for n in names}
        # BlockingAssign: the value is read before the target is written
        self.reads(stmt["value"], cov)
        name, mask, selectors = self.target(stmt["target"])
        self.reads(selectors, cov)
        info = self.info(name)
        out = dict(cov)
        if mask == -1:
            out[name] = info.full
        elif mask is not None:
            out[name] = cov.get(name, 0) | mask
        return out


def _and_all(values):
    out = -1
    for v in values:
        out &= v
    return out


def _inside(loc, rng):
    try:
        return loc.buffer == rng.start.buffer and rng.start.offset <= loc.offset < rng.end.offset
    except Exception:
        return False


def _function_reads_module_signal(ex, body):
    """R4. The first module signal read by a function a call of `body` reaches (a user subroutine, transitively) that
    the function neither declares nor receives as an argument, else `None`."""
    seen = set()
    hits = []

    def scan(sub):
        if id(sub) in seen or hits:
            return
        seen.add(id(sub))
        rng = sub.syntax.sourceRange

        def visit(node):
            n = type(node).__name__
            if n == "NamedValueExpression":
                if str(node.symbol.kind).split(".")[-1] in ("Variable", "Net") and not _inside(node.symbol.location, rng):
                    hits.append(node.symbol.name)
            elif n == "CallExpression" and not node.isSystemCall:
                scan(node.subroutine)
        sub.body.visit(visit)

    def top(node):
        if type(node).__name__ == "CallExpression" and not node.isSystemCall:
            scan(node.subroutine)
    body.visit(top)
    return hits[0] if hits else None


_ANALYSES = {}


def _drivers(ex, symbol):
    comp = ex._SYM.comp
    hit = _ANALYSES.get(id(comp))
    if hit is None or hit[0] is not comp:
        from pyslang.analysis import AnalysisManager
        comp.getAllDiagnostics()
        manager = AnalysisManager()
        manager.analyze(comp)
        hit = _ANALYSES[id(comp)] = (comp, manager)
    return hit[1].getDrivers(symbol)


def _instance_driver_target(owner, symbol):
    """Return the source target of an instance output driver for ``symbol``.

    Slang reports an output port connection as a ``ValueDriver`` owned by the
    instance, with the actual target in an ``AssignmentExpression``.  Keep
    this check tied to that connection instead of admitting arbitrary
    parameter-dependent driver text: the hierarchy route must retain the
    instance node and its source-shaped port target.
    """
    try:
        for pc in owner.portConnections:
            port = getattr(pc, "port", None)
            if str(getattr(port, "direction", "")).split(".")[-1] != "Out":
                continue
            expr = getattr(pc, "expression", None)
            if type(expr).__name__ != "AssignmentExpression":
                continue
            left = getattr(expr, "left", None)
            root = getattr(left, "symbol", None)
            if root is None:
                root = getattr(getattr(left, "value", None), "symbol", None)
            if root is symbol:
                return left
    except Exception:
        return None
    return None


def _star_rules(ex, sm, m, converted, listed, form):
    """The reason (text) this block cannot be an `always_comb`, or `None` when R1 to R6 hold."""
    star = _Star(ex, sm, listed, form)
    stmt = m.body.stmt
    clash = []

    def names(node):
        n = type(node).__name__
        if n == "NamedValueExpression":
            symbol = node.symbol
            if str(symbol.kind).split(".")[-1] in ("Variable", "Net"):
                name = storage_name(symbol)
                if star.symbols.setdefault(name, symbol) is not symbol:
                    clash.append(name)
        elif n == "HierarchicalValueExpression":
            clash.append("hierarchical reference")
    stmt.visit(names)
    if clash:
        return "R5: a hierarchical reference or two signals of one name (%s)" % clash[0]
    star.collect_writes(converted)
    if star.why:
        return star.why
    cov = star.flow(converted, {})
    if star.why:
        return star.why
    for name in sorted(star.writes):
        if cov.get(name, 0) != star.info(name).full:
            return "R5: `%s` is not assigned on every path (an `if` without `else`, a `case` without `default`, " \
                   "or a partly assigned window): `always @*` would infer a latch" % name
    # R3
    if not star.ext:
        return "R3: the body reads no signal it does not write: an `@*` block would not run at time zero"
    for name in star.ext:
        info = star.info(name)
        if info.kind not in ("Variable", "Net") or info.hoisted or not info.integral:
            return "R3: `%s` is not a module signal of integral type" % name
        if not info.fourstate:
            return ("R3: `%s` is a 2-state signal: driven to its initial value it produces no event, so an `@*` "
                    "block would not run at time zero (always_comb does)" % name)
        # §9.2.2.2.2 does not run an `always @*` body at time zero.  A
        # signal whose only source is a continuous driver can therefore race:
        # the driver and the level-sensitive block are both scheduled at
        # time zero, and the block may miss the one transition entirely.
        # Keep this source-shaped boundary loud until the event scheduler
        # models that initial active-region ordering.
        for driver in _drivers(ex, info.symbol):
            owner = driver.containingSymbol
            if type(owner).__name__ == "ContinuousAssignSymbol":
                return ("R3: `%s` has a continuous time-zero driver; `always @*` does not run at time zero "
                        "and its first wake-up is scheduler-dependent (always_comb does)" % name)
    # R2
    if form == "list":
        for name in star.ext:
            if name not in listed:
                return "R2: the event list does not name `%s`, which the body reads" % name
    # R4
    called = _function_reads_module_signal(ex, stmt)
    if called is not None:
        return ("R4: a called function reads the module signal `%s` without receiving it as an argument "
                "(`@*` does not wake on it, always_comb does)" % called)
    # R6
    here = m.location
    for name in sorted(star.writes):
        info = star.info(name)
        if info.hoisted:
            continue
        if info.kind != "Variable":
            return "R6: the target `%s` is not a variable" % name
        for driver in _drivers(ex, info.symbol):
            owner = driver.containingSymbol
            if type(owner).__name__ != "ProceduralBlockSymbol" or owner.location != here:
                return "R6: `%s` is also written by another process or a declaration initializer" % name
    return None


def star_block(ex, sm, m, module_level):
    """E1. The `AlwaysComb` node of a level-sensitive `always` block (`@*`, `@(*)`, `@(a or b)`, `@(a, b)`, `@a`)
    when R1 to R6 hold, the process-level `Unsupported` (its `sv_kind` unchanged, the failing rule in its text) when
    one fails, `None` for every block the star lowering does not decide (edge terms, other timing, no timing)."""
    body = m.body
    if ex._SYM is None or type(body).__name__ != "TimedStatement":
        return None
    shape = _star_events(ex, body)
    if shape is None:
        return None
    tag, form, listed, reason = shape

    def refuse(why):
        return ex.unsupported(sm, m, tag, ("always @%s: %s -- %s" % ("*" if form == "implicit" else "(list)", why,
                                                                   ex.source_text(m)))[:ex.UNSUPPORTED_TEXT_LIMIT])
    if reason is not None:
        return refuse(reason)
    written = ex._sym_proc_initialized_write(body.stmt)
    if written is not None:
        return refuse("R6: the body writes `%s`, which has a declaration initializer" % written[1])
    converted = _convert_body(ex, sm, body.stmt, module_level)
    node = {"kind": "AlwaysComb", "span": ex.sym_span(sm, m), "body": converted, "always_star_lowered": form}
    if _node_kinds(converted) & {"Unsupported", "LocalDecl"}:
        return node                 # refused inside, exactly as the same body of an always_comb would be
    try:
        why = _star_rules(ex, sm, m, converted, listed, form)
    except Exception as exc:        # noqa: BLE001  (fail closed)
        why = "the rules could not be decided (%s: %s)" % (type(exc).__name__, str(exc)[:120])
    return refuse(why) if why else node


# ---------------------------------------------------------------------------------------------------------------
# N2. nets with exactly one continuous driver per bit
# ---------------------------------------------------------------------------------------------------------------
#
# A net reads z where no driver drives it (IEEE 1800-2023 6.6) and resolves several drivers; the semantic tier stores
# variables, so every net was refused (`NetSymbol:net-z`, `PortSymbol:net-z`). A plain `wire` whose every bit has
# EXACTLY ONE continuous driver, and no strength, delay or other net type on it, has neither effect: resolution of one
# driver is the identity and no bit is undriven, so the net is the variable the driver assigns, and it is declared as
# one (`Var`; an `output wire` is an `out` `Port`). A net declaration assignment `wire [w] x = e;` is the driver
# `assign x = e;` (IEEE 1800-2023 10.3.1), queued as an `Assign` at the declaration's position, never an initializer
# (which would be the net's value before the first evaluation). The decision is made on slang's own driver table
# (`AnalysisManager.getDrivers`), at the default point, and holds at every point of a parametric family because it is
# one of two point-independent shapes: (A) one driver that is the WHOLE net by its source text (a whole-net `assign`,
# a declaration assignment, an instance output connected to the whole net), whatever the width; (B) a net of literal
# width whose drivers' source texts select literal windows, which tile the net exactly. Everything else is refused
# with today's tag: no driver or a partial cover (z), two drivers on a bit (resolution), a driver inside a generate
# scope (it may not exist at every point), an explicit drive strength, a net in a generate scope, a net type other
# than `wire`, a 2-state or signed net.

import os
import re


def _driver_source_text(ex, sm, rng):
    """Return a driver's source spelling using slang's byte offsets.

    ``SourceManager.getSourceText`` returns decoded Unicode, while slang's
    ``SourceLocation.offset`` is a byte offset.  Slicing the decoded string
    therefore shifts the range after any non-ASCII source character.  The
    symbolic context already retains the original UTF-8 bytes for every
    source, so decode the byte slice only after applying the offsets.
    """
    try:
        # ``getSourceText`` is decoded, but re-encoding it restores the byte
        # indexing contract for valid UTF-8 source files.
        data = sm.getSourceText(rng.start.buffer).encode("utf-8")
        start, end = rng.start.offset, rng.end.offset
        if 0 <= start <= end <= len(data):
            return data[start:end].decode("utf-8", errors="replace").strip()
    except Exception:
        pass
    try:
        sym = ex._SYM
        fname = os.path.normpath(sym.sm.getFileName(rng.start))
        data = sym.source_map.get(fname)
        if data is not None:
            start, end = rng.start.offset, rng.end.offset
            if 0 <= start <= end <= len(data):
                return data[start:end].decode("utf-8", errors="replace").strip()
    except Exception:
        pass
    return ""

_NET_OWNERS = ("ContinuousAssignSymbol", "InstanceSymbol")


def has_strength(assign):
    """Whether the continuous assignment symbol was written with `(strength0, strength1)`. (The extractor's own
    `_continuous_assignment_has_strength` reads the source bytes the symbolic mode does not load: the syntax tree is
    the source of truth here. `convert_continuous_assign` refuses every such assignment in symbolic mode.)"""
    parent = getattr(getattr(assign, "syntax", None), "parent", None)
    return getattr(parent, "strength", None) is not None


def net_driver_reason(ex, sm, symbol, dtype):
    """`None` when the net `symbol` (a module-level `wire`, or the internal net of an `output` port) can be declared as a
    variable, else the reason (text) it cannot."""
    if ex._SYM is None:
        return "not a symbolic extraction"
    try:
        if str(symbol.netType.netKind).split(".")[-1] != "Wire":
            return "net type"
        if getattr(symbol, "delay", None) is not None:
            return "delay"
        if getattr(getattr(getattr(symbol, "syntax", None), "parent", None), "strength", None) is not None:
            return "a net declaration with a drive strength"
        t = symbol.type
        if not t.isFourState or not t.isIntegral:
            return "2-state or non-integral net"
        if not (isinstance(dtype, dict) and dtype.get("kind") == "PackedType" and dtype.get("packed") is not None):
            return "unrecovered dimensions"
        scope = ex._SYM.scope
        members = list(scope)
        nets_here = {m.location for m in members if str(m.kind).split(".")[-1] == "Net"}
        if symbol.location not in nets_here:
            return "net in a generate scope"
        drivers_here = {m.location for m in members if str(m.kind).split(".")[-1] in ("ContinuousAssign", "Instance")}
        width = int(t.bitWidth)
        records = list(_drivers(ex, symbol))
        if symbol.initializer is not None:
            return None if not records else "a declaration assignment and another driver"
        if not records:
            return "no driver: the net reads z"
        intervals, texts = [], []
        generated_windows = False
        instance_windows = False
        for d in records:
            owner = d.containingSymbol
            kind = type(owner).__name__
            if kind not in _NET_OWNERS:
                return "driver of kind %s" % kind
            if kind == "InstanceSymbol":
                # An instance output is a continuous driver too, but unlike a
                # plain assign it is a hierarchy node.  Permit its
                # parameter-dependent static range only when slang confirms
                # that the output connection targets this exact net.  The
                # source-shaped range is checked below; expression-selected,
                # concatenated, and unrelated targets remain loud.
                target = _instance_driver_target(owner, symbol)
                if target is None:
                    return "instance output does not target this net"
                if type(target).__name__ not in (
                        "RangeSelectExpression", "NamedValueExpression",
                        "HierarchicalValueExpression"):
                    return "instance output selects a non-static window"
                instance_windows = True
            if owner.location not in drivers_here:
                # Slang's driver table puts every elaborated assignment from
                # a generate loop under the generate scope rather than the
                # module scope.  Keep the source-shaped genvar window; the
                # interval coverage below and Design2.driverGuard check the
                # actual parameter point for one driver per bit.
                if kind != "ContinuousAssignSymbol":
                    return "a driver inside a generate scope"
                generated_windows = True
            if kind == "ContinuousAssignSymbol" and (has_strength(owner) or getattr(owner, "delay", None) is not None):
                return "an explicit drive strength or a delay"
            lo, hi = d.bounds
            intervals.append((lo, hi))
            rng = d.sourceRange
            texts.append(_driver_source_text(ex, sm, rng))
        intervals.sort()
        edge = 0
        for lo, hi in intervals:
            if lo != edge:
                return "two drivers on a bit" if lo < edge else "undriven bits: the net reads z there"
            edge = hi + 1
        if edge != width:
            return "undriven bits: the net reads z there"
        if len(records) == 1 and texts[0] == symbol.name and not generated_windows:
            return None                                                       # (A)
        if generated_windows:
            gen_window = re.compile(r"^%s\s*\[\s*[A-Za-z_$][A-Za-z0-9_$]*\s*\]$" % re.escape(symbol.name))
            if all(gen_window.match(t) for t in texts):
                return None                                                       # generated genvar windows
            return "drivers select windows by an expression"
        if instance_windows:
            # ``sourceRange`` is the actual target text (for example
            # ``y[W/2-1:0]``).  Keep the instance and its range intact for the
            # hierarchy/E route; coverage above still rejects overlaps and
            # holes at the elaborated default point, while the parameter
            # cross-check and driversOk re-check every requested point.
            if all(t == symbol.name for t in texts):
                return None
            inst_window = re.compile(
                r"^%s\s*\[\s*[^\]]+\s*:\s*[^\]]+\s*\]$"
                % re.escape(symbol.name))
            if all(inst_window.match(t) for t in texts):
                return None
            return "instance output selects a non-static window"
        if not ex._sym_dtype_fixed(dtype):
            return "drivers select windows of a net whose width depends on a parameter"
        window = re.compile(r"^%s\s*(\[\s*\d+\s*(:\s*\d+\s*)?\])?$" % re.escape(symbol.name))
        if all(window.match(t) for t in texts):
            return None                                                       # (B)
        return "drivers select windows by an expression"
    except Exception as exc:        # noqa: BLE001  (fail closed)
        return "the drivers could not be decided (%s: %s)" % (type(exc).__name__, str(exc)[:100])


def net_variable(ex, sm, symbol, dtype):
    """N2. The `Var` declaration of a net accepted by `net_driver_reason`; a declaration assignment is queued as the
    process `take_pending` hands to `convert_module_sym`."""
    state = _MODULES[-1] if _MODULES else None
    init = symbol.initializer
    if init is not None and state is not None:
        state.pending.append({
            "kind": "Assign",
            "span": ex.node_span(sm, init),
            "target": {"kind": "Ident", "span": ex.sym_span(sm, symbol), "width": int(symbol.type.bitWidth),
                       "name": symbol.name},
            "value": ex.convert_expr(sm, init),
            "net_declaration_assign": True,
        })
    elif init is not None:
        return None
    result = {"kind": "Var", "span": ex.sym_span(sm, symbol), "name": symbol.name, "width": dtype, "init": None,
              "net_as_variable": True}
    if symbol.type.isSigned:
        result["signed"] = True
    return result


def take_pending():
    """The processes queued by the declaration just converted (N2)."""
    if not _MODULES:
        return []
    out, _MODULES[-1].pending = _MODULES[-1].pending, []
    return out
