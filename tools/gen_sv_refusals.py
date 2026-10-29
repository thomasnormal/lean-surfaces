#!/usr/bin/env python3
"""gen_sv_refusals.py -- the SystemVerilog refusal register: generator and completeness check.

The register is DATA: docs/sv-refusals.json.  This tool renders it into

  docs/sv-refusals.md      the ls-sv (sv-0.2 tier) register for maintainers,
  svgolf/REFUSALS.md       the svGolf-facing document for contestants and task authors,

and checks that the data still describes the code.  Python >= 3.9, stdlib only.

    python3 tools/gen_sv_refusals.py --write      regenerate both documents from the JSON
    python3 tools/gen_sv_refusals.py --check      exit 1 unless the register is complete and fresh
    python3 tools/gen_sv_refusals.py --scan       print every refusal kind found in the code
    python3 tools/gen_sv_refusals.py --where ID   current file:line of an entry's code sites
    python3 tools/gen_sv_refusals.py --emit-svgolf PATH   write svgolf/REFUSALS.md standalone
    python3 tools/gen_sv_refusals.py --fmt        rewrite the JSON in canonical layout

WITH AND WITHOUT svgolf/
------------------------
svGolf is a separate project; a checkout may not carry the `svgolf/` directory.  The tool detects it
(`has_svgolf`: the directory exists under the root; `--svgolf` / `--no-svgolf` override).  Without it,
--check verifies the ls-sv half only (extractor kinds, Lean tags, `match` texts, the JSON's internal
consistency, and docs/sv-refusals.md) and prints that the svGolf half was skipped; it requires no file under
svgolf/ and does not ask for svgolf/REFUSALS.md.  --write then regenerates docs/sv-refusals.md only and
never creates svgolf/.  docs/sv-refusals.md is a function of the JSON alone, so it is byte-identical in
both situations.

WHAT --check VERIFIES
---------------------
(i)   the generated files equal what --write would produce;
(ii)  COMPLETENESS, code -> register, for every refusal that carries a stable id:
        * extractor: every kind that an `unsupported(...)` call in extractors/sv/extract.py can
          emit in SYMBOLIC mode (found by an AST walk from `process_symbolic` that prunes the
          branches guarded by `_SYM is None`) is covered by an entry's `kinds.extractor`.
          A kind built from variables is a pattern (`PortSymbol:*`); a call without a kind
          argument takes the slang class name and is identified as `@default:<function>`.
          Kinds that are only reachable on the M0 / self-check path are NOT required (they are
          one blanket row), and the tool prints how many there are.
        * Lean: every tag that LeanModels/Sv production code builds with `.unsupported "TAG"`,
          `unsupported s!"TAG:{..}"`, `some ("TAG", ..)` or `.error s!"TAG: ..."` (comments and
          `#guard` blocks excluded) is covered by an entry's `kinds.lean`.
        * svGolf (only when svgolf/ is present): every attack / negative name in
          svgolf/tests/expected.json is cited by an entry's `attacks`, and the svGolf entries' own
          `match` / `where` files are checked like the ls-sv ones.
      and register -> code: every listed kind is still in the code (a removed refusal is
      noticed), and every `match` {file, text} pair (used for refusals that have only a message,
      not an id) still finds its text.  An entry whose category is `refused-pending` is the one
      exception: its kinds may be ABSENT from the code (decided, in flight).  If a pending kind
      appears in the code the tool warns (error with --strict) so the entry is refreshed.
(iii) every `later` names a prerequisite, every `never` a principle of the principle table,
      every later/never states `proposed`, ids are unique, groups and plan items exist.

A register kind is an exact string; `glob:<pattern>` (fnmatch) is a deliberate family; a bare `*`
is the code pattern of a call site whose entire kind is built at run time.  Rows hidden from the
svGolf document carry `"aggregate": true`.  The JSON's `schema` field documents every row field.

LIMITS, stated rather than hidden: free-text messages have no id, so for them only the
register -> code direction exists (`match`); a new message-only refusal is invisible to
--check until someone adds it.  Reachability of extractor kinds is a static over-approximation
(some statically live kinds are unreachable in practice, see the entries marked unverified).
Line numbers are never stored: `where` names a function, and --where resolves it to a line
at the moment of asking, so the data cannot rot when a file is edited above it.
"""

import argparse
import ast
import collections
import fnmatch
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REGISTER = "docs/sv-refusals.json"
OUT_MD = "docs/sv-refusals.md"
OUT_SVGOLF = "svgolf/REFUSALS.md"


def has_svgolf(root):
    """True when the checkout carries the svGolf project (the `svgolf/` directory)."""
    return os.path.isdir(os.path.join(root, "svgolf"))


HAS_SVGOLF = has_svgolf(ROOT)

CATEGORIES = ("refused-now", "later", "never", "refused-pending")
LAYERS = ("extractor", "lean-model", "lean-guard", "lean-loader", "lean-proof-tooling")
SVG_LAYERS = ("svgolf-gate", "svgolf-banlist", "svgolf-fourstate", "svgolf-checker",
              "svgolf-statement", "svgolf-task")

# ---------------------------------------------------------------------------
# scanning the code
# ---------------------------------------------------------------------------


def read(root, rel):
    with open(os.path.join(root, rel), encoding="utf-8", errors="replace") as fh:
        return fh.read()


def _is_sym(n):
    return isinstance(n, ast.Name) and n.id == "_SYM"


def _ev(t):
    """Value of a condition when `_SYM is not None` (symbolic mode): True / False / None."""
    if (isinstance(t, ast.Compare) and _is_sym(t.left) and len(t.ops) == 1
            and isinstance(t.comparators[0], ast.Constant) and t.comparators[0].value is None):
        if isinstance(t.ops[0], ast.Is):
            return False
        if isinstance(t.ops[0], ast.IsNot):
            return True
    if _is_sym(t):
        return True
    if isinstance(t, ast.UnaryOp) and isinstance(t.op, ast.Not):
        v = _ev(t.operand)
        return None if v is None else (not v)
    if isinstance(t, ast.BoolOp):
        vals = [_ev(x) for x in t.values]
        if isinstance(t.op, ast.And):
            if any(v is False for v in vals):
                return False
            if all(v is True for v in vals):
                return True
            return None
        if any(v is True for v in vals):
            return True
        if all(v is False for v in vals):
            return False
    return None


def _terminates(stmts):
    for s in stmts:
        if isinstance(s, (ast.Return, ast.Raise)):
            return True
        if isinstance(s, ast.If) and s.orelse and _terminates(s.body) and _terminates(s.orelse):
            return True
    return False


def _live_stmts(stmts, out):
    for s in stmts:
        if isinstance(s, ast.If):
            v = _ev(s.test)
            _live_expr(s.test, out)
            if v is True:
                _live_stmts(s.body, out)
                if _terminates(s.body):
                    return
            elif v is False:
                _live_stmts(s.orelse, out)
            else:
                _live_stmts(s.body, out)
                _live_stmts(s.orelse, out)
                if s.orelse and _terminates(s.body) and _terminates(s.orelse):
                    return
            continue
        if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef)):
            out.append(s)
            _live_stmts(s.body, out)
            continue
        if isinstance(s, (ast.For, ast.While)):
            _live_expr(getattr(s, "iter", None) or getattr(s, "test", None), out)
            _live_stmts(s.body, out)
            _live_stmts(s.orelse, out)
            continue
        if isinstance(s, ast.With):
            for it in s.items:
                _live_expr(it.context_expr, out)
            _live_stmts(s.body, out)
            continue
        if isinstance(s, ast.Try):
            _live_stmts(s.body, out)
            for h in s.handlers:
                _live_stmts(h.body, out)
            _live_stmts(s.orelse, out)
            _live_stmts(s.finalbody, out)
            continue
        _live_expr(s, out)


def _live_expr(e, out):
    if e is None:
        return
    if isinstance(e, ast.IfExp):
        v = _ev(e.test)
        _live_expr(e.test, out)
        if v is True:
            _live_expr(e.body, out)
        elif v is False:
            _live_expr(e.orelse, out)
        else:
            _live_expr(e.body, out)
            _live_expr(e.orelse, out)
        return
    if isinstance(e, ast.BoolOp):
        for x in e.values:
            _live_expr(x, out)
            v = _ev(x)
            if isinstance(e.op, ast.And) and v is False:
                break
            if isinstance(e.op, ast.Or) and v is True:
                break
        return
    out.append(e)
    for c in ast.iter_child_nodes(e):
        if isinstance(c, ast.stmt):
            continue
        _live_expr(c, out)


def _kind_arg(call):
    arg = None
    if len(call.args) >= 3:
        arg = call.args[2]
    for k in call.keywords:
        if k.arg == "sv_kind":
            arg = k.value
    return arg


def _pattern(arg):
    """The kind string an `sv_kind` argument evaluates to, with `*` for every variable part."""
    if arg is None:
        return None
    if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
        return arg.value
    if isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Add):
        return (_pattern(arg.left) or "*") + (_pattern(arg.right) or "*")
    if isinstance(arg, ast.JoinedStr):
        return "".join(v.value if isinstance(v, ast.Constant) else "*" for v in arg.values)
    return "*"


def _is_unsupported_call(n):
    if not isinstance(n, ast.Call):
        return False
    f = n.func
    name = f.id if isinstance(f, ast.Name) else (f.attr if isinstance(f, ast.Attribute) else None)
    return name == "unsupported"


def extractor_kinds(src, root_fn="process_symbolic"):
    """(all_patterns, live_patterns): {pattern: number of call sites}."""
    tree = ast.parse(src)
    funcs = collections.defaultdict(list)
    for n in ast.walk(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            funcs[n.name].append(n)
    cache = {}

    def live(name):
        if name not in cache:
            o = []
            for f in funcs.get(name, []):
                _live_stmts(f.body, o)
            cache[name] = o
        return cache[name]

    seen, stack = set(), [root_fn]
    while stack:
        f = stack.pop()
        if f in seen or f not in funcs:
            continue
        seen.add(f)
        for n in live(f):
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load) and n.id in funcs:
                stack.append(n.id)
    allk, livek = collections.Counter(), collections.Counter()
    for name, fns in funcs.items():
        for fn in fns:
            for n in ast.walk(fn):
                if _is_unsupported_call(n):
                    allk[_pattern(_kind_arg(n)) or "@default:" + name] += 1
    for name in seen:
        for n in live(name):
            if _is_unsupported_call(n):
                livek[_pattern(_kind_arg(n)) or "@default:" + name] += 1
    return dict(allk), dict(livek)


def strip_lean(text):
    """Lean source with comments removed and `#guard`/`#eval`/`example` blocks blanked."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1
    lines, res, skipping = "".join(out).split("\n"), [], False
    for ln in lines:
        if re.match(r"(#guard|#eval|#check|#print|example\b)", ln):
            skipping = True
        elif ln and not ln[0].isspace():
            skipping = False
        res.append("" if skipping else ln)
    return "\n".join(res)


_TAG = r"[A-Za-z][A-Za-z0-9_]*(?::[A-Za-z0-9_\-]+)*"
LEAN_RX = (
    re.compile(r'\bunsupported\s+"(' + _TAG + r')"'),
    re.compile(r'\bunsupported\s+s!"(' + _TAG + r')(?::?\{[^"]*)?"'),
    re.compile(r'some\s+\("(' + _TAG + r')"\s*,'),
    re.compile(r'\.error\s+s?!?"(' + _TAG + r'):\s'),
    re.compile(r'\.error\s+s!"(' + _TAG + r'):\{'),
)


def lean_tags(root, files, ignore=()):
    """{tag: sorted files} for the production Lean files."""
    res = collections.defaultdict(set)
    for rel in files:
        path = os.path.join(root, rel)
        if not os.path.exists(path):
            continue
        text = strip_lean(read(root, rel))
        for rx in LEAN_RX:
            for m in rx.finditer(text):
                if m.group(1) not in ignore:
                    res[m.group(1)].add(os.path.basename(rel))
    return {k: sorted(v) for k, v in res.items()}


def find_line(root, rel, fn):
    """1-based line of the definition of `fn` in `rel`, or None."""
    path = os.path.join(root, rel)
    if not os.path.exists(path):
        return None
    last = fn.split(".")[-1]
    defrx = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|partial|noncomputable|unsafe|"
                       r"opaque|abbrev|def|theorem|lemma|instance|structure|inductive|axiom)\s+)+"
                       r"(?:[\w.']*\.)?" + re.escape(last) + r"(?![\w?!'])|^\s*def\s+" + re.escape(last) + r"(?![\w?!'])")
    anyrx = re.compile(r"(?<![\w.])" + re.escape(last) + r"(?![\w?!'])")
    lines = read(root, rel).split("\n")
    for i, ln in enumerate(lines, 1):
        if defrx.search(ln):
            return i
    for i, ln in enumerate(lines, 1):
        if anyrx.search(ln):
            return i
    return None


# ---------------------------------------------------------------------------
# loading and validating the register
# ---------------------------------------------------------------------------


def load(root):
    with open(os.path.join(root, REGISTER), encoding="utf-8") as fh:
        return json.load(fh)


def all_entries(data):
    return list(data["entries"]) + list(data["svgolf"]["entries"])


def kinds_of(e, ns):
    k = e.get("kinds") or {}
    return list(k.get(ns, []))


def validate(data):
    """Structural problems of the register itself (no code needed)."""
    err = []
    cats = set(data["categories"])
    if cats != set(CATEGORIES):
        err.append("categories must be exactly %s, got %s" % (sorted(CATEGORIES), sorted(cats)))
    principles = {p["id"] for p in data["principles"]}
    groups = {g["id"] for g in data["groups"]} | {g["id"] for g in data["svgolf"]["groups"]}
    plans = {p["id"] for p in data.get("plan_items", [])}
    seen = set()
    for e in all_entries(data):
        eid = e.get("id")
        where = "entry %r" % eid
        if not eid or eid in seen:
            err.append("%s: id missing or duplicated" % where)
        seen.add(eid)
        for f in ("tag", "group", "layers", "trigger", "why", "category", "proposed"):
            if f not in e:
                err.append("%s: missing field %r" % (where, f))
        if e.get("category") not in CATEGORIES:
            err.append("%s: bad category %r" % (where, e.get("category")))
        if e.get("group") not in groups:
            err.append("%s: unknown group %r" % (where, e.get("group")))
        for ly in e.get("layers", []):
            if ly not in LAYERS + SVG_LAYERS:
                err.append("%s: unknown layer %r" % (where, ly))
        cat = e.get("category")
        if cat == "later":
            if not str(e.get("prerequisite", "")).strip():
                err.append("%s: category later without a prerequisite" % where)
            if not isinstance(e.get("proposed"), bool):
                err.append("%s: later without boolean `proposed`" % where)
        if cat == "never":
            if e.get("principle") not in principles:
                err.append("%s: category never without a principle of the table (got %r)"
                           % (where, e.get("principle")))
            if not isinstance(e.get("proposed"), bool):
                err.append("%s: never without boolean `proposed`" % where)
        if cat == "refused-pending":
            if not str(e.get("decided_by", "") or e.get("source", "")).strip():
                err.append("%s: refused-pending without the source of the decision" % where)
        if cat == "refused-now" and e.get("proposed") not in (False, None):
            err.append("%s: refused-now must not carry proposed=true (nothing is proposed)" % where)
        sv = e.get("svgolf")
        if sv:
            if sv.get("category") not in CATEGORIES:
                err.append("%s: svgolf.category invalid" % where)
            if sv.get("category") == "never" and sv.get("principle") not in principles:
                err.append("%s: svgolf never without a principle" % where)
            if sv.get("category") == "later" and not str(sv.get("prerequisite", "")).strip():
                err.append("%s: svgolf later without a prerequisite" % where)
        if e.get("plan") and e["plan"] not in plans:
            err.append("%s: unknown plan item %r" % (where, e["plan"]))
        if e.get("principle") and e["principle"] not in principles:
            err.append("%s: unknown principle %r" % (where, e["principle"]))
        for m in e.get("match", []):
            if not (m.get("file") and m.get("text")):
                err.append("%s: match needs file and text" % where)
    for g in data["svgolf"]["groups"]:
        if "stage" not in g:
            err.append("svgolf group %r lacks a stage" % g.get("id"))
    return err


def kind_matches(code_kind, reg_kind):
    """A register kind is an exact string, or `glob:<fnmatch pattern>` for a deliberate family."""
    if reg_kind.startswith("glob:"):
        return fnmatch.fnmatchcase(code_kind, reg_kind[5:])
    return code_kind == reg_kind


def covered(pattern, kinds):
    return any(kind_matches(pattern, k) for k in kinds)


def check_code(root, data, strict=False, svgolf=None):
    """(errors, warnings, info) of the register against the code.

    `svgolf` None = auto-detect (`has_svgolf`); False checks the ls-sv entries only."""
    err, warn, info = [], [], []
    scan = data["scan"]
    if svgolf is None:
        svgolf = has_svgolf(root)
    entries = all_entries(data) if svgolf else list(data["entries"])

    # --- extractor ---------------------------------------------------------
    ex_path = scan["extractor"]
    allk, livek = extractor_kinds(read(root, ex_path), scan.get("extractor_root", "process_symbolic"))
    ex_globs, ex_pending = [], []
    for e in entries:
        ks = kinds_of(e, "extractor")
        if e["category"] == "refused-pending":
            ex_pending += ks
        else:
            ex_globs += ks
    for k in sorted(livek):
        if not covered(k, ex_globs + ex_pending):
            err.append("extractor kind %r (symbolic mode, %d site(s)) is not in the register" % (k, livek[k]))
    m0 = [k for k in allk if k not in livek]
    info.append("extractor: %d kind patterns live in symbolic mode, %d only on the M0 / self-check path"
                % (len(livek), len(m0)))
    for e in entries:
        for k in kinds_of(e, "extractor"):
            hit = any(kind_matches(c, k) for c in allk)
            if e["category"] == "refused-pending":
                if hit:
                    (err if strict else warn).append(
                        "pending entry %r: extractor kind %r is now in the code -- refresh the entry" % (e["id"], k))
                continue
            if not hit:
                err.append("entry %r: extractor kind %r is no longer in %s" % (e["id"], k, ex_path))

    # --- Lean --------------------------------------------------------------
    files = scan["lean_files"]
    ltags = lean_tags(root, files, scan.get("lean_ignore_tags", ()))
    lean_globs, lean_pending = [], []
    for e in entries:
        ks = kinds_of(e, "lean")
        if e["category"] == "refused-pending":
            lean_pending += ks
        else:
            lean_globs += ks
    for t in sorted(ltags):
        if not covered(t, lean_globs + lean_pending):
            err.append("Lean tag %r (%s) is not in the register" % (t, ", ".join(ltags[t])))
    info.append("Lean: %d tags in production code (%d files scanned)" % (len(ltags), len(files)))
    for e in entries:
        for k in kinds_of(e, "lean"):
            hit = any(kind_matches(c, k) for c in ltags)
            if e["category"] == "refused-pending":
                if hit:
                    (err if strict else warn).append(
                        "pending entry %r: Lean tag %r is now in the code -- refresh the entry" % (e["id"], k))
                continue
            if not hit:
                err.append("entry %r: Lean tag %r is no longer built by the scanned Lean code" % (e["id"], k))

    # --- message matches ----------------------------------------------------
    cache = {}
    for e in entries:
        for m in e.get("match", []):
            p = m["file"]
            if p not in cache:
                cache[p] = read(root, p) if os.path.exists(os.path.join(root, p)) else None
            if cache[p] is None:
                if e["category"] != "refused-pending":
                    err.append("entry %r: match file %s does not exist" % (e["id"], p))
                continue
            found = m["text"] in cache[p]
            if e["category"] == "refused-pending":
                if found:
                    (err if strict else warn).append(
                        "pending entry %r: text %r is now in %s -- refresh the entry" % (e["id"], m["text"], p))
            elif not found:
                err.append("entry %r: text %r is no longer in %s" % (e["id"], m["text"], p))
        for w in e.get("where", []):
            if find_line(root, w["file"], w["fn"]) is None:
                warn.append("entry %r: %s (%s) cannot be located" % (e["id"], w["file"], w["fn"]))

    # --- svGolf attack / negative names ---------------------------------------
    exp = scan.get("svgolf_expected")
    if not svgolf:
        info.append("svGolf: half skipped because svgolf/ is absent (%d svGolf entries, their match/where files, the "
                    "attack citations of expected.json and svgolf/REFUSALS.md are not checked)"
                    % len(data["svgolf"]["entries"]))
    elif exp and os.path.exists(os.path.join(root, exp)):
        d = json.loads(read(root, exp))
        cited = {a for e in data["svgolf"]["entries"] for a in e.get("attacks", [])}
        for task, tv in sorted(d.get("tasks", {}).items()):
            for kind in ("negatives", "attacks"):
                for name in sorted(tv.get(kind, {})):
                    key = "%s/%s" % (task, name)
                    if key not in cited:
                        err.append("svgolf/tests/expected.json %s %r is not cited by any svgolf entry" % (kind[:-1], key))
        allnames = {"%s/%s" % (t, n) for t, tv in d.get("tasks", {}).items()
                    for kind in ("negatives", "attacks") for n in tv.get(kind, {})}
        for a in sorted(cited - allnames):
            err.append("svgolf entry cites attack/negative %r that is not in expected.json" % a)
        info.append("svGolf: %d attack/negative names in expected.json" % len(allnames))
    return err, warn, info


# ---------------------------------------------------------------------------
# rendering
# ---------------------------------------------------------------------------


def cell(s):
    s = " ".join(str(s).split())
    return s.replace("|", "\\|")


def code(s):
    """An inline code span for `s`, with a double fence when `s` itself contains a backtick."""
    return "`` %s ``" % s if "`" in s else "`%s`" % s


def is_sv(e, data):
    return any(x is e for x in data["svgolf"]["entries"])


def mark(e, key="proposed"):
    return "†" if e.get(key) is True else ""


def short_file(path):
    return os.path.basename(path)


def where_text(e):
    out = []
    for w in e.get("where", []):
        out.append("`%s:%s`" % (short_file(w["file"]), w["fn"]))
    return ", ".join(out)


def status_text(e, plans):
    cat = e["category"]
    d = "**%s**" % cat
    if cat == "later":
        d += "%s: %s" % (mark(e), e["prerequisite"])
        if e.get("plan"):
            d += " [%s]" % e["plan"]
    elif cat == "never":
        d += "%s: %s" % (mark(e), e["principle"])
    elif cat == "refused-pending":
        d += ": %s" % (e.get("decided_by") or e.get("source"))
    sv = e.get("svgolf")
    if sv:
        t = "svGolf: **%s**" % sv["category"]
        if sv["category"] == "never":
            t += "%s %s" % (mark(sv), sv["principle"])
        elif sv["category"] == "later":
            t += "%s: %s" % (mark(sv), sv["prerequisite"])
        d += "<br>" + t
    if e.get("unverified"):
        d += " (unverified)"
    return d


def entry_row(e, plans):
    tag = code(e["tag"])
    return "| %s | %s | %s | %s | %s |" % (
        cell(tag), cell(e["trigger"]), cell(e["why"]), cell(where_text(e) or "-"), cell(status_text(e, plans)))


def counts(entries):
    c = collections.Counter((e["category"]) for e in entries)
    return c


def render_register(data):
    L = []
    w = L.append
    plans = {p["id"]: p for p in data.get("plan_items", [])}
    ent = data["entries"]
    w("<!-- GENERATED by tools/gen_sv_refusals.py from docs/sv-refusals.json. DO NOT EDIT; edit the JSON and run --write. -->")
    w("")
    w("# SystemVerilog refusal register (ls-sv, schema sv-0.2)")
    w("")
    w(data["intro"].rstrip())
    w("")
    w("Register of %s. Snapshot: %s." % (data["scope"], data["snapshot"]))
    w("")
    w("## How to read this register")
    w("")
    w("Every construct the sv-0.2 tier does not accept is refused LOUDLY, never evaluated to a guess. "
      "Each row is one refusal tag (or a family of tags) with a measured trigger, the reason, where "
      "the code raises it, and its future. Marks: `†` = proposed by the register authors, not yet confirmed "
      "by Thomas; `(unverified)` = read from the source, not triggered by a run; a bare category without "
      "`†` is a recorded decision or a plain statement of today's behaviour.")
    w("")
    w("### The four categories")
    w("")
    w("| category | meaning |")
    w("|---|---|")
    for k in CATEGORIES:
        w("| `%s` | %s |" % (k, cell(data["categories"][k])))
    w("")
    w("### Two scopes: the ls-sv tier and svGolf admission")
    w("")
    w(data["scope_note"].rstrip())
    w("")
    w("### Principles behind `never`")
    w("")
    w("| principle | statement |")
    w("|---|---|")
    for p in data["principles"]:
        w("| `%s` | %s |" % (p["id"], cell(p["text"])))
    w("")
    w("## Standing policies")
    w("")
    w("| policy | source | decided |")
    w("|---|---|---|")
    for p in data["policies"]:
        w("| %s | %s | %s |" % (cell(p["policy"]), cell(p["source"]), "Thomas" if p.get("decided_by_thomas") else "lead / proposal"))
    w("")
    w("## Counts")
    w("")
    w("| layer | " + " | ".join("`%s`" % c for c in CATEGORIES) + " |")
    w("|---|" + "---|" * len(CATEGORIES))
    byl = collections.defaultdict(collections.Counter)
    for e in ent:
        byl[e["layers"][0]][e["category"]] += 1
    for ly in LAYERS:
        if ly in byl:
            w("| %s | " % ly + " | ".join(str(byl[ly][c]) for c in CATEGORIES) + " |")
    tot = counts(ent)
    w("| **ls-sv total** | " + " | ".join("**%d**" % tot[c] for c in CATEGORIES) + " |")
    sv = counts(data["svgolf"]["entries"])
    w("| svGolf checker (separate project: `svgolf/REFUSALS.md` on the golf branch) | " + " | ".join(str(sv[c]) for c in CATEGORIES) + " |")
    w("")
    # --- Allowed later, ordered by value ------------------------------------
    w("## Allowed later (ordered by expected value for svGolf tasks)")
    w("")
    w("What a contestant is likely to want first comes first. Rank and reason are the register authors' "
      "estimate (`†`); the prerequisite is what has to exist before the refusal can be lifted.")
    w("")
    ranked = sorted([e for e in ent + data["svgolf"]["entries"] if e["category"] == "later" and e.get("value_rank")],
                    key=lambda e: e["value_rank"])
    w("| # | construct | why a task wants it | prerequisite |")
    w("|---|---|---|---|")
    for e in ranked:
        w("| %d | %s | %s | %s%s |" % (e["value_rank"], cell(e["tag"] if is_sv(e, data) else code(e["tag"])), cell(e.get("value_note", "")),
                                         cell(e["prerequisite"]), " [%s]" % e["plan"] if e.get("plan") else ""))
    w("")
    rest = [e for e in ent if e["category"] == "later" and not e.get("value_rank")]
    rest = [e for e in rest if e["tag"]]
    w("Other `later` entries (no ranking: no recorded svGolf task needs them yet): " +
      ", ".join(code(e["tag"]) for e in rest) + ".")
    w("")
    w("### Roadmap items the prerequisites refer to")
    w("")
    w("| id | item | status and source | decided |")
    w("|---|---|---|---|")
    for p in data.get("plan_items", []):
        deps = [e["tag"] for e in ent + data["svgolf"]["entries"]
                if e.get("plan") == p["id"] or (e.get("svgolf") or {}).get("plan") == p["id"]]
        w("| `%s` | %s | %s (unblocks %d entr%s) | %s |" % (
            p["id"], cell(p["title"]), cell(p["source"]), len(deps), "y" if len(deps) == 1 else "ies",
            "Thomas" if p.get("decided_by_thomas") else "proposal"))
    w("")
    # --- Never ---------------------------------------------------------------
    w("## Never (by principle)")
    w("")
    w("Entries whose `never` classification rests on a principle. `ls-sv` rows are refused in the semantics "
      "tier itself; `svGolf` rows are constructs the semantics tier may model one day but a svGolf submission "
      "may not use (the scored artifact is a Yosys netlist).")
    w("")
    w("| scope | principle | construct | decided |")
    w("|---|---|---|---|")
    nv = []
    for e in ent:
        if e["category"] == "never":
            nv.append(("ls-sv", e["principle"], e["tag"], not e["proposed"], False))
        sg = e.get("svgolf")
        if sg and sg["category"] == "never":
            nv.append(("svGolf", sg["principle"], e["tag"], not sg.get("proposed", True), False))
    for e in data["svgolf"]["entries"]:
        if e["category"] == "never":
            nv.append(("svGolf", e["principle"], e["tag"], not e["proposed"], True))
    for scope, pr, tag, dec, plain in sorted(nv, key=lambda x: (x[0], x[1], x[2])):
        w("| %s | `%s` | %s | %s |" % (scope, pr, cell(tag if plain else code(tag)), "recorded" if dec else "proposed \u2020"))
    w("")
    # --- per group tables ------------------------------------------------------
    w("## The register")
    w("")
    w("One section per group. Columns: tag, a measured trigger (`H:` = the body of `module t(input logic [7:0] a, b, "
      "input logic c, output logic [7:0] y); ... endmodule`), why, where the code raises it (`file:function`; "
      "`python3 tools/gen_sv_refusals.py --where ID` prints current line numbers), and the status.")
    w("")
    for g in data["groups"]:
        rows = [e for e in ent if e["group"] == g["id"]]
        if not rows:
            continue
        w("### %s" % g["title"])
        w("")
        if g.get("note"):
            w(g["note"])
            w("")
        w("| tag | trigger | why | where | status |")
        w("|---|---|---|---|---|")
        for e in rows:
            w(entry_row(e, plans))
        w("")
    # --- departures, holes -----------------------------------------------------
    w("## Declared departures (not refusals)")
    w("")
    w("These are admitted and DIFFER from a simulator on purpose; each is a hash-bound row in `harness/sv/cases2.json`.")
    w("")
    w("| departure | what differs | source |")
    w("|---|---|---|")
    for d in data["departures"]:
        w("| %s | %s | %s |" % (cell(d["name"]), cell(d["text"]), cell(d["source"])))
    w("")
    w("## Known holes: admitted today, not refused")
    w("")
    w("A register of refusals cannot list what nobody refuses. These are the shapes the audits found that the "
      "tier ADMITS although a tool disagrees; none has been decided.")
    w("")
    w("| hole | what | source |")
    w("|---|---|---|")
    for d in data["holes"]:
        w("| %s | %s | %s |" % (cell(d["name"]), cell(d["text"]), cell(d["source"])))
    w("")
    w("## Detailed documents")
    w("")
    for d in data["docs"]:
        if d["path"].startswith("svgolf/"):   # the svGolf project may be absent from a checkout: no link
            w("- `%s` -- %s (svGolf project, golf branch)" % (d["path"], d["what"]))
            continue
        w("- [`%s`](%s) -- %s" % (d["path"], d["path"][len("docs/"):] if d["path"].startswith("docs/") else "../" + d["path"], d["what"]))
    w("")
    w("## Data format")
    w("")
    for line in data.get("schema", []):
        w("- " + line)
    w("")
    w("## Keeping this file true")
    w("")
    w("`python3 tools/gen_sv_refusals.py --check` fails when the extractor or the Lean code raises a tagged refusal "
      "that is not listed here, when a listed tag has disappeared from the code, or when this file is stale. "
      "After round-6 style work: rerun `--check`, add the new rows to `docs/sv-refusals.json`, run `--write`. "
      "A checkout without `svgolf/` (the svGolf project lives on the golf branch) is checked for this half only: "
      "`--check` says it skipped the svGolf half and `--write` regenerates this file alone.")
    w("")
    return "\n".join(L)


def render_svgolf(data):
    sg = data["svgolf"]
    L = []
    w = L.append
    plans = {p["id"]: p for p in data.get("plan_items", [])}
    w("<!-- GENERATED by tools/gen_sv_refusals.py from docs/sv-refusals.json (lean-surfaces). DO NOT EDIT; edit the JSON and run --write. -->")
    w("")
    w("# svGolf: what the checker refuses, and what you can write")
    w("")
    w(sg["intro"].rstrip())
    w("")
    w("## How to read this document")
    w("")
    w("Every restriction has one of four states. A mark `†` means the classification is a proposal, not yet "
      "confirmed by Thomas.")
    w("")
    w("| state | meaning |")
    w("|---|---|")
    for k in CATEGORIES:
        w("| `%s` | %s |" % (k, cell(data["categories"][k])))
    w("")
    w("The `never` rows rest on these principles:")
    w("")
    w("| principle | statement |")
    w("|---|---|")
    for p in data["principles"]:
        w("| `%s` | %s |" % (p["id"], cell(p["text"])))
    w("")
    w("## The pipeline: where a refusal can happen")
    w("")
    w("`check.py` runs the stages in this order and stops at the first that refuses; the stage name is what "
      "`tests/expected.json` records.")
    w("")
    w("| stage | what it does | refuses |")
    w("|---|---|---|")
    for s in sg["stages"]:
        w("| `%s` | %s | %s |" % (s["id"], cell(s["what"]), cell(s["refuses"])))
    w("")
    w("## Policies")
    w("")
    for p in sg["policies"]:
        w("- %s" % p)
    w("")
    for g in sg["groups"]:
        rows = [e for e in sg["entries"] if e["group"] == g["id"] and not e.get("aggregate")]
        w("## %s" % g["title"])
        w("")
        w(g["intro"].rstrip())
        w("")
        if rows:
            w("| refused | why | state |")
            w("|---|---|---|")
            for e in rows:
                w("| %s | %s | %s |" % (cell("**%s**<br>e.g. %s" % (e["tag"], e["trigger"])), cell(e["why"]), cell(status_text(e, plans))))
            w("")
        if g.get("write_ok") or g.get("refused_example"):
            if g.get("write_ok"):
                w("What you can write:")
                w("")
                w("```systemverilog")
                w(g["write_ok"].rstrip())
                w("```")
                w("")
            if g.get("refused_example"):
                w("What is refused:")
                w("")
                w("```systemverilog")
                w(g["refused_example"].rstrip())
                w("```")
                w("")
    w("## Constructs the ls-sv tier refuses, as seen from svGolf")
    w("")
    w("The `extract` and `design` stages pass on the refusals of the language tier (ls-sv). The full register is "
      "`docs/sv-refusals.md` in the lean-surfaces repository; the ones a task is most likely to run into, "
      "with what has to exist before each is allowed:")
    w("")
    w("| construct | why you might want it | prerequisite |")
    w("|---|---|---|")
    ranked = sorted([e for e in data["entries"] + sg["entries"] if e["category"] == "later" and e.get("value_rank")],
                    key=lambda e: e["value_rank"])
    for e in ranked:
        w("| %s | %s | %s |" % (cell(e["tag"] if is_sv(e, data) else code(e["tag"])), cell(e.get("value_note", "")), cell(e["prerequisite"])))
    w("")
    w("And what ls-sv will not model and svGolf will not accept for as long as the tools disagree or the "
      "construct is not hardware:")
    w("")
    for t in sg["never_summary"]:
        w("- %s" % t)
    w("")
    w("## How a refusal becomes allowed")
    w("")
    for t in sg["lifting"]:
        w("- %s" % t)
    w("")
    w("## Known limits (not refusals)")
    w("")
    for t in sg["limits"]:
        w("- %s" % t)
    w("")
    w("## Where to read more (paths in the lean-surfaces repository)")
    w("")
    for d in sg["links"]:
        w("- `%s` -- %s" % (d["path"], d["what"]))
    w("")
    return "\n".join(L)


# ---------------------------------------------------------------------------
# command line
# ---------------------------------------------------------------------------


def canonical_json(data):
    return json.dumps(data, indent=1, ensure_ascii=False) + "\n"


def rendered(root, svgolf=None):
    data = load(root)
    if svgolf is None:
        svgolf = has_svgolf(root)
    want = {OUT_MD: render_register(data) + "\n"}
    if svgolf:
        want[OUT_SVGOLF] = render_svgolf(data) + "\n"
    return data, want


def run_check(root, strict=False, out=sys.stdout, svgolf=None):
    if svgolf is None:
        svgolf = has_svgolf(root)
    data = load(root)
    errors = validate(data)
    e2, warns, info = check_code(root, data, strict, svgolf)
    errors += e2
    _, want = rendered(root, svgolf)
    for rel, text in want.items():
        path = os.path.join(root, rel)
        have = None
        if os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                have = fh.read()
        if have != text:
            errors.append("%s is %s; run: python3 tools/gen_sv_refusals.py --write"
                          % (rel, "missing" if have is None else "stale"))
    for i in info:
        print("info: " + i, file=out)
    for wmsg in warns:
        print("warning: " + wmsg, file=out)
    for emsg in errors:
        print("ERROR: " + emsg, file=out)
    if errors:
        print("sv-refusals: FAILED (%d error(s))" % len(errors), file=out)
        return 1
    if svgolf:
        print("sv-refusals: ok (%d ls-sv entries, %d svGolf entries)"
              % (len(data["entries"]), len(data["svgolf"]["entries"])), file=out)
    else:
        print("sv-refusals: ok (%d ls-sv entries; svGolf half skipped, svgolf/ is absent)" % len(data["entries"]), file=out)
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", default=ROOT, help="repository root (default: this checkout)")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--strict", action="store_true", help="pending kinds found in the code are errors")
    ap.add_argument("--scan", action="store_true")
    ap.add_argument("--where", metavar="ID")
    ap.add_argument("--emit-svgolf", metavar="PATH")
    ap.add_argument("--fmt", action="store_true")
    ap.add_argument("--svgolf", action=argparse.BooleanOptionalAction, default=None,
                    help="treat the svGolf half as present / absent (default: present iff <root>/svgolf exists)")
    a = ap.parse_args(argv)
    root = a.root
    svgolf = has_svgolf(root) if a.svgolf is None else a.svgolf
    if a.fmt:
        data = load(root)
        with open(os.path.join(root, REGISTER), "w", encoding="utf-8") as fh:
            fh.write(canonical_json(data))
        return 0
    if a.scan:
        data = load(root)
        scan = data["scan"]
        allk, livek = extractor_kinds(read(root, scan["extractor"]), scan.get("extractor_root", "process_symbolic"))
        print("# extractor kinds (L = live in symbolic mode, M = M0 only)")
        for k in sorted(allk):
            print("%s %s  x%d" % ("L" if k in livek else "M", k, allk[k]))
        print("# Lean tags")
        for t, fs in sorted(lean_tags(root, scan["lean_files"], scan.get("lean_ignore_tags", ())).items()):
            print("%s  %s" % (t, ",".join(fs)))
        return 0
    if a.where:
        data = load(root)
        for e in all_entries(data):
            if e["id"] == a.where:
                for w_ in e.get("where", []):
                    print("%s:%s (%s)" % (w_["file"], find_line(root, w_["file"], w_["fn"]) or "?", w_["fn"]))
                return 0
        print("no entry with id %r" % a.where, file=sys.stderr)
        return 1
    if a.emit_svgolf:
        data = load(root)
        with open(a.emit_svgolf, "w", encoding="utf-8") as fh:
            fh.write(render_svgolf(data) + "\n")
        return 0
    if a.write:
        data, want = rendered(root, svgolf)
        errs = validate(data)
        if errs:
            print("\n".join("ERROR: " + e for e in errs), file=sys.stderr)
            return 1
        if OUT_SVGOLF in want and not has_svgolf(root):
            print("ERROR: --svgolf asked for %s but %s/svgolf does not exist" % (OUT_SVGOLF, root), file=sys.stderr)
            return 1
        for rel, text in want.items():
            with open(os.path.join(root, rel), "w", encoding="utf-8") as fh:
                fh.write(text)
            print("wrote " + rel)
        return 0
    if a.check:
        return run_check(root, a.strict, sys.stdout, svgolf)
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
