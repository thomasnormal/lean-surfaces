#!/usr/bin/env python3
"""Regression tests for extractors/python/extract.py.

Run from anywhere: python3 extractors/python/test_extract.py
Stdlib-only, Python 3.9 compatible. Covers the extractor guarantees that
are not exercised by the Lean build:

  * header-injection regression: a source under a ``/-``-containing path
    (dash-leading directory segment, e.g. scratch roots under /tmp) must
    produce a companion whose header is ``--`` line comments — the
    block-comment form would open a nested Lean comment and corrupt the
    file;
  * the historical block-comment header is preserved byte-for-byte for
    normal paths (companions of unchanged sources regenerate byte-stably);
  * double-run determinism: same input bytes => same output bytes;
  * a source with no ``# lean[`` blocks gets an envelope and NO companion
    (three-file per-example layout);
  * a hand-written .lean at the companion path is never overwritten — hard
    ExtractError naming the file;
  * literal parameter defaults (int/bool/str/None) are emitted as per-param
    ``default`` payloads and clear ``args_unsupported``; any non-literal
    default keeps ``args_unsupported: "defaults"`` with NO ``default`` keys;
  * ``is``/``is not`` ship structurally for EVERY identity comparison
    (H1-proper: the interpreter decides identity dynamically and owns the
    tier boundary);
  * ``ClassDef`` (H3) is structured, with ``class_unsupported`` flagging
    bases/metaclass/decorators/class-level statements.
"""

import importlib.util
import json
import os
import shutil
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))

spec = importlib.util.spec_from_file_location(
    "extract_under_test", os.path.join(HERE, "extract.py"))
extract = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extract)

SOURCE_WITH_BLOCK = (
    "def double(x):\n"
    "    return x + x\n"
    "\n"
    "\n"
    "# lean[\n"
    "# #py_check double(21) = 42\n"
    "# ]\n"
)

SOURCE_NO_BLOCK = (
    "def double(x):\n"
    "    return x + x\n"
)


def read(path):
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def write(path, text):
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


class ExtractorTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="extract-test-", dir="/tmp")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    # -- the header-injection regression (the '/-' path bug) ---------------

    def test_dash_segment_path_gets_line_comment_header(self):
        # A directory segment starting with '-' makes the path contain '/-',
        # which inside a '/- ... -/' block comment opens a NESTED comment.
        srcdir = os.path.join(self.tmp, "-home-someone-project")
        os.makedirs(srcdir)
        src = os.path.join(srcdir, "double.py")
        write(src, SOURCE_WITH_BLOCK)
        extract.process_file(src, self.tmp)

        companion = os.path.join(self.tmp, "Double.lean")
        text = read(companion)
        header = text.split("import LeanModels")[0]
        self.assertIn("/-", src.replace(os.sep, "/"))  # premise of the test
        self.assertTrue(
            text.startswith("-- " + extract.AUTOGEN_MARKER),
            "dangerous path must switch the header to line comments:\n" + header,
        )
        self.assertIn("-- source: ", header)
        self.assertIn("-- sha256: ", header)
        # No block comment anywhere in the header => nothing to corrupt.
        self.assertNotIn("/-\n", header)
        # The dangerous sequence may only survive where Lean cannot read it
        # as a comment opener: inside `--` line comments and inside the
        # `load_program ... from "<path>"` string literal. (The original
        # failure mode: a bare `/-` opened an unterminated block comment.)
        for ln in text.split("\n"):
            if "/-" in ln:
                self.assertTrue(
                    ln.lstrip().startswith("--") or 'from "' in ln,
                    "raw block-comment opener leaked into the companion: %r" % ln,
                )

    def test_normal_path_keeps_block_comment_header_verbatim(self):
        src = os.path.join(self.tmp, "double.py")
        write(src, SOURCE_WITH_BLOCK)
        extract.process_file(src, self.tmp)
        text = read(os.path.join(self.tmp, "Double.lean"))
        sha = extract.hashlib.sha256(
            SOURCE_WITH_BLOCK.encode("utf-8")).hexdigest()
        expected = (
            "/-\n"
            + extract.AUTOGEN_MARKER + " — DO NOT EDIT.\n"
            + "source: " + src.replace(os.sep, "/") + "\n"
            + "sha256: " + sha + "\n"
            + "-/\n"
        )
        self.assertTrue(
            text.startswith(expected),
            "historical block-comment header must be byte-stable",
        )

    # -- determinism --------------------------------------------------------

    def test_double_run_is_byte_stable(self):
        src = os.path.join(self.tmp, "double.py")
        write(src, SOURCE_WITH_BLOCK)
        extract.process_file(src, self.tmp)
        json1 = read(os.path.join(self.tmp, "double.json"))
        lean1 = read(os.path.join(self.tmp, "Double.lean"))
        extract.process_file(src, self.tmp)
        self.assertEqual(json1, read(os.path.join(self.tmp, "double.json")))
        self.assertEqual(lean1, read(os.path.join(self.tmp, "Double.lean")))

    # -- three-file layout: no blocks => no companion ------------------------

    def test_no_lean_blocks_emits_envelope_only(self):
        src = os.path.join(self.tmp, "double.py")
        write(src, SOURCE_NO_BLOCK)
        extract.process_file(src, self.tmp)
        self.assertTrue(os.path.exists(os.path.join(self.tmp, "double.json")))
        self.assertFalse(
            os.path.exists(os.path.join(self.tmp, "Double.lean")),
            "a block-less source must not generate a companion",
        )

    # -- default companion dir: next to the source ---------------------------

    def test_default_companion_dir_is_source_dir(self):
        # Per-example layout: with companion_dir=None the companion must land
        # NEXT TO the source (Examples/python/sum_to/sum_to.py → Examples/python/sum_to/
        # SumTo.lean), not in any fixed root.
        srcdir = os.path.join(self.tmp, "sum_to")
        os.makedirs(srcdir)
        src = os.path.join(srcdir, "sum_to.py")
        write(src, SOURCE_WITH_BLOCK)
        extract.process_file(src, None)
        self.assertTrue(
            os.path.exists(os.path.join(srcdir, "SumTo.lean")),
            "default companion dir must be the source file's own directory",
        )
        self.assertFalse(os.path.exists(os.path.join(self.tmp, "SumTo.lean")))

    # -- hand-written files are never clobbered ------------------------------

    def test_refuses_to_overwrite_hand_written_lean(self):
        src = os.path.join(self.tmp, "double.py")
        write(src, SOURCE_WITH_BLOCK)
        companion = os.path.join(self.tmp, "Double.lean")
        hand_written = "-- my precious hand-written spec\ntheorem t : True := trivial\n"
        write(companion, hand_written)
        with self.assertRaises(extract.ExtractError) as ctx:
            extract.process_file(src, self.tmp)
        self.assertIn("Double.lean", str(ctx.exception))
        self.assertEqual(read(companion), hand_written, "file must be untouched")

    def test_overwrites_generated_companion(self):
        src = os.path.join(self.tmp, "double.py")
        write(src, SOURCE_WITH_BLOCK)
        extract.process_file(src, self.tmp)
        first = read(os.path.join(self.tmp, "Double.lean"))
        extract.process_file(src, self.tmp)  # must not raise
        self.assertEqual(first, read(os.path.join(self.tmp, "Double.lean")))

    # -- F1: literal parameter defaults --------------------------------------

    def _envelope_of(self, source, stem="mod"):
        src = os.path.join(self.tmp, stem + ".py")
        write(src, source)
        extract.process_file(src, self.tmp)
        with open(os.path.join(self.tmp, stem + ".json"),
                  "r", encoding="utf-8") as f:
            return json.load(f)

    def _first_fn(self, source):
        return self._envelope_of(source)["module"]["body"][0]

    def test_literal_defaults_emitted_and_in_tier(self):
        fn = self._first_fn(
            "def f(a, i=3, b=True, s='x', n=None):\n    return a\n")
        self.assertIsNone(fn["args_unsupported"])
        self.assertEqual(
            [p.get("default") for p in fn["args"]],
            [None,
             {"type": "int", "repr": "3"},
             {"type": "bool", "value": True},
             {"type": "str", "value": "x"},
             {"type": "none"}])

    def test_non_literal_default_stays_unsupported(self):
        # A Name default (the easter.py EASTER_WESTERN shape) and a negative
        # number (UnaryOp, not Constant) are both non-literal: the function
        # keeps args_unsupported="defaults" and emits NO default keys —
        # mixed literal/non-literal included.
        for src in ("def f(a, m=EASTER_WESTERN):\n    return a\n",
                    "def f(a, lo=-1):\n    return a\n",
                    "def f(a, b=1, c=NAMED):\n    return a\n",
                    "def f(a, x=1.5):\n    return a\n"):
            fn = self._first_fn(src)
            self.assertEqual(fn["args_unsupported"], "defaults", src)
            self.assertTrue(
                all("default" not in p for p in fn["args"]), src)

    def test_default_free_param_object_unchanged(self):
        # Byte-level compatibility: a param without a default has exactly the
        # historical two keys (no "default": null noise).
        fn = self._first_fn("def f(a, b):\n    return a\n")
        for p in fn["args"]:
            self.assertEqual(sorted(p.keys()), ["arg", "span"])

    # -- F2: is / is not gated on a literal-None side ------------------------

    def _first_return_expr(self, source):
        fn = self._first_fn(source)
        return fn["body"][0]["value"]

    def test_is_none_survives_either_side(self):
        for src, ops in (
                ("def f(x):\n    return x is None\n", ["Is"]),
                ("def f(x):\n    return x is not None\n", ["IsNot"]),
                ("def f(x):\n    return None is x\n", ["Is"])):
            e = self._first_return_expr(src)
            self.assertEqual(e["kind"], "Compare", src)
            self.assertEqual(e["ops"], ops, src)

    def test_is_without_none_is_structural(self):
        # Since H1-proper the extractor emits Is/IsNot for EVERY identity
        # comparison: identity is decided DYNAMICALLY by the interpreter
        # (refs by address, None by the singleton test), which loudly
        # refuses the remaining out-of-tier operand forms. (These two
        # tests previously pinned the pre-H1 gate-at-extraction behavior
        # and had gone stale — repaired to the recorded decision.)
        for src, ops in (("def f(x, y):\n    return x is y\n", ["Is"]),
                         ("def f(x, y):\n    return x is not y\n", ["IsNot"])):
            e = self._first_return_expr(src)
            self.assertEqual(e["kind"], "Compare", src)
            self.assertEqual(e["ops"], ops, src)

    def test_chained_is_is_structural(self):
        # chains too: every link ships structurally, the interpreter owns
        # the per-link tier boundary.
        e = self._first_return_expr("def f(x):\n    return x is None is None\n")
        self.assertEqual(e["kind"], "Compare")
        self.assertEqual(e["ops"], ["Is", "Is"])
        e = self._first_return_expr(
            "def f(x, y):\n    return x is y is None\n")
        self.assertEqual(e["kind"], "Compare")
        self.assertEqual(e["ops"], ["Is", "Is"])

    # -- call:sorted: NO extractor special-casing (exact `len` analogy) ------

    def test_sorted_call_is_plain_in_tier_call(self):
        # `sorted(xs)` is a plain Call node whose callee is Name "sorted" —
        # the builtin lives entirely in the interpreter's name-resolution
        # order; the extractor emits no builtin table and no marking.
        e = self._first_return_expr("def f(xs):\n    return sorted(xs)\n")
        self.assertEqual(e["kind"], "Call")
        self.assertIsNone(e["call_unsupported"])
        self.assertEqual(e["func"]["kind"], "Name")
        self.assertEqual(e["func"]["id"], "sorted")
        self.assertEqual(len(e["args"]), 1)

    def test_call_keywords_are_structured(self):
        # H6: plain named keywords are STRUCTURED (name + value), no
        # call_unsupported flag — binding happens in the interpreter
        # (docs/memory-model.md §call-site keyword arguments).
        for src, kwnames in (
                ("def f(xs, g):\n    return sorted(xs, key=g)\n", ["key"]),
                ("def f(xs):\n    return sorted(xs, reverse=True)\n", ["reverse"]),
                ("def f(p):\n    return p.rotate(nullmove=True)\n", ["nullmove"])):
            e = self._first_return_expr(src)
            self.assertEqual(e["kind"], "Call", src)
            self.assertIsNone(e["call_unsupported"], src)
            self.assertEqual([kw["arg"] for kw in e["keywords"]], kwnames, src)
            for kw in e["keywords"]:
                self.assertIn("kind", kw["value"], src)

    def test_nested_def_is_structured(self):
        # H7: a def DIRECTLY inside a function body, captures never
        # rebound after — structured with the capture set.
        fn = self._first_fn(
            "def outer(a):\n    b = a + 1\n    def inner(x):\n"
            "        return x * b + a\n    return inner(3)\n")
        nd = fn["body"][1]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertEqual(nd["captures"], ["a", "b"])
        self.assertIsNone(nd["closure_unsupported"])

    def test_nested_generator_def_keeps_flag(self):
        fn = self._first_fn(
            "def outer(n):\n    lim = n * 2\n    def g():\n"
            "        i = 0\n        while i < lim:\n"
            "            yield i\n            i = i + 1\n"
            "    return g\n")
        nd = fn["body"][1]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertTrue(nd.get("is_generator"))
        self.assertEqual(nd["captures"], ["lim"])
        self.assertIsNone(nd["closure_unsupported"])

    def test_nested_def_rebound_after_refuses(self):
        # snapshot-at-def would diverge from CPython's cell: LOUD.
        fn = self._first_fn(
            "def outer(a):\n    def f():\n        return a\n"
            "    a = a + 1\n    return f()\n")
        nd = fn["body"][0]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertIn("rebound after the def", nd["closure_unsupported"])

    def test_nested_def_nonlocal_refuses(self):
        fn = self._first_fn(
            "def outer(a):\n    c = 0\n    def f():\n"
            "        nonlocal c\n        c = c + 1\n    f()\n    return c\n")
        nd = fn["body"][1]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertIn("nonlocal", nd["closure_unsupported"])

    def test_nested_def_inside_loop_stays_plain_functiondef(self):
        # not a DIRECT child of the body: plain FunctionDef, which
        # ingestion refuses loudly (the loop is where snapshot-vs-cell
        # becomes observable)
        fn = self._first_fn(
            "def outer(a):\n    t = 0\n    while a > 0:\n"
            "        def f():\n            return a\n"
            "        t = t + f()\n        a = a - 1\n    return t\n")
        loop = fn["body"][1]
        self.assertEqual(loop["body"][0]["kind"], "FunctionDef")

    def test_early_call_of_nested_name_flags_locals(self):
        # CPython: UnboundLocalError (static-locals rule) — a module
        # fallthrough would silently call the wrong function: LOUD.
        fn = self._first_fn(
            "def outer(a):\n    r = f()\n    def f():\n"
            "        return a\n    return r\n")
        self.assertIn("nested-def name", fn["locals_unsupported"])

    def test_call_kwargs_unpacking_stays_unsupported_loud(self):
        # `f(**d)` (a keyword node with arg=None) has no per-name binding
        # story — it stays a LOUD call_unsupported, and the structured
        # keywords list carries only the named ones.
        e = self._first_return_expr("def f(g, d):\n    return g(1, **d)\n")
        self.assertEqual(e["kind"], "Call", src := "g(1, **d)")
        self.assertEqual(e["call_unsupported"], "** unpacking in call", src)
        self.assertEqual(e["keywords"], [], src)

    def test_sorted_shadowing_assignment_after_is_admitted(self):
        # H7 refinement: a single direct assignment with every call AFTER
        # it has no UnboundLocalError window — the dynamic env is faithful
        # (here: the REAL TypeError, `sorted` shadowed by an int).
        fn = self._first_fn(
            "def f(xs):\n    sorted = 3\n    return sorted(xs)\n")
        self.assertIsNone(fn["locals_unsupported"])

    def test_call_before_assignment_still_flags_locals(self):
        # the UnboundLocalError window is real here: still LOUD.
        fn = self._first_fn(
            "def f(xs):\n    r = sorted(xs)\n    sorted = 3\n    return r\n")
        self.assertEqual(
            fn["locals_unsupported"],
            "calls locally-assigned name(s) (static-locals rule): sorted")


    # -- For statements and module constants (sunfish ladder steps 1-2) ----

    def test_for_over_name_is_structured(self):
        env = self._envelope_of(
            "def f(xs):\n    t = 0\n    for v in xs:\n"
            "        t += v\n    return t\n")
        st = env["module"]["body"][0]["body"][1]
        self.assertEqual(st["kind"], "For")
        self.assertEqual(st["target"]["kind"], "Name")
        self.assertEqual(st["iter"]["kind"], "Name")
        self.assertEqual(st["orelse"], [])
        self.assertEqual(st["body"][0]["kind"], "AugAssign")

    def test_for_tuple_target_is_structured(self):
        env = self._envelope_of(
            "def f(ps):\n    t = 0\n    for a, b in ps:\n"
            "        t = a + b\n    return t\n")
        st = env["module"]["body"][0]["body"][1]
        self.assertEqual(st["kind"], "For")
        self.assertEqual(st["target"]["kind"], "Tuple")

    def test_for_else_keeps_orelse(self):
        # `for … else` is representable (the interpreter refuses it loudly).
        env = self._envelope_of(
            "def f(xs):\n    for v in xs:\n        pass\n"
            "    else:\n        pass\n    return 0\n")
        st = env["module"]["body"][0]["body"][0]
        self.assertEqual(st["kind"], "For")
        self.assertEqual(len(st["orelse"]), 1)

    def test_module_constants_are_plain_assigns(self):
        # Top-level constant bindings (G1 globals) ride through as ordinary
        # Assign statements in module body order — no special marking.
        env = self._envelope_of(
            "MATE = 69290\nA1, H1 = 91, 98\n\ndef f():\n    return MATE\n")
        kinds = [st["kind"] for st in env["module"]["body"]]
        self.assertEqual(kinds, ["Assign", "Assign", "FunctionDef"])


    # -- Dict / Attribute representation (H0, docs/memory-model.md) --------

    def test_dict_literal_is_structured(self):
        e = self._first_return_expr(
            "def f():\n    return {\"P\": 100, \"N\": 280}\n")
        self.assertEqual(e["kind"], "Dict")
        self.assertEqual(len(e["keys"]), 2)
        self.assertEqual(len(e["values"]), 2)
        self.assertEqual(e["keys"][0]["kind"], "Constant")

    def test_dict_unpack_stays_unsupported(self):
        e = self._first_return_expr(
            "def f(d):\n    return {\"a\": 1, **d}\n")
        self.assertEqual(e["kind"], "Unsupported")
        self.assertEqual(e["py_kind"], "Dict:unpack")

    def test_attribute_load_is_structured(self):
        e = self._first_return_expr(
            "def f(pos):\n    return pos.score\n")
        self.assertEqual(e["kind"], "Attribute")
        self.assertEqual(e["attr"], "score")
        self.assertEqual(e["value"]["kind"], "Name")

    def test_attribute_call_is_structured(self):
        # `d.get(k)` — a Call whose callee is an Attribute node.
        e = self._first_return_expr(
            "def f(d, k):\n    return d.get(k)\n")
        self.assertEqual(e["kind"], "Call")
        self.assertEqual(e["func"]["kind"], "Attribute")
        self.assertEqual(e["func"]["attr"], "get")


class ClassDefTests(unittest.TestCase):
    # -- H3: ClassDef is structured; tier flags mirror args_unsupported ----

    def _module_body(self, source):
        import ast
        return [extract.convert_stmt(st) for st in ast.parse(source).body]

    def test_plain_class_is_structured(self):
        body = self._module_body(
            "class C:\n"
            "    def __init__(self, x):\n"
            "        self.x = x\n"
            "    def get(self):\n"
            "        return self.x\n")
        c = body[0]
        self.assertEqual(c["kind"], "ClassDef")
        self.assertEqual(c["name"], "C")
        self.assertIsNone(c["class_unsupported"])
        self.assertEqual([m["kind"] for m in c["body"]],
                         ["FunctionDef", "FunctionDef"])
        self.assertEqual([m["name"] for m in c["body"]], ["__init__", "get"])

    def test_docstring_and_pass_stay_in_tier(self):
        body = self._module_body('class C:\n    "doc"\n    pass\n')
        self.assertIsNone(body[0]["class_unsupported"])

    def test_bases_flag_class_unsupported(self):
        body = self._module_body("class C(D):\n    pass\n")
        self.assertIn("bases", body[0]["class_unsupported"])

    def test_metaclass_and_decorators_flag(self):
        body = self._module_body("class C(metaclass=type):\n    pass\n")
        self.assertIn("metaclass", body[0]["class_unsupported"])
        body = self._module_body("@deco\nclass C:\n    pass\n")
        self.assertIn("decorators", body[0]["class_unsupported"])

    def test_class_attributes_flag(self):
        body = self._module_body("class C:\n    x = 1\n")
        self.assertIn("class-level statements", body[0]["class_unsupported"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
