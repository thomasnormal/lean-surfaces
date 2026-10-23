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
        # The subject here is the HEADER SHAPE, not the path policy: since
        # 2026-08-16 `rel_posix` canonicalises (repo-relative inside the
        # tree, realpath outside), and this fixture lives in a temp dir
        # whose `/var` realpaths to `/private/var`. Path invariance has its
        # own tests (tools/test_leanpy.py).
        expected = (
            "/-\n"
            + extract.AUTOGEN_MARKER + " — DO NOT EDIT.\n"
            + "source: " + extract.rel_posix(src) + "\n"
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

    def test_ellipsis_constant_and_default(self):
        fn = self._first_fn("def f(value=...):\n    return ...\n")
        self.assertIsNone(fn["args_unsupported"])
        self.assertEqual(fn["args"][0]["default"], {"type": "ellipsis"})
        self.assertEqual(fn["body"][0]["value"]["kind"], "Constant")
        self.assertEqual(fn["body"][0]["value"]["value"], {"type": "ellipsis"})

    def test_float_constant_default_and_true_division(self):
        fn = self._first_fn("def f(value=0.1):\n    return value / 2.0\n")
        self.assertIsNone(fn["args_unsupported"])
        self.assertEqual(fn["args"][0]["default"],
                         {"type": "float", "bits": "4591870180066957722"})
        expression = fn["body"][0]["value"]
        self.assertEqual(expression["kind"], "BinOp")
        self.assertEqual(expression["op"], "Div")
        self.assertEqual(expression["right"]["value"],
                         {"type": "float", "bits": "4611686018427387904"})

    def test_float_subnormal_and_infinity_bits(self):
        fn = self._first_fn("def f():\n    return 5e-324, 1e999\n")
        values = [element["value"] for element in fn["body"][0]["value"]["elts"]]
        self.assertEqual(values, [{"type": "float", "bits": "1"},
                                  {"type": "float", "bits": "9218868437227405312"}])

    def test_bytes_literal_and_default_preserve_octets(self):
        fn = self._first_fn("def f(value=b'ab\\x00\\xff'):\n    return b'\\x01\\x80'\n")
        self.assertIsNone(fn["args_unsupported"])
        self.assertEqual(fn["args"][0]["default"],
                         {"type": "bytes", "value": [97, 98, 0, 255]})
        self.assertEqual(fn["body"][0]["value"]["value"],
                         {"type": "bytes", "value": [1, 128]})

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
                    "def f(a, b=1, c=NAMED):\n    return a\n"):
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

    def test_fstring_retains_structured_fields_and_conversion_codes(self):
        expression = self._first_return_expr(
            "def f(value):\n    return f'a{value}/{value!s}/{value!r}b'\n")
        self.assertEqual(expression["kind"], "JoinedStr")
        fields = [part for part in expression["values"]
                  if part["kind"] == "FormattedValue"]
        self.assertEqual([field["conversion"] for field in fields], [-1, 115, 114])
        self.assertTrue(all(field["format_spec"] is None for field in fields))
        self.assertTrue(all(field["value"]["id"] == "value" for field in fields))

    def test_fstring_conversion_is_not_a_shadowable_name_call(self):
        for source in (
                "def f(str, repr):\n    return f'{3!r}/{3!s}/{3}'\n",
                "str = 7\nrepr = 8\ndef f():\n    return f'{3!r}/{3!s}/{3}'\n"):
            function = self._envelope_of(source)["module"]["body"][-1]
            expression = function["body"][0]["value"]
            self.assertEqual(expression["kind"], "JoinedStr")
            self.assertEqual(
                [part["conversion"] for part in expression["values"]
                 if part["kind"] == "FormattedValue"], [114, 115, -1])

    def test_fstring_debug_retains_text_and_default_repr_conversion(self):
        expression = self._first_return_expr(
            "def f(value):\n    return f'{value=}'\n")
        self.assertEqual(expression["values"][0]["value"],
                         {"type": "str", "value": "value="})
        self.assertEqual(expression["values"][1]["conversion"], 114)

    def test_fstring_empty_format_spec_is_structured(self):
        expression = self._first_return_expr(
            "def f(value):\n    return f'{value!r:}'\n")
        specification = expression["values"][0]["format_spec"]
        self.assertEqual(specification["kind"], "JoinedStr")
        self.assertEqual(specification["values"], [])

    def test_fstring_ascii_conversion_is_structured(self):
        expression = self._first_return_expr(
            "def f(value):\n    return f'{value!a}'\n")
        self.assertEqual(expression["kind"], "JoinedStr")
        self.assertEqual(expression["values"][0]["conversion"], 97)

    def test_fstring_nonempty_format_specs_remain_loud(self):
        for field in ("value!r:>5", "value!s:03d"):
            expression = self._first_return_expr(
                "def f(value):\n    return f'{" + field + "}'\n")
            self.assertEqual(expression["kind"], "Unsupported")
            self.assertEqual(expression["py_kind"], "JoinedStr:format_spec")

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

    def test_nested_def_rebound_after_is_a_CELL(self):
        # H7 cells: snapshot-at-def would diverge from CPython's cell, so
        # the capture ships as a real cell (`<cell>a`) and the def is
        # ADMITTED -- `f` is called, never escapes, and is not a generator.
        fn = self._first_fn(
            "def outer(a):\n    def f():\n        return a\n"
            "    a = a + 1\n    return f()\n")
        nd = fn["body"][0]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertIsNone(nd["closure_unsupported"])
        self.assertEqual(nd["captures"], ["<cell>a"])

    def test_cell_capture_escaping_the_frame_refuses(self):
        # the cell is refreshed from the DEFINING frame at the call, so an
        # escaping closure would read it stale: LOUD.
        fn = self._first_fn(
            "def outer(a):\n    def f():\n        return a\n"
            "    a = a + 1\n    return f\n")
        nd = fn["body"][0]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertIn("ESCAPES", nd["closure_unsupported"])

    def test_cell_capture_rebound_after_a_generator_call_refuses(self):
        # a generator reads its cells at RESUME; the tier refreshes at the
        # call only, so a rebinding at or after the first call is LOUD.
        fn = self._first_fn(
            "def outer(a):\n    def g():\n        yield a\n"
            "    t = 0\n    for v in g():\n        a = a + 1\n"
            "        t = t + v\n    return t\n")
        nd = fn["body"][0]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertIn("at or after the first call", nd["closure_unsupported"])

    def test_generator_cell_bound_before_first_call_is_admitted(self):
        # the shipped `moves()` shape: the celled name is written after the
        # def but BEFORE the generator is ever called.
        fn = self._first_fn(
            "def outer(a):\n    def g():\n        yield a\n"
            "    a = a + 1\n    t = 0\n    for v in g():\n"
            "        t = t + v\n    return t\n")
        nd = fn["body"][0]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertIsNone(nd["closure_unsupported"])
        self.assertEqual(nd["captures"], ["<cell>a"])

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

    def test_lambda_assign_is_nested_def(self):
        # H7 lambdas: `put = lambda …` directly in a body is the
        # nested-def shape with a Return-expression body.
        fn = self._first_fn(
            "def f(s, i, p):\n"
            "    put = lambda board, i, p: board[:i] + p + board[i + 1:]\n"
            "    return put(s, i, p)\n")
        nd = fn["body"][0]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertEqual(nd["name"], "put")
        self.assertEqual(nd["captures"], [])
        self.assertIsNone(nd["closure_unsupported"])
        self.assertEqual(nd["body"][0]["kind"], "Return")

    def test_lambda_capture_rebound_is_a_CELL(self):
        fn = self._first_fn(
            "def f(a):\n    g = lambda: a\n    a = a + 1\n    return g()\n")
        nd = fn["body"][0]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertIsNone(nd["closure_unsupported"])
        self.assertEqual(nd["captures"], ["<cell>a"])

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

    def test_raise_local_binding_refuses_without_order_exemptions(self):
        for source in (
            "def f(ValueError):\n    raise ValueError\n",
            "def f(ValueError):\n    raise ValueError()\n",
            "def f():\n    raise ValueError\n    ValueError = 1\n",
            "def f():\n    raise ValueError()\n    ValueError = 1\n",
            "def f():\n    if False:\n        ValueError = 1\n    raise ValueError\n",
            "def f():\n    if False:\n        ValueError = 1\n    raise ValueError()\n",
        ):
            with self.subTest(source=source):
                reason = self._first_fn(source)["locals_unsupported"]
                self.assertIn("ValueError", reason)

    def test_raise_guard_does_not_cross_nested_scopes(self):
        fn = self._first_fn(
            "def f():\n    def g(ValueError):\n        return ValueError\n"
            "    raise ValueError\n")
        self.assertIsNone(fn["locals_unsupported"])

    def test_zero_argument_raise_constructor_lowers_to_class_name(self):
        fn = self._first_fn("def f():\n    raise ValueError()\n")
        exc = fn["body"][0]["exc"]
        self.assertEqual(exc["kind"], "Name")
        self.assertEqual(exc["id"], "ValueError")

    def test_raise_constructor_with_arguments_stays_a_call(self):
        fn = self._first_fn("def f():\n    raise ValueError('boom')\n")
        exc = fn["body"][0]["exc"]
        self.assertEqual(exc["kind"], "Call")
        self.assertEqual(exc["func"]["id"], "ValueError")

    def test_handler_local_binding_refuses_without_order_exemptions(self):
        bodies = (
            "    try:\n        TypeError = 1\n        len(1)\n"
            "    except TypeError:\n        return 9\n",
            "    try:\n        len(1)\n"
            "    except TypeError:\n        return 9\n    TypeError = 1\n",
            "    if False:\n        TypeError = 1\n"
            "    try:\n        len(1)\n    except TypeError:\n        return 9\n",
            "    def TypeError():\n        return 1\n"
            "    try:\n        len(1)\n    except TypeError:\n        return 9\n",
            "    class TypeError:\n        pass\n"
            "    try:\n        len(1)\n    except TypeError:\n        return 9\n",
            "    import math as TypeError\n"
            "    try:\n        len(1)\n    except TypeError:\n        return 9\n",
            "    for TypeError in [1]:\n        pass\n"
            "    try:\n        len(1)\n    except TypeError:\n        return 9\n",
            "    with value as TypeError:\n        pass\n"
            "    try:\n        len(1)\n    except TypeError:\n        return 9\n",
            "    if (TypeError := 1):\n        pass\n"
            "    try:\n        len(1)\n    except TypeError:\n        return 9\n",
        )
        for body in bodies:
            with self.subTest(body=body):
                fn = self._first_fn("def f():\n" + body)
                self.assertEqual(
                    fn["locals_unsupported"],
                    "matches locally-bound handler name(s) "
                    "(static-locals rule): TypeError")

    def test_handler_parameter_binding_refuses(self):
        for params in ("TypeError", "TypeError, /", "*, TypeError",
                       "*TypeError", "**TypeError"):
            with self.subTest(params=params):
                fn = self._first_fn(
                    "def f(" + params + "):\n    try:\n        len(1)\n"
                    "    except TypeError:\n        return 9\n")
                self.assertIn("locally-bound handler", fn["locals_unsupported"])

    def test_handler_guard_preserves_existing_local_refusal_precedence(self):
        fn = self._first_fn(
            "def f():\n    del TypeError\n    try:\n        len(1)\n"
            "    except TypeError:\n        return 9\n")
        self.assertIn("reads del'd name(s)", fn["locals_unsupported"])
        fn = self._first_fn(
            "def f():\n    len(1)\n    len = 2\n    try:\n        len(1)\n"
            "    except TypeError:\n        return 9\n    TypeError = 1\n")
        self.assertEqual(
            fn["locals_unsupported"],
            "calls locally-assigned name(s) (static-locals rule): len")

    def test_handler_guard_does_not_cross_nested_scopes(self):
        fn = self._first_fn(
            "def f():\n    def helper(TypeError):\n        TypeError = 1\n"
            "    try:\n        len(1)\n    except TypeError:\n        return 9\n")
        self.assertIsNone(fn["locals_unsupported"])
        fn = self._first_fn(
            "def f(TypeError):\n    def helper():\n        try:\n"
            "            len(1)\n        except TypeError:\n            return 9\n"
            "    return 0\n")
        self.assertIsNone(fn["locals_unsupported"])

    def test_handler_rebinding_oracle_reproductions(self):
        rows = (
            ("def f():\n    try:\n        TypeError = 1\n        len(1)\n"
             "    except TypeError:\n        return 9\n", TypeError),
            ("def f():\n    try:\n        TypeError = 1\n        1 // 0\n"
             "    except TypeError:\n        return 9\n", TypeError),
            ("def f():\n    try:\n        len(1)\n"
             "    except TypeError:\n        return 9\n    TypeError = 1\n",
             UnboundLocalError),
        )
        for source, exception in rows:
            with self.subTest(source=source):
                namespace = {}
                exec(source, namespace)
                with self.assertRaises(exception):
                    namespace["f"]()
                self.assertIn("locally-bound handler",
                              self._first_fn(source)["locals_unsupported"])

    def test_module_handler_rebinding_refuses_before_static_matching(self):
        sources = (
            "try:\n    TypeError = 1\n    len(1)\n"
            "except TypeError:\n    pass\n",
            "try:\n    while True:\n        TypeError = 1\n        len(1)\n"
            "    else:\n        pass\nexcept TypeError:\n    pass\n",
            "try:\n    def TypeError():\n        pass\n    len(1)\n"
            "except TypeError:\n    pass\n",
        )
        for source in sources:
            with self.subTest(source=source):
                stmt = self._envelope_of(source)["module"]["body"][0]
                self.assertEqual(stmt["try_unsupported"],
                                 "handler name rebound in try body: TypeError")

    def test_module_handler_rebinding_guard_stays_scope_local(self):
        stmt = self._envelope_of(
            "try:\n    def helper(TypeError):\n        TypeError = 1\n"
            "    len(1)\nexcept TypeError:\n    pass\n"
        )["module"]["body"][0]
        self.assertIsNone(stmt["try_unsupported"])


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

    def test_starred_assignment_target_has_dedicated_statement(self):
        env = self._envelope_of(
            "def f(xs):\n    a, *middle, z = xs\n    return a, middle, z\n")
        st = env["module"]["body"][0]["body"][0]
        self.assertEqual(st["kind"], "UnpackAssign")
        self.assertEqual(st["before"], ["a"])
        self.assertEqual(st["star"], "middle")
        self.assertEqual(st["after"], ["z"])
        self.assertEqual(st["value"]["kind"], "Name")

    def test_starred_assignment_target_rejects_non_names_and_multiple_stars(self):
        for source in (
                "def f(xs):\n    a, *middle, obj.x = xs\n",
                "def f(xs):\n    a, *middle, xs[0] = xs\n",
                "def f(xs):\n    a, *b, *c = xs\n"):
            with self.subTest(source=source):
                st = self._envelope_of(source)["module"]["body"][0]["body"][0]
                self.assertEqual(st["kind"], "Unsupported")
                self.assertEqual(st["py_kind"], "Starred:target")

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

    def test_module_annotation_with_value_splices_assignment_then_annotation(self):
        env = self._envelope_of(
            "x: 1 = 1\n"
            "if True:\n"
            "    y: 2 = 2\n")
        body = env["module"]["body"]
        self.assertEqual([st["kind"] for st in body], ["Assign", "Expr", "If"])
        self.assertEqual(body[0]["targets"][0]["id"], "x")
        self.assertEqual(body[1]["value"]["kind"], "Constant")
        self.assertEqual([st["kind"] for st in body[2]["body"]],
                         ["Assign", "Expr"])

    def test_module_annotations_flatten_in_compound_statement_bodies(self):
        for source, branches in (
                ("if True:\n    x: 1 = 7\nelse:\n    x: 2 = 8\n",
                 ("body", "orelse")),
                ("while False:\n    x: 1 = 7\nelse:\n    x: 2 = 8\n",
                 ("body", "orelse")),
                ("for index in []:\n    x: 1 = 7\nelse:\n    x: 2 = 8\n",
                 ("body", "orelse")),
                ("try:\n    x: 1 = 7\nexcept ValueError:\n    x: 2 = 8\n",
                 ("body", "handler"))):
            with self.subTest(source=source):
                statement = self._envelope_of(source)["module"]["body"][0]
                for branch in branches:
                    body = statement[branch]
                    self.assertEqual([item["kind"] for item in body],
                                     ["Assign", "Expr"])
                    self.assertEqual(body[0]["targets"][0]["id"], "x")
                    self.assertEqual(body[1]["value"]["kind"], "Constant")
                    self.assertEqual(body[1]["value"]["value"]["type"], "int")
                    self.assertIn(body[1]["value"]["value"]["repr"], ("1", "2"))

    def test_module_annotation_calls_are_loud_after_value_store(self):
        source = (
            "events = []\n"
            "def value():\n    events.append('value')\n    return 7\n"
            "def annotation(value):\n    events.append(value)\n    return 9\n"
            "x: annotation(x) = value()\n")
        namespace = {}
        exec(compile(source, "<annotation-order>", "exec"), namespace)
        self.assertEqual(namespace["events"], ["value", 7])
        self.assertEqual(namespace["x"], 7)
        self.assertEqual(namespace["__annotations__"], {"x": 9})
        body = self._envelope_of(source)["module"]["body"]
        self.assertEqual(body[-1]["kind"], "Expr")
        self.assertEqual(body[-1]["value"]["kind"], "Call")

    def test_module_scalar_annotations_preserve_rhs_evaluation_order(self):
        for annotation, value, kind in (("'tag'", "tag", "str"),
                                        ("42", 42, "int"),
                                        ("True", True, "bool"),
                                        ("False", False, "bool"),
                                        ("None", None, "none")):
            with self.subTest(annotation=annotation):
                source = (
                    "events = []\n"
                    "def value():\n    events.append('value')\n    return 7\n"
                    "x: " + annotation + " = value()\n")
                namespace = {}
                exec(compile(source, "<scalar-annotation>", "exec"), namespace)
                self.assertEqual(namespace["events"], ["value"])
                self.assertEqual(namespace["x"], 7)
                self.assertEqual(namespace["__annotations__"], {"x": value})
                body = self._envelope_of(source)["module"]["body"]
                self.assertEqual([item["kind"] for item in body[-2:]],
                                 ["Assign", "Expr"])
                self.assertEqual(body[-2]["targets"][0]["id"], "x")
                self.assertEqual(body[-2]["value"]["func"]["id"], "value")
                self.assertEqual(body[-1]["value"]["kind"], "Constant")
                self.assertEqual(body[-1]["value"]["value"]["type"], kind)

    def test_module_annotation_expressions_run_after_value_store(self):
        for annotation in ("x", "boom()", "1 // 0", "[1]", "(1,)",
                           "{1: 1}", "1.5", "1j", "-1"):
            with self.subTest(annotation=annotation):
                source = ("x: " + annotation + " = 3\n"
                          "def f():\n    return x\n")
                body = self._envelope_of(source)["module"]["body"]
                self.assertEqual([item["kind"] for item in body[:2]],
                                 ["Assign", "Expr"])
        namespace = {}
        with self.assertRaises(ZeroDivisionError):
            exec("x: (1 // 0) = 3\n", namespace)
        self.assertEqual(namespace["x"], 3)

    def test_module_builtin_type_annotation_is_a_plain_assignment(self):
        body = self._envelope_of("x: int = 3\nprint(x)\n")["module"]["body"]
        self.assertEqual([item["kind"] for item in body], ["Assign", "Expr"])
        self.assertEqual(body[0]["targets"][0]["id"], "x")

    def test_module_shadowed_builtin_annotation_is_evaluated(self):
        body = self._envelope_of("int = 7\nx: int = 3\n")["module"]["body"]
        self.assertEqual([item["kind"] for item in body[1:]],
                         ["Assign", "Expr"])

    def test_function_annotations_stay_erased_in_compound_bodies(self):
        fn = self._first_fn(
            "def f():\n"
            "    x: boom() = 1\n"
            "    if True:\n        x: boom() = 2\n"
            "    while False:\n        x: boom() = 3\n"
            "    for index in []:\n        x: boom() = 4\n"
            "    try:\n        x: boom() = 5\n"
            "    except ValueError:\n        x: boom() = 6\n"
            "    return x\n")
        self.assertEqual([item["kind"] for item in fn["body"]],
                         ["Assign", "If", "While", "For", "Try", "Return"])
        for statement in fn["body"][1:5]:
            self.assertEqual([item["kind"] for item in statement["body"]],
                             ["Assign"])
        self.assertEqual([item["kind"] for item in fn["body"][4]["handler"]],
                         ["Assign"])
        self.assertNotIn("boom", json.dumps(fn))

    def test_statement_flattening_preserves_direct_closure_recognition(self):
        fn = self._first_fn(
            "def outer():\n"
            "    base: boom() = 7\n"
            "    callback = lambda: base\n"
            "    def nested():\n        return base\n"
            "    return callback() + nested()\n")
        self.assertEqual([item["kind"] for item in fn["body"]],
                         ["Assign", "NestedDef", "NestedDef", "Return"])
        for statement in fn["body"][1:3]:
            self.assertEqual(statement["captures"], ["base"])
            self.assertIsNone(statement["closure_unsupported"])
        self.assertEqual(fn["body"][1]["name"], "callback")
        self.assertEqual(fn["body"][2]["name"], "nested")

    def test_annotation_refusal_shapes_remain_unsupported(self):
        for source, reason in (
                ("(x): int = 7\n", "AnnAssign:non-simple-target"),
                ("obj.attr: int = 7\n", "AnnAssign:non-simple-target"),
                ("items[0]: int = 7\n", "AnnAssign:non-simple-target")):
            with self.subTest(source=source):
                statement = self._envelope_of(source)["module"]["body"][0]
                self.assertEqual(statement["kind"], "Unsupported")
                self.assertEqual(statement["py_kind"], reason)
                local = self._first_fn("def f():\n    " + source)["body"][0]
                self.assertEqual(local["kind"], "Unsupported")
                self.assertEqual(local["py_kind"], reason)
        module = self._envelope_of("x: int\n")["module"]["body"][0]
        self.assertEqual(module["kind"], "Unsupported")
        self.assertEqual(module["py_kind"], "AnnAssign:no-value")
        local = self._first_fn("def f():\n    x: int\n    return 1")
        self.assertEqual(local["body"][0]["kind"], "Pass")
        local_read = self._first_fn("def f():\n    x: int\n    return x")
        self.assertEqual(local_read["body"][0]["kind"], "Unsupported")
        self.assertEqual(local_read["body"][0]["py_kind"],
                         "AnnAssign:no-value")
        cls = self._envelope_of("class C:\n    x: int = 7\n")["module"]["body"][0]
        self.assertEqual(cls["body"][0]["kind"], "Unsupported")
        self.assertEqual(cls["body"][0]["py_kind"], "AnnAssign:module-scope")

    def test_module_annotation_explicit_table_bindings_refuse(self):
        for source, count in (
                ("__annotations__ = None\nx: 1 = 7\n", 1),
                ("table = {}\n__annotations__ = table\nx: 1 = 7\n", 1),
                ("__annotations__: 1 = {}\nx: 1 = 7\n", 2),
                ("x: 1 = 7\ndel __annotations__\n", 1),
                ("def f(__annotations__):\n    return 1\nx: 1 = 7\n", 1)):
            with self.subTest(source=source):
                body = self._envelope_of(source)["module"]["body"]
                refused = [item for item in body
                           if item["kind"] == "Unsupported"]
                self.assertEqual(len(refused), count)
                self.assertEqual([item["py_kind"] for item in refused],
                                 ["AnnAssign:annotations-bound"] * count)
        body = self._envelope_of("x: 1 = 7\n")["module"]["body"]
        self.assertEqual([item["kind"] for item in body], ["Assign", "Expr"])

    def test_module_annotation_shared_empty_table_updates_through_alias(self):
        body = self._envelope_of(
            "__annotations__ = table = {}\n"
            "x: 'int' = 7\n")["module"]["body"]
        self.assertEqual([item["kind"] for item in body],
                         ["Assign", "Assign", "Assign"])
        store = body[2]
        self.assertEqual(store["targets"][0]["kind"], "Subscript")
        self.assertEqual(store["targets"][0]["value"]["id"],
                         "__annotations__")
        self.assertEqual(store["targets"][0]["index"]["value"],
                         {"type": "str", "value": "x"})

    def test_function_annotation_erasure_ignores_bound_annotation_table(self):
        for binding in ("__annotations__ = None\n",
                        "table = {}\n__annotations__ = table\n",
                        "__annotations__: 1 = {}\n",
                        "del __annotations__\n"):
            with self.subTest(binding=binding):
                env = self._envelope_of(
                    binding + "def f():\n    x: boom() = 7\n    return x\n")
                fn = env["module"]["body"][-1]
                self.assertEqual([item["kind"] for item in fn["body"]],
                                 ["Assign", "Return"])
                self.assertEqual(fn["body"][0]["targets"][0]["id"], "x")
                self.assertNotIn("boom", json.dumps(fn))


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

    def test_set_display_lowers_to_existing_set_constructor(self):
        e = self._first_return_expr("def f(a):\n    return {1, True, a}\n")
        self.assertEqual(e["kind"], "Call")
        self.assertEqual(e["func"]["kind"], "Name")
        self.assertEqual(e["func"]["id"], "set")
        self.assertEqual(e["args"][0]["kind"], "List")
        self.assertEqual(len(e["args"][0]["elts"]), 3)

    def test_set_display_unpack_stays_unsupported(self):
        e = self._first_return_expr("def f(xs):\n    return {*xs}\n")
        self.assertEqual(e["kind"], "Unsupported")
        self.assertEqual(e["py_kind"], "Set:unpack")

    def test_set_comprehension_lowers_to_set_generator(self):
        e = self._first_return_expr(
            "def f(xs):\n    return {x + 1 for x in xs if x > 0}\n")
        self.assertEqual(e["kind"], "Call")
        self.assertEqual(e["func"]["id"], "set")
        self.assertEqual(e["args"][0]["kind"], "GeneratorExp")

    def test_dict_comprehension_lowers_to_dict_generator(self):
        e = self._first_return_expr(
            "def f(xs):\n    return {x: x + 1 for x in xs}\n")
        self.assertEqual(e["kind"], "Call")
        self.assertEqual(e["func"]["id"], "dict")
        self.assertEqual(e["args"][0]["kind"], "GeneratorExp")

    def test_dict_comprehension_shadow_stays_unsupported(self):
        env = self._envelope_of(
            "dict = 0\n"
            "def f(xs):\n    return {x: x for x in xs}\n")
        e = env["module"]["body"][1]["body"][0]["value"]
        self.assertEqual(e["kind"], "Unsupported")
        self.assertEqual(e["py_kind"], "DictComp:shadowed")

    def test_matmul_is_structured(self):
        e = self._first_return_expr("def f(a, b):\n    return a @ b\n")
        self.assertEqual(e["kind"], "BinOp")
        self.assertEqual(e["op"], "MatMult")

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

    def test_slots_accept_literal_string_tuple_and_list(self):
        for source, expected in (
                ("class C:\n    __slots__ = 'x'\n", ["x"]),
                ("class C:\n    __slots__ = ('x', 'y')\n", ["x", "y"]),
                ("class C:\n    __slots__ = ['x', 'y']\n", ["x", "y"]),
                ("class C:\n    __slots__ = ()\n", [])):
            with self.subTest(source=source):
                c = self._module_body(source)[0]
                self.assertEqual(c.get("slots"), expected)
                self.assertIsNone(c["class_unsupported"])
                self.assertFalse(c["creation_effects"])

    def test_slots_reject_duplicate_and_repeated_declarations(self):
        for source in (
                "class C:\n    __slots__ = ('x', 'x')\n",
                "class C:\n    __slots__ = ('x',)\n"
                "    __slots__ = ('y',)\n"):
            with self.subTest(source=source):
                c = self._module_body(source)[0]
                self.assertNotIn("slots", c)
                self.assertIn("class-level statements", c["class_unsupported"])
                self.assertTrue(c["creation_effects"])

    def test_slots_reject_nonliteral_or_nonstring_values(self):
        for source in (
                "names = ('x',)\nclass C:\n    __slots__ = names\n",
                "class C:\n    __slots__ = [1]\n",
                "class C:\n    __slots__ = ('x-y',)\n",
                "class C:\n    __slots__ = ''\n"):
            with self.subTest(source=source):
                c = self._module_body(source)[-1]
                self.assertNotIn("slots", c)
                self.assertIn("class-level statements", c["class_unsupported"])
                self.assertTrue(c["creation_effects"])

    # -- THE THIRD DOOR (docs/memory-model.md §class semantics): a
    # DECORATED method is a creation EFFECT. CPython calls the decorator
    # at the `class` statement; the model executes no class body, so
    # skipping it would print nothing where CPython prints.

    def test_undecorated_methods_keep_creation_pure(self):
        body = self._module_body(
            "class C:\n"
            "    'doc'\n"
            "    def __init__(self): pass\n"
            "    def get(self): return 1\n")
        self.assertFalse(body[0]["creation_effects"])

    def test_decorated_method_is_a_creation_effect(self):
        body = self._module_body(
            "class C:\n"
            "    @log\n"
            "    def m(self): pass\n")
        self.assertTrue(body[0]["creation_effects"])
        self.assertTrue(body[0]["body"][0]["has_decorators"])

    def test_property_is_a_creation_effect_too(self):
        # every one of the 15 stdlib classes the census found decorates
        # with property/setter/classmethod/staticmethod, which happen to
        # have no observable effect -- lucky, not sound, so they refuse.
        body = self._module_body(
            "class C:\n"
            "    @property\n"
            "    def x(self): return 1\n")
        self.assertTrue(body[0]["creation_effects"])

    def test_argument_shapes_are_NOT_creation_effects(self):
        # PRECISION: `args_unsupported` mixes "decorators" with
        # "*args"/"**kwargs"/"defaults". Only the decorator is an effect,
        # which is why ingestion reads the structured `has_decorators`
        # flag and never matches on that message.
        body = self._module_body(
            "class C:\n"
            "    def m(self, *rest, **kw): pass\n")
        self.assertFalse(body[0]["creation_effects"])
        m = body[0]["body"][0]
        self.assertIn("*args", m["args_unsupported"])
        self.assertNotIn("has_decorators", m)

    def test_undecorated_function_has_no_decorator_flag(self):
        body = self._module_body("def f(x): return x\n")
        self.assertNotIn("has_decorators", body[0])


class ImportFromTests(unittest.TestCase):
    # -- Pass 0 (docs/memory-model.md paragraph "Import forms (Pass 0)"):
    # the extractor structures EXACTLY the admitted shape; everything
    # else keeps the Unsupported fallthrough verbatim, because five
    # text-keyed consumers depend on that shape for still-refused
    # imports. `zzz_no_such_module` is the inventory-absent probe;
    # `binascii` / `_bisect` are platform-present (in the committed
    # inventory), so their unguarded forms must stay Unsupported.

    def _module_body(self, source):
        import ast
        return [extract.convert_stmt(st, module_scope=True)
                for st in ast.parse(source).body]

    def _try_body(self, source):
        """The converted DIRECT body of a module-level try statement."""
        return self._module_body(source)[0]["body"]

    def test_guarded_star_of_admitted_accelerator_is_structured(self):
        # bisect.py 73-76, the census's one program-mode flip -- and the
        # ONE accelerator whose equivalence has been measured (15/15)
        s = self._try_body(
            "try:\n"
            "    from _bisect import *\n"
            "except ImportError:\n"
            "    pass\n")[0]
        self.assertEqual(s["kind"], "ImportFrom")
        self.assertEqual(s["module"], "_bisect")
        self.assertEqual(s["names"], [])
        self.assertIs(s["star"], True)

    def test_second_try_body_statement_is_also_guarded(self):
        # guard position is "direct body statement", never "sole
        # statement" (opcode.py 18-21 is the shape; _bisect is used here
        # because the shape question is separate from the registry one)
        body = self._try_body(
            "try:\n"
            "    from _bisect import *\n"
            "    x = 1\n"
            "except ImportError:\n"
            "    pass\n")
        self.assertEqual(body[0]["kind"], "ImportFrom")
        self.assertEqual(body[1]["kind"], "Assign")

    # -- The 2.5 ACCELERATOR-EQUIVALENCE REGISTRY (2026-08-16). Guard
    # position is necessary and NO LONGER SUFFICIENT: the fallback branch
    # runs where CPython ran C, so the admission asserts the two branches
    # agree, and that assertion now needs a recorded measurement. The
    # refusal says WHICH of the two failures it is.

    def test_guarded_unmeasured_accelerator_refuses_by_name(self):
        # quopri.py 14-18: a genuine pure-accel fallback (`if b2a_qp is
        # not None: ... else: <pure python>`) whose equivalence nobody
        # has ever driven -- quopri walls on bytes long before it runs
        s = self._try_body(
            "try:\n"
            "    from binascii import a2b_qp, b2a_qp\n"
            "except ImportError:\n"
            "    a2b_qp = None\n"
            "    b2a_qp = None\n")[0]
        self.assertEqual(s["kind"], "Unsupported")
        self.assertEqual(s["py_kind"], "ImportFrom:accelerator-unmeasured")
        self.assertEqual(s["text"], "from binascii import a2b_qp, b2a_qp")

    def test_guarded_diverging_accelerator_refuses_under_its_own_name(self):
        # stat.py 192-195: MEASURED non-equivalent, 21 of 104 calls
        s = self._try_body(
            "try:\n"
            "    from _stat import *\n"
            "except ImportError:\n"
            "    pass\n")[0]
        self.assertEqual(s["kind"], "Unsupported")
        self.assertEqual(s["py_kind"], "ImportFrom:accelerator-diverges")

    def test_opcode_binds_a_name_the_fallback_does_not(self):
        # opcode.py 18-21: the branches differ by INSPECTION -- CPython
        # binds `stack_effect`, the `pass` handler binds nothing
        body = self._try_body(
            "try:\n"
            "    from _opcode import stack_effect\n"
            "    x = 1\n"
            "except ImportError:\n"
            "    pass\n")
        self.assertEqual(body[0]["kind"], "Unsupported")
        self.assertEqual(body[0]["py_kind"], "ImportFrom:accelerator-diverges")

    def test_guarded_absent_module_needs_no_registry_entry(self):
        # the raise is CPython's OWN behavior, so there is no fallback
        # branch to assert anything about
        s = self._try_body(
            "try:\n"
            "    from zzz_no_such_module import *\n"
            "except ImportError:\n"
            "    pass\n")[0]
        self.assertEqual(s["kind"], "ImportFrom")

    def test_every_registry_entry_carries_its_evidence(self):
        # an admission whose evidence is not written down is the thing
        # this registry exists to prevent
        for mod, rec in extract.ACCELERATOR_ADMISSIONS.items():
            self.assertIsInstance(rec["equivalent"], bool, mod)
            self.assertTrue(rec["fallback"].strip(), mod)
            self.assertGreater(len(rec["evidence"].strip()), 40, mod)
            self.assertIn(mod, extract.platform_inventory())

    def test_unguarded_absent_module_is_structured(self):
        # CPython's own ModuleNotFoundError -- admitted anywhere at top
        # level, guarded or not
        s = self._module_body("from zzz_no_such_module import x\n")[0]
        self.assertEqual(s["kind"], "ImportFrom")
        self.assertEqual(s["module"], "zzz_no_such_module")
        self.assertEqual(s["names"], ["x"])

    def test_unguarded_absent_star_is_structured(self):
        s = self._module_body("from zzz_no_such_module import *\n")[0]
        self.assertEqual(s["kind"], "ImportFrom")
        self.assertIs(s["star"], True)

    def test_unguarded_present_module_stays_unsupported(self):
        # CPython SUCCEEDS here; a surfaced ImportError would be a
        # wrong answer, so outside the guard it refuses loudly
        s = self._module_body("from binascii import a2b_qp\n")[0]
        self.assertEqual(s["kind"], "Unsupported")
        self.assertEqual(s["py_kind"], "ImportFrom")
        self.assertEqual(s["text"], "from binascii import a2b_qp")

    def test_nested_in_try_body_if_is_not_guard_position(self):
        # only DIRECT body statements are caught by construction
        body = self._try_body(
            "try:\n"
            "    if 1:\n"
            "        from binascii import a2b_qp\n"
            "except ImportError:\n"
            "    pass\n")
        inner = body[0]["body"][0]
        self.assertEqual(inner["kind"], "Unsupported")
        self.assertEqual(inner["py_kind"], "ImportFrom")

    def test_wrong_handler_class_is_not_a_guard(self):
        body = self._try_body(
            "try:\n"
            "    from binascii import a2b_qp\n"
            "except OSError:\n"
            "    pass\n")
        self.assertEqual(body[0]["kind"], "Unsupported")

    def test_relative_imports_stay_unsupported(self):
        for src in ("from . import x\n", "from .foo import x\n"):
            s = self._module_body(src)[0]
            self.assertEqual(s["kind"], "Unsupported")
            self.assertEqual(s["py_kind"], "ImportFrom")

    def test_dotted_module_stays_unsupported_even_guarded(self):
        body = self._try_body(
            "try:\n"
            "    from os.path import join\n"
            "except ImportError:\n"
            "    pass\n")
        self.assertEqual(body[0]["kind"], "Unsupported")

    def test_alias_stays_unsupported_even_when_absent(self):
        s = self._module_body("from zzz_no_such_module import x as y\n")[0]
        self.assertEqual(s["kind"], "Unsupported")

    def test_function_body_import_stays_unsupported(self):
        # non-top-level: module_scope is False inside a def, guarded or
        # not -- the not_top_level battery row's static half
        import ast
        fn = ast.parse(
            "def f():\n"
            "    try:\n"
            "        from zzz_no_such_module import x\n"
            "    except ImportError:\n"
            "        pass\n").body[0]
        out = extract.convert_stmt(fn)
        inner = out["body"][0]["body"][0]
        self.assertEqual(inner["kind"], "Unsupported")
        self.assertEqual(inner["py_kind"], "ImportFrom")

    def test_plain_import_stays_unsupported(self):
        for src in ("import zzz_no_such_module\n", "import time\n"):
            s = self._module_body(src)[0]
            self.assertEqual(s["kind"], "Unsupported")
            self.assertEqual(s["py_kind"], "Import")

    def test_benign_whitelist_rows_are_structured(self):
        # canonicalized BACK to the legacy node at ingestion (Json.lean);
        # structured here so envelope-structured <=> admitted holds and
        # the survey's wall census needs zero code change
        for src, mod, name in (
                ("from itertools import count\n", "itertools", "count"),
                ("from collections import namedtuple\n", "collections",
                 "namedtuple")):
            s = self._module_body(src)[0]
            self.assertEqual(s["kind"], "ImportFrom")
            self.assertEqual(s["module"], mod)
            self.assertEqual(s["names"], [name])

    def test_top_level_if_body_is_module_scope(self):
        # module_scope threads through top-level if/for/while bodies
        # (the lambda-NestedDef precedent), so a guarded try inside a
        # top-level `if` still guards
        s = self._module_body(
            "if 1:\n"
            "    try:\n"
            "        from _bisect import *\n"
            "    except ImportError:\n"
            "        pass\n")[0]["body"][0]["body"][0]
        self.assertEqual(s["kind"], "ImportFrom")

    def test_inventory_probes(self):
        inv = extract.platform_inventory()
        for present in ("bisect", "_bisect", "binascii", "_stat",
                        "_opcode", "itertools", "collections"):
            self.assertIn(present, inv)
        self.assertNotIn("zzz_no_such_module", inv)


class DeleteTests(unittest.TestCase):
    """The del statement (docs/memory-model.md paragraph "the del
    statement" + docs/backlog.md paragraph "del RECONCILED"): bare-name
    targets structure at BOTH scopes; census clause 2 refuses any read
    of a del'd name; non-name targets keep the Unsupported fallthrough;
    a del counts as a binding for the closure rebound-after-def rule."""

    def _module_body(self, source):
        import ast
        return [extract.convert_stmt(st, module_scope=True)
                for st in ast.parse(source).body]

    def _first_fn(self, source):
        import ast
        return extract.convert_stmt(ast.parse(source).body[0])

    def test_function_scope_del_is_structured(self):
        fn = self._first_fn(
            "def f(n):\n    x = n\n    del x\n    return 0\n")
        self.assertIsNone(fn["locals_unsupported"])
        st = fn["body"][1]
        self.assertEqual(st["kind"], "Delete")
        self.assertEqual(st["names"], ["x"])

    def test_multi_target_del_keeps_order(self):
        fn = self._first_fn(
            "def f(n):\n    x = n\n    y = n\n    del x, y\n    return 0\n")
        self.assertEqual(fn["body"][2]["names"], ["x", "y"])

    def test_del_of_parameter_is_in_tier(self):
        fn = self._first_fn("def f(n):\n    del n\n    return 0\n")
        self.assertIsNone(fn["locals_unsupported"])
        self.assertEqual(fn["body"][0]["kind"], "Delete")

    def test_read_after_del_refuses(self):
        fn = self._first_fn(
            "def f(n):\n    x = n\n    del x\n    return x\n")
        self.assertIn("del'd", fn["locals_unsupported"])
        self.assertIn("x", fn["locals_unsupported"])

    def test_rebind_after_del_refuses_the_stated_overrefusal(self):
        # CPython accepts this; the census refuses it (recorded price:
        # the read at `return x` intersects the del'd name set).
        fn = self._first_fn(
            "def f(n):\n    x = n\n    del x\n    x = 99\n    return x\n")
        self.assertIn("del'd", fn["locals_unsupported"])

    def test_conditional_del_without_read_is_in_tier(self):
        fn = self._first_fn(
            "def f(n):\n    x = n\n    if n > 0:\n        del x\n"
            "    return 0\n")
        self.assertIsNone(fn["locals_unsupported"])

    def test_single_subscript_del_is_structured(self):
        # clause 4 widened (2026-08-23-pycomplete-15): `del d[k]` is
        # admitted syntactically; the evaluator decides the receiver type.
        fn = self._first_fn(
            "def f(d, o):\n    del d['k']\n    return 0\n")
        self.assertEqual(fn["body"][0]["kind"], "DeleteSubscript")
        self.assertEqual(fn["body"][0]["recv"]["kind"], "Name")

    def test_slice_attribute_and_mixed_del_stay_unsupported(self):
        for src in ("def f(xs):\n    del xs[1:]\n    return 0\n",
                    "def f(o):\n    del o.attr\n    return 0\n",
                    "def f(d, e):\n    del d['k'], e['k']\n    return 0\n"):
            fn = self._first_fn(src)
            self.assertEqual(fn["body"][0]["kind"], "Unsupported", src)
            self.assertEqual(fn["body"][0]["py_kind"], "Delete", src)

    def test_module_scope_del_is_structured(self):
        # the REVISED clause 3: module scope structures; the runtime
        # admission is the script executor's (docs/backlog.md paragraph
        # "del RECONCILED with the one pipeline")
        body = self._module_body("b = 5\ndel b\n")
        self.assertEqual(body[1]["kind"], "Delete")
        self.assertEqual(body[1]["names"], ["b"])

    def test_del_counts_as_binding_for_closures(self):
        # a capture DELETED after the def is a rebind (`_binding_linenos`
        # and `_assigned_names` agree), so it cells rather than snapshots
        fn = self._first_fn(
            "def outer(a):\n    def f():\n        return a\n"
            "    del a\n    return 0\n")
        nd = fn["body"][0]
        self.assertEqual(nd["kind"], "NestedDef")
        self.assertIsNone(nd["closure_unsupported"])
        self.assertEqual(nd["captures"], ["<cell>a"])

    def test_del_shadowed_call_refuses(self):
        # clause 1 makes the del'd name local, so calling it takes the
        # static-locals refusal channel (the hazard's third instance)
        fn = self._first_fn(
            "def f():\n    del g\n    return g()\n")
        self.assertIsNotNone(fn["locals_unsupported"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
