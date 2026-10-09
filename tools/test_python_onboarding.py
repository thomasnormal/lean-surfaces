#!/usr/bin/env python3
"""Protect the Python quickstart's source-level dependency boundary.

Run ``python3 tools/test_python_onboarding.py`` without building Lean or
installing Python packages. The selected examples may transitively import only
local Core, Python, and Python-example modules, plus Lean's Init/Lean/Std
libraries. The header reader handles nested comments and ordinary qualified
module identifiers; unsupported import spellings fail rather than disappear.
"""

from __future__ import annotations

import pathlib
import re
import tempfile
import unittest
from typing import Iterator


REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
EXAMPLES = (
    "Examples.python.tri.spec",
    "Examples.python.tut_01.spec",
    "Examples.python.tut_02.spec",
    "Examples.python.tut_03.spec",
    "Examples.python.tut_04.spec",
    "Examples.python.tut_05.spec",
    "Examples.python.tut_06.spec",
)
LOCAL_PREFIXES = ("LeanModels.Core", "LeanModels.Python", "Examples.python")
EXTERNAL_ROOTS = frozenset(("Init", "Lean", "Std"))
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
DECLARATION_STARTERS = frozenset(
    (
        "namespace", "section", "end", "open", "export", "universe",
        "universes", "variable", "variables", "set_option", "attribute",
        "def", "abbrev", "opaque", "theorem", "lemma", "example", "axiom",
        "constant", "constants", "inductive", "coinductive", "structure",
        "class", "instance", "noncomputable", "unsafe", "partial", "private",
        "protected", "mutual", "syntax", "macro", "macro_rules", "elab",
        "elab_rules", "initialize", "builtin_initialize", "deriving", "infix",
        "infixl", "infixr", "prefix", "postfix", "notation", "local",
        "scoped", "declare_syntax_cat",
    )
)


class DependencyError(ValueError):
    """A header cannot be read or its closure violates the tier boundary."""


def skip_block_comment(source: str, position: int) -> int:
    """Skip a Lean block comment, whose delimiters nest even inside prose."""
    depth = 1
    position += 2
    while position < len(source):
        if source.startswith("/-", position):
            depth += 1
            position += 2
        elif source.startswith("-/", position):
            depth -= 1
            position += 2
            if depth == 0:
                return position
        else:
            position += 1
    raise DependencyError("unterminated block comment in Lean import header")


def skip_layout(source: str, position: int) -> int:
    """Skip whitespace and comments without reading declaration bodies."""
    while position < len(source):
        if source[position].isspace():
            position += 1
        elif source.startswith("--", position):
            newline = source.find("\n", position)
            position = len(source) if newline == -1 else newline + 1
        elif source.startswith("/-", position):
            position = skip_block_comment(source, position)
        else:
            return position
    return position


def header_tokens(source: str) -> Iterator[str]:
    """Yield tokens lazily so scanning stops at the first declaration."""
    position = 0
    while position < len(source):
        position = skip_layout(source, position)
        start = position
        while (
            position < len(source)
            and not source[position].isspace()
            and not source.startswith("--", position)
            and not source.startswith("/-", position)
        ):
            position += 1
        if position > start:
            yield source[start:position]


def read_imports(source: str) -> list[str]:
    """Read ordinary import headers, including multi-module import commands."""
    imports = []
    importing = False
    needs_module = False
    for token in header_tokens(source):
        if token in DECLARATION_STARTERS or token.startswith("#"):
            break
        if token in ("module", "prelude", "public", "meta"):
            continue
        if token == "import":
            if needs_module:
                raise DependencyError("import command has no module name")
            importing = True
            needs_module = True
            continue
        if not importing:
            break
        if not MODULE_NAME.fullmatch(token):
            raise DependencyError("unsupported Lean import token: {!r}".format(token))
        imports.append(token)
        needs_module = False
    if needs_module:
        raise DependencyError("import command has no module name")
    return imports


def module_path(root: pathlib.Path, module: str) -> pathlib.Path:
    """Resolve a qualified local module to its source file."""
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def allowed_local_module(module: str) -> bool:
    """Match namespace components, not similarly named foreign-tier roots."""
    return any(module == prefix or module.startswith(prefix + ".") for prefix in LOCAL_PREFIXES)


def python_only_closure(root: pathlib.Path, entry: str) -> set[str]:
    """Traverse actual source imports; the visited set only terminates cycles."""
    pending = [(entry, (entry,))]
    visited = set()
    while pending:
        module, chain = pending.pop()
        if module in visited:
            continue
        source_path = module_path(root, module)
        namespace = module.split(".")[0]
        local_root = (root / namespace).is_dir() or (root / (namespace + ".lean")).is_file()
        if namespace in EXTERNAL_ROOTS and not local_root and not source_path.is_file():
            continue
        import_chain = " -> ".join(chain)
        if not allowed_local_module(module):
            raise DependencyError("Python-only dependency leakage: " + import_chain)
        if not source_path.is_file():
            raise DependencyError("missing local module {}: {} ({})".format(module, source_path, import_chain))
        visited.add(module)
        try:
            imports = read_imports(source_path.read_text(encoding="utf-8"))
        except DependencyError as error:
            raise DependencyError("{}: {} ({})".format(source_path, error, import_chain)) from error
        pending.extend((imported, chain + (imported,)) for imported in imports)
    return visited


class HeaderTests(unittest.TestCase):
    def test_nested_comments_hide_imports(self):
        source = "/- import LeanModels.C /- nested -/ still hidden -/\nimport LeanModels.Python\n"
        self.assertEqual(read_imports(source), ["LeanModels.Python"])

    def test_line_comments_hide_imports_and_block_openers(self):
        source = "-- import LeanModels.Sv /-\nimport Lean -- /- not a block\nimport Std\n"
        self.assertEqual(read_imports(source), ["Lean", "Std"])

    def test_multiple_imports_and_inline_comments(self):
        source = "import LeanModels.Core.Basic/- ignored -/ LeanModels.Python.Ast\nimport Lean\n"
        self.assertEqual(read_imports(source), ["LeanModels.Core.Basic", "LeanModels.Python.Ast", "Lean"])

    def test_multiline_import_command(self):
        self.assertEqual(read_imports("import\n  Lean\n  Std\nnamespace Test\n"), ["Lean", "Std"])

    def test_module_header_with_public_and_meta_imports(self):
        source = "module\nprelude\npublic import Lean\npublic meta import Std\n"
        self.assertEqual(read_imports(source), ["Lean", "Std"])

    def test_declaration_bodies_are_not_scanned(self):
        source = 'import Lean\ndef value := "import LeanModels.C /-"\n/- unterminated body comment'
        self.assertEqual(read_imports(source), ["Lean"])

    def test_quoted_identifiers_fail_loudly(self):
        with self.assertRaisesRegex(DependencyError, "unsupported Lean import token"):
            read_imports("import LeanModels.«foreign-tier»\n")

    def test_unterminated_header_comment_fails(self):
        with self.assertRaisesRegex(DependencyError, "unterminated block comment"):
            read_imports("/- unclosed\nimport Lean\n")

    def test_empty_import_fails(self):
        for source in ("import", "import\nimport Lean", "import\nnamespace Test"):
            with self.subTest(source=source):
                with self.assertRaisesRegex(DependencyError, "no module name"):
                    read_imports(source)


class ClosureTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="python-onboarding-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)

    def write_module(self, module: str, source: str):
        source_path = module_path(self.root, module)
        source_path.parent.mkdir(parents=True, exist_ok=True)
        source_path.write_text(source, encoding="utf-8")

    def test_transitive_foreign_tier_fails(self):
        self.write_module("Examples.python.start", "import LeanModels.Python.Middle\n")
        self.write_module("LeanModels.Python.Middle", "import LeanModels.C.Semantics\n")
        self.write_module("LeanModels.C.Semantics", "namespace Foreign\n")
        with self.assertRaisesRegex(DependencyError, "Examples.python.start -> LeanModels.Python.Middle -> LeanModels.C.Semantics"):
            python_only_closure(self.root, "Examples.python.start")

    def test_cycles_terminate(self):
        self.write_module("Examples.python.start", "import LeanModels.Python.Middle\n")
        self.write_module("LeanModels.Python.Middle", "import Examples.python.start\n")
        self.assertEqual(
            python_only_closure(self.root, "Examples.python.start"),
            {"Examples.python.start", "LeanModels.Python.Middle"},
        )

    def test_missing_local_module_fails(self):
        self.write_module("Examples.python.start", "import LeanModels.Python.Missing\n")
        with self.assertRaisesRegex(DependencyError, "missing local module LeanModels.Python.Missing"):
            python_only_closure(self.root, "Examples.python.start")

    def test_core_external_imports_are_allowed(self):
        self.write_module("Examples.python.start", "import Init.Prelude Lean Std.Do\n")
        self.assertEqual(python_only_closure(self.root, "Examples.python.start"), {"Examples.python.start"})

    def test_mathlib_is_not_an_implicit_external_dependency(self):
        self.write_module("Examples.python.start", "import Mathlib.Data.Int.Basic\n")
        with self.assertRaisesRegex(DependencyError, "dependency leakage.*Mathlib.Data.Int.Basic"):
            python_only_closure(self.root, "Examples.python.start")

    def test_local_modules_cannot_hide_behind_external_names(self):
        self.write_module("Examples.python.start", "import Lean.Foreign\n")
        self.write_module("Lean.Foreign", "namespace Foreign\n")
        with self.assertRaisesRegex(DependencyError, "dependency leakage.*Lean.Foreign"):
            python_only_closure(self.root, "Examples.python.start")

    def test_allowed_prefixes_match_whole_namespace_components(self):
        self.write_module("Examples.python.start", "import LeanModels.PythonExtra\n")
        self.write_module("LeanModels.PythonExtra", "namespace Foreign\n")
        with self.assertRaisesRegex(DependencyError, "dependency leakage.*LeanModels.PythonExtra"):
            python_only_closure(self.root, "Examples.python.start")


class OnboardingTests(unittest.TestCase):
    def test_selected_example_closures_are_python_only(self):
        for module in EXAMPLES:
            with self.subTest(module=module):
                closure = python_only_closure(REPO_ROOT, module)
                print("Python onboarding: {}: {} local modules".format(module, len(closure)))


if __name__ == "__main__":
    unittest.main()
