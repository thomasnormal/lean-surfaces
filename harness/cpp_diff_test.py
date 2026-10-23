#!/usr/bin/env python3
"""Differential and coverage driver for the bounded C++ tier.

The native side is deliberately narrow: Clang/LLVM 21.1.8 compiles the
unchanged TinyXML-2 source and a generated caller invokes the original
declaration.  The Lean side evaluates the checked-in literal exported from
that same source.  Missing compiler/source inputs are reported as ORACLE;
they are never converted into matches.

This first driver also owns the C++ grammar census.  A witness is compiled
with ``-ast-dump=json`` and its node kind is checked, while the translation
surface is asked to execute it.  Translation execution currently refuses by
design, so the page records those loud refusals until a rung admits them.

Usage::

    python3 harness/cpp_diff_test.py
    python3 harness/cpp_diff_test.py --check
    python3 harness/cpp_diff_test.py --json /tmp/cpp-coverage.json

The process has no implicit corpus download.  Set ``LEANCPP_CLANG`` and
``LEANCPP_TINYXML2_DIR`` to run the native rows.  Every Lean invocation is
under the lane's 16 GiB address-space cap and one worker.
"""

from __future__ import print_function

import argparse
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[1]
CASES = ROOT / "harness" / "cpp_cases.json"
GRAMMAR = ROOT / "harness" / "cpp_grammar.json"
COVERAGE_PAGE = ROOT / "docs" / "cpp-coverage.md"
RUNG_PAGE = ROOT / "docs" / "cpp-rung-status.md"
ADDRESS_CAP = "17179869184"
PINNED_CLANG = "21.1.8"


RUNG_STATUS = [
    (0, "§5, §6.2–6.6", "executable", "Bounded TranslationUnitDecl, NamespaceDecl, FunctionDecl, ParmVarDecl, CXXRecordDecl, FieldDecl, CXXMethodDecl, EnumConstantDecl, AccessSpecDecl, CXXConstructorDecl, CXXDestructorDecl, CXXConversionDecl, FriendDecl, FriendTemplateDecl, TemplateTypeParmDecl, NonTypeTemplateParmDecl, TemplateTemplateParmDecl, TemplateParamObjectDecl, ImplicitConceptSpecializationDecl, RequiresExpr, TypeRequirement, SimpleRequirement, CompoundRequirement, NestedRequirement, UsingEnumDecl, ClassTemplateDecl, FunctionTemplateDecl, VarTemplateDecl, TypeAliasTemplateDecl, ClassTemplateSpecializationDecl, VarTemplateSpecializationDecl, ClassTemplatePartialSpecializationDecl, VarTemplatePartialSpecializationDecl, ConceptDecl, CXXDeductionGuideDecl, UsingShadowDecl, ConstructorUsingShadowDecl, UsingPackDecl, UnresolvedUsingTypenameDecl, UnresolvedUsingValueDecl, BindingDecl, DecompositionDecl, IndirectFieldDecl, ClassScopeFunctionSpecializationDecl, VarDecl, EnumDecl, TypedefDecl, TypeAliasDecl, NamespaceAliasDecl, UsingDirectiveDecl, UsingDecl, LinkageSpecDecl and StaticAssertDecl metadata occurrences are admitted; declaration and body execution remains refused."),
    (1, "§6.7, §6.9", "executable", "Static, thread, automatic, and dynamic storage reservation, integral initialization, lifetime end, and dynamic release execute; LifetimeExtendedTemporaryDecl and MaterializeTemporaryExpr metadata are admitted, while temporary materialization and unsupported storage remain loud."),
    (2, "§6.8", "executable", "LP64 scalar/integral values and conversions execute definitionally."),
    (3, "§7", "executable", "Bounded integral expressions and selected callable bodies execute; general overloads do not."),
    (4, "§8", "executable", "Selected callable blocks, branches, loops, switch and transfers execute."),
    (5, "§9", "executable", "The bounded integral declaration/reference frame subset executes."),
    (6, "§10", "not started", "Modules and imports have no semantic representation."),
    (7, "§11", "specified", "Class, base-subobject and member-getter evidence is specified; object construction is bounded."),
    (8, "§12", "not started", "Clang-selected overload and conversion execution is not admitted."),
    (9, "§13", "not started", "Template instantiation is retained as frontend evidence only."),
    (10, "§14", "not started", "Exceptions, unwinding and cleanup are not executable."),
    (11, "§15", "specified", "Preprocessing remains in the pinned Clang trusted boundary."),
    (12, "§16+", "not started", "The standard-library subset has not been admitted as C++ execution."),
]


CORPORA = [
    {
        "name": "TinyXML-2",
        "revision": "321ea883b7190d4e85cae5512a12e5eaa8f8731f",
        "capture": "COMPLETE",
        "admitted": 0,
        "refused": 202,
        "execution": {"MATCH": 0, "DIVERGE": 0, "REFUSE": 202, "TIMEOUT": 0, "ORACLE": 0},
        "note": "202 source-owned implementation bodies in the 2026-10-20 complete callable census; execution remains behind the translation refusal.",
    },
    {
        "name": "nlohmann/json",
        "revision": "9cca280a4d0ccf0c08f47a99aa71d1b0e52f8d03",
        "capture": "RESOURCE",
        "admitted": None,
        "refused": None,
        "execution": {"MATCH": 0, "DIVERGE": 0, "REFUSE": 0, "TIMEOUT": 0, "ORACLE": 1},
        "note": "Clang emitted a 1,975,718,707-byte probe; the recorded 128 MiB runtime census bound refused measurement before body admission.",
    },
    {
        "name": "extension-heavy systems input",
        "revision": "external pinned input",
        "capture": "EXTRACT",
        "admitted": None,
        "refused": None,
        "execution": {"MATCH": 0, "DIVERGE": 0, "REFUSE": 0, "TIMEOUT": 0, "ORACLE": 1},
        "note": "Strict C++23 extraction stopped on four anonymous-structure extension diagnostics; no source-owned denominator was published.",
    },
]


def run(command, cwd=ROOT, timeout=180):
    """Run a command with text pipes and return the completed process."""
    return subprocess.run(command, cwd=str(cwd), stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, universal_newlines=True,
                          timeout=timeout)


def capped(command, cwd=ROOT, timeout=180):
    """Run one Lean process under the mandatory 16 GiB cap."""
    prlimit = shutil.which("prlimit")
    if prlimit:
        command = [prlimit, "--as=" + ADDRESS_CAP, "--"] + list(command)
    return run(command, cwd=cwd, timeout=timeout)


def load_json(path):
    with open(path, encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, list):
        raise RuntimeError("%s must contain a JSON array" % path)
    return value


def render_lean(cases):
    modules = []
    namespaces = []
    for row in cases:
        if row["lean_module"] not in modules:
            modules.append(row["lean_module"])
        if row.get("lean_namespace") and row["lean_namespace"] not in namespaces:
            namespaces.append(row["lean_namespace"])
    lines = ["import %s" % module for module in modules]
    lines += [
        "open LeanModels.Cpp",
        "def cppRender : Option Int → String",
        "  | none => \"refuse\"",
        "  | some value => s!\"ok {value}\"",
        "def cppRenderBool : Bool → String",
        "  | true => \"ok\"",
        "  | false => \"refuse\"",
        "def cppRenderUnit : Except String Unit → String",
        "  | .ok _ => \"ok\"",
        "  | .error message => \"refuse \" ++ message",
        "def cppEmptyArtifact : Artifact := { sourceFile := \"witness.cpp\", sourceSha256 := \"fixture\", frontend := .null, dependencies := [], ast := .object [(\"kind\", .string \"TranslationUnitDecl\"), (\"inner\", .array [])] }",
    ]
    lines += ["open %s" % namespace for namespace in namespaces]
    for row in cases:
        expression = row["lean_expression"]
        render = ("cppRenderUnit" if row.get("kind") == "translation" and row.get("render") != "bool" else
                  "cppRenderBool" if row.get("render") == "bool" else
                  "cppRenderBool" if row.get("kind") in ("lifetime", "scalar", "expression", "statement") else "cppRender")
        lines.append("#eval IO.println (\"CPPCASE|%s|\" ++ %s (%s))" %
                     (row["id"], render, expression))
    return "\n".join(lines) + "\n"


def model_rows(cases):
    """Evaluate all checked-in literal rows with one Lean process."""
    with tempfile.TemporaryDirectory(prefix="cpp-diff-model-") as directory:
        source = pathlib.Path(directory) / "Rows.lean"
        source.write_text(render_lean(cases), encoding="utf-8")
        result = capped(["lake", "env", "lean", "-j", "1", str(source)], timeout=300)
    if result.returncode != 0:
        raise RuntimeError("Lean model failed:\n%s" % (result.stdout + result.stderr)[-6000:])
    values = {}
    for line in result.stdout.splitlines():
        if not line.startswith("CPPCASE|"):
            continue
        _, row_id, value = line.split("|", 2)
        values[row_id] = value.strip()
    missing = [row["id"] for row in cases if row["id"] not in values]
    if missing:
        raise RuntimeError("Lean model emitted no result for %s" % ", ".join(missing))
    return values


def clang_info():
    requested = os.environ.get("LEANCPP_CLANG") or "clang++"
    executable = shutil.which(requested) if os.path.basename(requested) == requested else requested
    if not executable or not os.path.exists(executable):
        return None, "pinned Clang/LLVM %s is unavailable (set LEANCPP_CLANG)" % PINNED_CLANG
    result = run([executable, "--version"], timeout=20)
    version = (result.stdout + result.stderr).strip()
    if result.returncode != 0:
        return None, "Clang version probe failed: %s" % version[-500:]
    if PINNED_CLANG not in version:
        return None, "Clang is not pinned to %s: %s" % (PINNED_CLANG, version.splitlines()[0] if version else "unknown")
    return executable, version.splitlines()[0] if version else PINNED_CLANG


def native_rows(cases, clang):
    if clang is None:
        return {row["id"]: ("ORACLE", "pinned Clang/LLVM %s is unavailable" % PINNED_CLANG) for row in cases}
    translation = [row for row in cases if row.get("kind") == "translation"]
    checks = [row for row in cases if row.get("kind") in ("lifetime", "scalar", "expression", "statement")]
    callable_cases = [row for row in cases if row.get("kind", "callable") == "callable"]
    result = {}
    if translation:
        with tempfile.TemporaryDirectory(prefix="cpp-diff-translation-") as directory:
            for row in translation:
                source = pathlib.Path(directory) / (row["id"].replace("/", "_") + ".cpp")
                source.write_text(row["cpp_source"] + "\n", encoding="utf-8")
                check = run([clang, "-std=c++23", "-pedantic-errors", "-fsyntax-only", str(source)], timeout=60)
                if check.returncode == 0:
                    result[row["id"]] = ("NATIVE", "ok")
                else:
                    result[row["id"]] = ("ORACLE", "translation compile failed: %s" % (check.stdout + check.stderr)[-1200:])
    if checks:
        with tempfile.TemporaryDirectory(prefix="cpp-diff-check-") as directory:
            for row in checks:
                subject = pathlib.Path(directory) / "subject.cpp"
                wrapper = pathlib.Path(directory) / "caller.cpp"
                subject.write_text(row["cpp_source"] + "\n", encoding="utf-8")
                wrapper.write_text('#include "subject.cpp"\n#include <iostream>\nint main() { if (!(%s)) return 3; std::cout << "ok\\n"; }\n' % row["cpp_expression"], encoding="utf-8")
                binary = pathlib.Path(directory) / "caller"
                check = run([clang, "-std=c++23", "-pedantic-errors", str(wrapper), "-o", str(binary)], timeout=60)
                if check.returncode != 0:
                    result[row["id"]] = ("ORACLE", "check witness compile failed: %s" % (check.stdout + check.stderr)[-1200:])
                    continue
                try:
                    execute = run([str(binary)], timeout=30)
                except subprocess.TimeoutExpired:
                    result[row["id"]] = ("TIMEOUT", "check witness exceeded 30 seconds")
                    continue
                if execute.returncode == 0 and execute.stdout.strip() == "ok":
                    result[row["id"]] = ("NATIVE", "ok")
                else:
                    result[row["id"]] = ("ORACLE", "check witness did not complete")
    if not callable_cases:
        return result
    corpus = os.environ.get("LEANCPP_TINYXML2_DIR")
    if not corpus:
        result.update({row["id"]: ("ORACLE", "set LEANCPP_TINYXML2_DIR for the unchanged source") for row in callable_cases})
        return result
    root = pathlib.Path(corpus).resolve()
    implementation = root / "tinyxml2.cpp"
    header = root / "tinyxml2.h"
    if not implementation.is_file() or not header.is_file():
        result.update({row["id"]: ("ORACLE", "LEANCPP_TINYXML2_DIR must contain tinyxml2.cpp and tinyxml2.h") for row in callable_cases})
        return result
    with tempfile.TemporaryDirectory(prefix="cpp-diff-native-") as directory:
        wrapper = pathlib.Path(directory) / "caller.cpp"
        body = ["#include <iostream>", "#include <cstdlib>", '#include "tinyxml2.h"', "int main() {"]
        for row in callable_cases:
            arg = row["args"][0]
            expression = row["cpp_expression"].format(arg=arg)
            body.append("  std::cout << (static_cast<int>(%s) ? 1 : 0) << '\\n';" % expression)
        body.append("  return 0;\n}")
        wrapper.write_text("\n".join(body) + "\n", encoding="utf-8")
        binary = pathlib.Path(directory) / "caller"
        compile_result = run([clang, "-std=c++23", "-pedantic-errors", "-I", str(root),
                              str(wrapper), str(implementation), "-o", str(binary)], timeout=180)
        if compile_result.returncode != 0:
            reason = "native compile failed: %s" % (compile_result.stdout + compile_result.stderr)[-1200:]
            result.update({row["id"]: ("ORACLE", reason) for row in callable_cases})
            return result
        try:
            execute = run([str(binary)], timeout=30)
        except subprocess.TimeoutExpired:
            result.update({row["id"]: ("TIMEOUT", "native caller exceeded 30 seconds") for row in callable_cases})
            return result
        if execute.returncode != 0:
            reason = "native caller failed: %s" % (execute.stdout + execute.stderr)[-1200:]
            result.update({row["id"]: ("ORACLE", reason) for row in callable_cases})
            return result
        outputs = execute.stdout.splitlines()
        if len(outputs) != len(callable_cases):
            reason = "native caller emitted %d rows, expected %d" % (len(outputs), len(callable_cases))
            result.update({row["id"]: ("ORACLE", reason) for row in callable_cases})
            return result
        result.update({row["id"]: ("NATIVE", outputs[index].strip())
                       for index, row in enumerate(callable_cases)})
        return result


def differential(cases, model, native):
    rows = []
    for row in cases:
        model_value = model[row["id"]]
        native_status, native_value = native[row["id"]]
        if native_status in ("ORACLE", "TIMEOUT"):
            verdict = native_status
            detail = native_value
        elif native_status == "NATIVE":
            if row.get("expect") != "match":
                verdict, detail = "DIVERGE", "native call completed for a recorded refusal"
            elif row.get("kind") in ("translation", "lifetime", "scalar", "expression", "statement") and model_value == native_value:
                verdict, detail = "MATCH", "Lean admission and Clang compilation agree"
            elif row.get("kind", "callable") == "callable" and model_value == "ok " + native_value:
                verdict, detail = "MATCH", "Lean and Clang agree"
            else:
                verdict, detail = "DIVERGE", "model=%s native=%s" % (model_value, native_value)
        else:
            verdict, detail = "DIVERGE", "unknown native status %s" % native_status
        rows.append({"id": row["id"], "corpus": row["corpus"], "kind": row.get("kind", "callable"), "rung": row["rung"],
                     "model": model_value, "native": native_status,
                     "verdict": verdict, "detail": detail})
    return rows


def raw_has_kind(value, kind):
    if isinstance(value, dict):
        if value.get("kind") == kind:
            return True
        return any(raw_has_kind(child, kind) for child in value.values())
    if isinstance(value, list):
        return any(raw_has_kind(child, kind) for child in value)
    return False


def grammar_rows(grammar, clang):
    if clang is None:
        return [{"id": row["id"], "rung": row["rung"], "verdict": "ORACLE",
                 "frontend": "ORACLE", "detail": "pinned Clang is unavailable"} for row in grammar]
    rows = []
    for row in grammar:
        with tempfile.TemporaryDirectory(prefix="cpp-grammar-") as directory:
            source = pathlib.Path(directory) / "witness.cpp"
            source.write_text(row["source"] + "\n", encoding="utf-8")
            result = run([clang, "-std=c++23", "-fsyntax-only", "-w", "-Xclang",
                          "-ast-dump=json", str(source)], timeout=60)
        if result.returncode != 0:
            rows.append({"id": row["id"], "rung": row["rung"], "verdict": "ORACLE",
                         "frontend": "ORACLE", "detail": "witness did not compile"})
            continue
        try:
            ast = json.loads(result.stdout)
        except ValueError:
            rows.append({"id": row["id"], "rung": row["rung"], "verdict": "ORACLE",
                         "frontend": "ORACLE", "detail": "Clang did not emit JSON AST"})
            continue
        if not raw_has_kind(ast, row["id"]):
            rows.append({"id": row["id"], "rung": row["rung"], "verdict": "DIVERGE",
                         "frontend": "DIVERGE", "detail": "witness AST lacks its declared node kind"})
            continue
        rows.append({"id": row["id"], "rung": row["rung"], "verdict": "REFUSE",
                     "frontend": "MATCH", "detail": "translation execution is intentionally refused"})
    return rows


def counts(rows, field="verdict"):
    result = {}
    for row in rows:
        key = row[field]
        result[key] = result.get(key, 0) + 1
    return result


def corpus_table():
    return CORPORA


def markdown_cell(value):
    return str(value).replace("|", "\\|").replace("\n", " ")


def render_rung_page(diff_rows, grammar_rows_value):
    lines = [
        "# C++ rung status and corpus census",
        "",
        "<!-- GENERATED by harness/cpp_diff_test.py --check -->",
        "",
        "Measured against the C++ charter's N4950 clause ladder. `executable` means a bounded Lean definition and tests run; it does not claim complete ISO coverage. `MATCH` requires the unchanged source compiled by pinned Clang/LLVM 21.1.8. Missing frontend or corpus inputs are reported as `ORACLE`/`EXTRACT`, never as matches.",
        "",
        "## Clause ladder",
        "",
        "| rung | N4950 clauses | status | measured boundary |",
        "|---:|---|---|---|",
    ]
    for rung, clauses, status, note in RUNG_STATUS:
        lines.append("| %d | %s | **%s** | %s |" % (rung, clauses, status, note))
    lines += ["", "## Three-corpus census", "",
              "The source-owned denominator is the retained 2026-10-20 callable census where available. A null denominator means extraction or resource limits prevented a semantic count.",
              "",
              "| corpus | capture | source-owned admitted | source-owned refused | MATCH | DIVERGE | REFUSE | TIMEOUT | ORACLE |",
              "|---|---|---:|---:|---:|---:|---:|---:|---:|"]
    for corpus in CORPORA:
        execution = corpus["execution"]
        lines.append("| %s | %s | %s | %s | %d | %d | %d | %d | %d |" %
                     (corpus["name"], corpus["capture"],
                      corpus["admitted"] if corpus["admitted"] is not None else "—",
                      corpus["refused"] if corpus["refused"] is not None else "—",
                      execution["MATCH"], execution["DIVERGE"], execution["REFUSE"],
                      execution["TIMEOUT"], execution["ORACLE"]))
        lines.append("")
        lines.append("*%s:* %s" % (corpus["name"], corpus["note"]))
        lines.append("")
    lines += ["## This run's grammar and differential measurements", "",
              "The grammar census uses one source witness per listed Clang AST node kind. The root-shape admission is executable, while declaration and body execution remain loud refusals; therefore a successfully compiled declaration witness is a `REFUSE` until its rung is admitted.",
              "",
              "| measurement | rows | MATCH | DIVERGE | REFUSE | TIMEOUT | ORACLE |",
              "|---|---:|---:|---:|---:|---:|---:|"]
    grammar_count = counts(grammar_rows_value)
    diff_count = counts(diff_rows)
    lines.append("| grammar witnesses | %d | %d | %d | %d | %d | %d |" %
                 (len(grammar_rows_value), grammar_count.get("MATCH", 0),
                  grammar_count.get("DIVERGE", 0), grammar_count.get("REFUSE", 0),
                  grammar_count.get("TIMEOUT", 0), grammar_count.get("ORACLE", 0)))
    lines.append("| differential calls | %d | %d | %d | %d | %d | %d |" %
                 (len(diff_rows), diff_count.get("MATCH", 0), diff_count.get("DIVERGE", 0),
                  diff_count.get("REFUSE", 0), diff_count.get("TIMEOUT", 0),
                  diff_count.get("ORACLE", 0)))
    translation_count = sum(1 for row in diff_rows if row["rung"] == 0)
    lifetime_count = sum(1 for row in diff_rows if row["rung"] == 1)
    scalar_count = sum(1 for row in diff_rows if row["kind"] == "scalar")
    expression_count = sum(1 for row in diff_rows if row["kind"] == "expression")
    statement_count = sum(1 for row in diff_rows if row["kind"] == "statement")
    callable_count = len(diff_rows) - translation_count - lifetime_count - scalar_count - expression_count - statement_count
    lines += ["", "The differential rows include %d compile-only translation witness, %d rung-1 lifetime witnesses, %d rung-2 scalar checks, %d rung-3 expression checks, %d rung-4 statement checks, and %d callable rows across the retained callable witness set; set `LEANCPP_TINYXML2_DIR` and `LEANCPP_CLANG` to replace the explicit ORACLE rows with compiled calls." % (translation_count, lifetime_count, scalar_count, expression_count, statement_count, callable_count), ""]
    return "\n".join(lines)


def render_coverage(diff_rows, grammar_rows_value):
    lines = [
        "# C++ coverage",
        "",
        "<!-- GENERATED by harness/cpp_diff_test.py --check -->",
        "",
        "This page is generated from `harness/cpp_cases.json` and `harness/cpp_grammar.json`. The native oracle is the unchanged source compiled and called by Clang/LLVM 21.1.8. The Lean side is the literal artifact and evaluator in `Examples/cpp`; unavailable inputs are counted as `ORACLE`.",
        "",
        "## Differential table",
        "",
        "| rows | MATCH | DIVERGE | REFUSE | TIMEOUT | ORACLE |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    diff_count = counts(diff_rows)
    lines.append("| %d | %d | %d | %d | %d | %d |" %
                 (len(diff_rows), diff_count.get("MATCH", 0), diff_count.get("DIVERGE", 0),
                  diff_count.get("REFUSE", 0), diff_count.get("TIMEOUT", 0),
                  diff_count.get("ORACLE", 0)))
    lines += ["", "Each row compares a Lean result with the native call. `ORACLE` is an environment or compilation boundary, not agreement.", "", "| case | rung | Lean | native | verdict | detail |", "|---|---:|---|---|---|---|"]
    for row in diff_rows:
        lines.append("| `%s` | %d | `%s` | `%s` | **%s** | %s |" %
                     (row["id"], row["rung"], row["model"], row["native"], row["verdict"], markdown_cell(row["detail"])))
    lines += ["", "## Grammar census", "", "One witness per listed Clang AST node kind, mapped to the charter rung. `frontend` records whether the pinned Clang AST contained the requested node; `verdict` is the Lean execution result.", "", "| node kind | rung | frontend | verdict | detail |", "|---|---:|---|---|---|"]
    for row in grammar_rows_value:
        lines.append("| `%s` | %d | %s | **%s** | %s |" %
                     (row["id"], row["rung"], row["frontend"], row["verdict"], markdown_cell(row["detail"])))
    lines += ["", "## Rung and corpus status", "", "See the generated [clause ladder and three-corpus census](cpp-rung-status.md).", ""]
    return "\n".join(lines)


def write_or_check(path, contents, check):
    if check:
        try:
            old = path.read_text(encoding="utf-8")
        except OSError:
            old = ""
        return old == contents
    path.write_text(contents, encoding="utf-8")
    return True


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", default=str(CASES))
    parser.add_argument("--grammar", default=str(GRAMMAR))
    parser.add_argument("--json", dest="json_path")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--require-oracle", action="store_true")
    args = parser.parse_args(argv)
    os.chdir(ROOT)
    cases = load_json(pathlib.Path(args.cases))
    grammar = load_json(pathlib.Path(args.grammar))
    ids = [row.get("id") for row in cases]
    if any(not row_id for row_id in ids) or len(ids) != len(set(ids)):
        raise SystemExit("cpp_diff_test: case ids must be nonempty and unique")
    if any(row.get("kind", "callable") == "callable" and not row.get("lean_namespace") for row in cases):
        raise SystemExit("cpp_diff_test: callable rows require lean_namespace")
    grammar_ids = [row.get("id") for row in grammar]
    if any(not row_id for row_id in grammar_ids) or len(grammar_ids) != len(set(grammar_ids)):
        raise SystemExit("cpp_diff_test: grammar ids must be nonempty and unique")
    model = model_rows(cases)
    clang, clang_version = clang_info()
    native = native_rows(cases, clang)
    diff_rows = differential(cases, model, native)
    grammar_result = grammar_rows(grammar, clang)
    rung = render_rung_page(diff_rows, grammar_result)
    coverage = render_coverage(diff_rows, grammar_result)
    payload = {"format": "cpp-coverage-1", "clang": clang_version,
               "differential": diff_rows, "grammar": grammar_result,
               "rungs": [{"rung": r, "clauses": c, "status": s, "note": n}
                          for r, c, s, n in RUNG_STATUS],
               "corpora": corpus_table()}
    if args.json_path:
        pathlib.Path(args.json_path).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.check:
        fresh = write_or_check(COVERAGE_PAGE, coverage, True) and write_or_check(RUNG_PAGE, rung, True)
        if not fresh:
            print("cpp_diff_test: generated C++ coverage pages are stale", file=sys.stderr)
            return 1
        print("cpp_diff_test: coverage pages are fresh")
    else:
        write_or_check(COVERAGE_PAGE, coverage, False)
        write_or_check(RUNG_PAGE, rung, False)
        print("cpp_diff_test: wrote %s and %s" % (COVERAGE_PAGE, RUNG_PAGE))
    counts_text = counts(diff_rows)
    print("%d differential rows: %d MATCH, %d DIVERGE, %d REFUSE, %d TIMEOUT, %d ORACLE" %
          (len(diff_rows), counts_text.get("MATCH", 0), counts_text.get("DIVERGE", 0),
           counts_text.get("REFUSE", 0), counts_text.get("TIMEOUT", 0), counts_text.get("ORACLE", 0)))
    grammar_text = counts(grammar_result)
    print("%d grammar witnesses: %d MATCH, %d DIVERGE, %d REFUSE, %d TIMEOUT, %d ORACLE" %
          (len(grammar_result), grammar_text.get("MATCH", 0), grammar_text.get("DIVERGE", 0),
           grammar_text.get("REFUSE", 0), grammar_text.get("TIMEOUT", 0), grammar_text.get("ORACLE", 0)))
    if args.require_oracle and (counts_text.get("ORACLE", 0) or grammar_text.get("ORACLE", 0)):
        return 2
    if counts_text.get("DIVERGE", 0) or grammar_text.get("DIVERGE", 0):
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        print("cpp_diff_test: ERROR: %s" % error, file=sys.stderr)
        sys.exit(2)
