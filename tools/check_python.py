#!/usr/bin/env python3
"""Run the Python lane's acceptance gates without other language harnesses."""

import argparse
import os
from pathlib import Path
import shlex
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
CURATED_EXAMPLES = (
    "add", "my_abs", "midpoint", "tri", "gcd", "fib", "nested_flow",
    "rsa_inverse", "bench_bisect", "bench_statistics", "int_string",
    "string_repeat", "tuple_repeat", "decimal_render", "range_render",
    "bool_lab", "divmod_lab", "repr_lab", "fstring_repr", "ellipsis_lab",
    "float_lab", "exc_handlers_lab", "exc_ancestors_lab",
)


def build_targets(root):
    targets = ["LeanModels/Python.lean"]
    for directory in ("LeanModels/Python", "Examples/python"):
        sources = sorted((root / directory).rglob("*.lean"))
        if not sources:
            raise ValueError("no Lean sources found under " + directory)
        targets.extend(source.relative_to(root).as_posix() for source in sources)
    return [*targets, "leanmodels-run"]


def acceptance_gates(root):
    python = sys.executable
    runner = ".lake/build/bin/leanmodels-run"
    lean_paths = [root / ".lake/build/lib/lean"]
    lean_paths.extend(sorted((root / ".lake/packages").glob("*/.lake/build/lib/lean")))
    axiom_modules = [
        "Examples.python." + example + "." + component
        for example in CURATED_EXAMPLES
        for component in ("spec", "proof")
    ]
    tests = (
        ("ci-entrypoint-tests", "tools/test_ci_entrypoint.py"),
        ("python-check-tests", "tools/test_python_check.py"),
        ("py-onboarding-imports", "tools/test_python_onboarding.py"),
        ("py-divergence-probe-tests", "harness/test_pyc_divergence_probe.py"),
        ("py-refusal-census-tests", "harness/test_refusal_census.py"),
        ("py-float-boundary-tests", "harness/test_float_boundary.py"),
        ("notebook-cache-tests", "tools/test_notebook_cache.py"),
        ("notebook-dependency-tests", "tools/test_notebook_dependencies.py"),
        ("extractor-tests", "extractors/python/test_extract.py"),
        ("leanpy-cache-tests", "tools/test_leanpy.py"),
    )
    return [(name, [python, script]) for name, script in tests] + [
        ("py-declared-divergences", [python, "harness/pyc_divergence_probe.py"]),
        ("py-harness", [python, "harness/diff_test.py", "--no-build", "--runner", runner]),
        ("py-proof-interpreter", [python, "harness/diff_test.py", "--no-build",
                                  "--runner", runner, "--proof-interpreter"]),
        ("py-script-corpus", [python, "harness/script_corpus.py", "--no-build",
                              "--runner", runner]),
        ("py-refusal-census", [python, "harness/refusal_census.py", "--whitelist",
                               "--scripts", "--no-build", "--runner", runner]),
        ("leanpy-survey", [python, "harness/leanpy_survey.py"]),
        ("py-coverage-fresh", [python, "harness/coverage_page.py", "--check",
                               "--runner", runner]),
        ("py-examples-axioms", [python, "harness/lean_axiom_census.py", "--modules",
                                *axiom_modules, "--lean-path",
                                os.pathsep.join(str(path) for path in lean_paths),
                                "--gate", "-o", os.devnull]),
        ("docs-check", [python, "tools/docs_check.py"]),
        ("python-notebooks", [python, "tools/run_notebooks.py", "--no-save",
                               "notebooks/01-pipeline.ipynb",
                               "notebooks/02-loops-interactive.ipynb"]),
    ]


def run_gate(root, name, command):
    print("=== [%s] %s" % (name, shlex.join(command)), flush=True)
    try:
        result = subprocess.run(command, cwd=root)
    except OSError as error:
        print("FAIL: %s could not start: %s" % (name, error), file=sys.stderr)
        return False
    return result.returncode == 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true",
                        help="reuse existing artifacts instead of the initial build")
    parser.add_argument("--require-build", action="store_true",
                        help="fail if the initial build is skipped")
    options = parser.parse_args(argv)
    if os.environ.get("LS_CI_SELF_TEST"):
        parser.error("LS_CI_SELF_TEST is set; refusing recursive CI execution")
    if options.no_build and options.require_build:
        parser.error("--no-build cannot be combined with --require-build")

    passed = []
    failed = []
    skipped = []
    if options.no_build or os.environ.get("GITHUB_ACTIONS") != "true":
        reason = "explicit --no-build" if options.no_build else "local builds use tools/triad.sh"
        print("=== [python-build] SKIP (%s; existing artifacts are required)" % reason,
              flush=True)
        if options.require_build:
            print("FAIL: --require-build does not permit a skipped build", file=sys.stderr)
            return 1
        skipped.append("python-build")
    else:
        try:
            targets = build_targets(ROOT)
        except ValueError as error:
            print("FAIL: python-build: %s" % error, file=sys.stderr)
            return 1
        if not run_gate(ROOT, "python-build", ["lake", "build", *targets]):
            print("FAIL: python-build; refusing gates against stale artifacts", file=sys.stderr)
            return 1
        passed.append("python-build")

    runner = ROOT / ".lake/build/bin/leanmodels-run"
    if not runner.is_file() or not os.access(runner, os.X_OK):
        print("FAIL: required Python runner is missing or not executable: " + str(runner),
              file=sys.stderr)
        return 1
    for name, command in acceptance_gates(ROOT):
        (passed if run_gate(ROOT, name, command) else failed).append(name)
    print("\n==================== PYTHON CHECK SUMMARY ====================")
    print("PASS: " + (" ".join(passed) or "none"))
    print("SKIP: " + (" ".join(skipped) or "none"))
    print("FAIL: " + (" ".join(failed) or "none"))
    print("Scope: Python acceptance and shared documentation only; not full repository CI.")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
