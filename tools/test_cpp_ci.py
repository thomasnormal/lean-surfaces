#!/usr/bin/env python3
"""Check the CI driver's C++ extractor admission without invoking real tools."""

import os
from pathlib import Path
import shlex
import subprocess
import unittest
from unittest.mock import patch


CI_DRIVER = Path(__file__).resolve().parent / "ci.sh"


def driver_function(name):
    source = CI_DRIVER.read_text(encoding="utf-8")
    prefix = "\n" + name + "() {"
    _, marker, suffix = source.partition(prefix)
    if not marker:
        raise AssertionError("CI driver has no " + name + " function")
    body, terminator, _ = suffix.partition("\n}\n")
    if not terminator:
        raise AssertionError("CI driver has no terminator for " + name)
    return marker + body + terminator


def driver_cpp_registration():
    source = CI_DRIVER.read_text(encoding="utf-8")
    _, main_marker, main = source.partition(
        '\nstep  "conflict-markers" conflict_markers\n'
    )
    if not main_marker:
        raise AssertionError("CI driver has no top-level gate sequence")
    preceding, extractor_marker, following = main.partition("\ncpp_extractor_step\n")
    if not extractor_marker:
        raise AssertionError("CI driver has no top-level C++ extractor registration")
    preceding = preceding.replace(driver_function("py_examples_axioms"), "\n")
    control_words = {"if", "then", "else", "elif", "fi", "case", "esac",
                     "for", "while", "until", "select", "do", "done", "function",
                     "{", "}", "(", ")"}
    for line in preceding.splitlines():
        words = shlex.split(line, comments=True)
        if words and (words[0] in control_words or words[-1] in {"{", "&&", "||", "|", "&"}):
            raise AssertionError("CI driver C++ registration must be unconditional at top level")
    comparison = following.splitlines()[0]
    expected = 'step "cpp-comparison-tests" python3 extractors/cpp/test_compare_ast.py'
    if comparison != expected:
        raise AssertionError("CI driver must register the unconditional C++ comparison step")
    return extractor_marker + comparison + "\n"


class CppCiTests(unittest.TestCase):
    def invoke(self, tools=(), override=None, extractor_status=0,
               comparison_status=0, include_comparison=False):
        fixtures = """
set -u
pass=(); fail=(); skip=(); calls=(); queries=(); env_calls=()
command() {
  if [ "$#" -eq 2 ] && [ "$1" = "-v" ]; then
    queries+=("$2")
    case "|$CI_AVAILABLE_TOOLS|" in
      *"|$2|"*) printf '/mock/%s\\n' "$2"; return 0 ;;
      *) return 1 ;;
    esac
  fi
  echo "unexpected command invocation: $*" >&2
  return 98
}
env() {
  if [ "$#" -ne 3 ] || [ "$1" != "LEANCPP_TEST_LEAN=1" ] ||
     [ "$2" != "python3" ] || [ "$3" != "extractors/cpp/test_extract.py" ]; then
    echo "unexpected env invocation: $*" >&2
    return 98
  fi
  env_calls+=("$*")
  shift
  LEANCPP_TEST_LEAN=1 "$@"
}
python3() {
  calls+=("${LEANCPP_TEST_LEAN:-}|${LEANCPP_CLANG:-}|$*")
  case "$*" in
    extractors/cpp/test_extract.py) return "$CI_EXTRACTOR_STATUS" ;;
    extractors/cpp/test_compare_ast.py) return "$CI_COMPARISON_STATUS" ;;
    *) echo "unexpected python invocation: $*" >&2; return 98 ;;
  esac
}
"""
        report = """
for name in "${pass[@]}"; do printf '__PASS__\\t%s\\n' "$name"; done
for name in "${fail[@]}"; do printf '__FAIL__\\t%s\\n' "$name"; done
for name in "${skip[@]}"; do printf '__SKIP__\\t%s\\n' "$name"; done
for invocation in "${calls[@]}"; do printf '__CALL__\\t%s\\n' "$invocation"; done
for query in "${queries[@]}"; do printf '__QUERY__\\t%s\\n' "$query"; done
for invocation in "${env_calls[@]}"; do printf '__ENV__\\t%s\\n' "$invocation"; done
"""
        environment = os.environ.copy()
        environment.pop("LEANCPP_CLANG", None)
        environment["LEANCPP_TEST_LEAN"] = "0"
        environment["CI_AVAILABLE_TOOLS"] = "|".join(tools)
        environment["CI_EXTRACTOR_STATUS"] = str(extractor_status)
        environment["CI_COMPARISON_STATUS"] = str(comparison_status)
        if override is not None:
            environment["LEANCPP_CLANG"] = override
        registration = (driver_cpp_registration() if include_comparison
                        else "\ncpp_extractor_step\n")
        result = subprocess.run(
            ["bash", "-c", fixtures + driver_function("step")
             + driver_function("cpp_extractor_step") + registration + report],
            env=environment,
            capture_output=True,
            text=True,
            timeout=10,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stderr, "")
        observed = {"pass": [], "fail": [], "skip": [], "calls": [],
                    "queries": [], "env_calls": [], "output": result.stdout}
        for line in result.stdout.splitlines():
            marker, separator, value = line.partition("\t")
            if separator and marker in ("__PASS__", "__FAIL__", "__SKIP__"):
                observed[marker[2:-2].lower()].append(value)
            elif marker == "__CALL__":
                integration, frontend, arguments = value.split("|", 2)
                observed["calls"].append((integration, frontend, shlex.split(arguments)))
            elif marker == "__QUERY__":
                observed["queries"].append(value)
            elif marker == "__ENV__":
                observed["env_calls"].append(shlex.split(value))
        return observed

    def test_present_clang_runs_the_extractor_and_lean_ingester(self):
        observed = self.invoke(("clang++",))
        self.assertEqual(observed["queries"], ["clang++"])
        self.assertEqual(observed["calls"], [("1", "", ["extractors/cpp/test_extract.py"])])
        self.assertEqual(observed["env_calls"], [
            ["LEANCPP_TEST_LEAN=1", "python3", "extractors/cpp/test_extract.py"],
        ])
        self.assertIn(
            "=== [cpp-extractor-tests] env LEANCPP_TEST_LEAN=1 python3 extractors/cpp/test_extract.py",
            observed["output"],
        )
        self.assertEqual(observed["pass"], ["cpp-extractor-tests"])
        self.assertEqual(observed["fail"], [])
        self.assertEqual(observed["skip"], [])

    def test_missing_clang_is_an_explicit_skip_without_an_extractor_call(self):
        observed = self.invoke()
        self.assertEqual(observed["queries"], ["clang++"])
        self.assertEqual(observed["calls"], [])
        self.assertEqual(observed["env_calls"], [])
        self.assertEqual(observed["pass"], [])
        self.assertEqual(observed["fail"], [])
        self.assertEqual(observed["skip"], ["cpp-extractor-tests"])
        self.assertIn("SKIP", observed["output"])
        self.assertIn("clang++", observed["output"])

    def test_frontend_override_is_checked_and_preserved_with_spaces(self):
        override = "/opt/clang tools/clang++-18"
        observed = self.invoke((override,), override=override)
        self.assertEqual(observed["queries"], [override])
        self.assertEqual(observed["calls"], [("1", override, ["extractors/cpp/test_extract.py"])])
        self.assertEqual(observed["env_calls"], [
            ["LEANCPP_TEST_LEAN=1", "python3", "extractors/cpp/test_extract.py"],
        ])
        self.assertEqual(observed["pass"], ["cpp-extractor-tests"])
        self.assertEqual(observed["fail"], [])
        self.assertEqual(observed["skip"], [])

    def test_missing_override_does_not_fall_back_to_clang(self):
        observed = self.invoke(("clang++",), override="clang++-unavailable")
        self.assertEqual(observed["queries"], ["clang++-unavailable"])
        self.assertEqual(observed["calls"], [])
        self.assertEqual(observed["env_calls"], [])
        self.assertEqual(observed["pass"], [])
        self.assertEqual(observed["fail"], [])
        self.assertEqual(observed["skip"], ["cpp-extractor-tests"])
        self.assertIn("clang++-unavailable", observed["output"])

    def test_extractor_failure_remains_a_failure_not_a_skip(self):
        observed = self.invoke(("clang++",), extractor_status=7)
        self.assertEqual(observed["calls"], [("1", "", ["extractors/cpp/test_extract.py"])])
        self.assertEqual(observed["env_calls"], [
            ["LEANCPP_TEST_LEAN=1", "python3", "extractors/cpp/test_extract.py"],
        ])
        self.assertEqual(observed["pass"], [])
        self.assertEqual(observed["fail"], ["cpp-extractor-tests"])
        self.assertEqual(observed["skip"], [])

    def test_comparison_runs_without_clang_or_lean_admission(self):
        observed = self.invoke(include_comparison=True)
        self.assertEqual(observed["queries"], ["clang++"])
        self.assertEqual(observed["calls"], [
            ("0", "", ["extractors/cpp/test_compare_ast.py"]),
        ])
        self.assertEqual(observed["env_calls"], [])
        self.assertEqual(observed["pass"], ["cpp-comparison-tests"])
        self.assertEqual(observed["fail"], [])
        self.assertEqual(observed["skip"], ["cpp-extractor-tests"])
        self.assertIn(
            "=== [cpp-comparison-tests] python3 extractors/cpp/test_compare_ast.py",
            observed["output"],
        )

    def test_comparison_failure_is_named_failure_without_clang(self):
        observed = self.invoke(comparison_status=7, include_comparison=True)
        self.assertEqual(observed["queries"], ["clang++"])
        self.assertEqual(observed["calls"], [
            ("0", "", ["extractors/cpp/test_compare_ast.py"]),
        ])
        self.assertEqual(observed["env_calls"], [])
        self.assertEqual(observed["pass"], [])
        self.assertEqual(observed["fail"], ["cpp-comparison-tests"])
        self.assertEqual(observed["skip"], ["cpp-extractor-tests"])

    def test_comparison_still_runs_after_extractor_failure(self):
        observed = self.invoke(("clang++",), extractor_status=7, include_comparison=True)
        self.assertEqual(observed["calls"], [
            ("1", "", ["extractors/cpp/test_extract.py"]),
            ("0", "", ["extractors/cpp/test_compare_ast.py"]),
        ])
        self.assertEqual(observed["env_calls"], [
            ["LEANCPP_TEST_LEAN=1", "python3", "extractors/cpp/test_extract.py"],
        ])
        self.assertEqual(observed["pass"], ["cpp-comparison-tests"])
        self.assertEqual(observed["fail"], ["cpp-extractor-tests"])
        self.assertEqual(observed["skip"], [])

    def test_comparison_in_an_unused_helper_is_not_registration(self):
        source = CI_DRIVER.read_text(encoding="utf-8")
        comparison = 'step "cpp-comparison-tests" python3 extractors/cpp/test_compare_ast.py\n'
        changed = "unused_comparison() {\n" + comparison + "}\n" + source.replace(comparison, "")
        with patch.object(Path, "read_text", return_value=changed):
            with self.assertRaisesRegex(AssertionError, "unconditional C\\+\\+ comparison"):
                driver_cpp_registration()

    def test_comparison_inside_a_guard_is_not_unconditional(self):
        source = CI_DRIVER.read_text(encoding="utf-8")
        registration = driver_cpp_registration()
        changed = source.replace(registration, "\nif false; then" + registration + "fi\n")
        with patch.object(Path, "read_text", return_value=changed):
            with self.assertRaisesRegex(AssertionError, "unconditional at top level"):
                driver_cpp_registration()


if __name__ == "__main__":
    unittest.main()
