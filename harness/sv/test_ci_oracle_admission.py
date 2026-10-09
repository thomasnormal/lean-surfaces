#!/usr/bin/env python3
"""Check the CI driver's SV oracle selection without invoking real tools."""

import os
from pathlib import Path
import shlex
import subprocess
import unittest


CI_DRIVER = Path(__file__).resolve().parents[2] / "tools" / "ci.sh"


def selection_block():
    source = CI_DRIVER.read_text(encoding="utf-8")
    _, marker, suffix = source.partition("\nxcelium_ready=0\n")
    if not marker:
        raise AssertionError("CI driver has no Xcelium readiness admission block")
    before_sv2, marker, sv2 = suffix.partition("\n# sv-0.2 semantic tier:")
    if not marker:
        raise AssertionError("CI driver has no SV2 boundary after SV admission")
    sv2_body, terminator, _ = sv2.partition("\nfi\n")
    if not terminator:
        raise AssertionError("CI driver has no SV2 admission terminator")
    return "xcelium_ready=0\n" + before_sv2 + marker + sv2_body + terminator


class CiOracleAdmissionTests(unittest.TestCase):
    def invoke(self, tools=(), probe_status=0):
        fixtures = """
set -u
pass=(); fail=(); skip=(); calls=()
probe_calls=0
command() {
  if [ "$#" -eq 2 ] && [ "$1" = "-v" ]; then
    case " $CI_AVAILABLE_TOOLS " in
      *" $2 "*) printf '/mock/%s\\n' "$2"; return 0 ;;
      *) return 1 ;;
    esac
  fi
  echo "unexpected command invocation: $*" >&2
  return 98
}
python3() {
  if [ "$#" -eq 1 ] && [ "$1" = "harness/sv/xcelium_probe.py" ]; then
    probe_calls=$((probe_calls + 1))
    return "$CI_PROBE_STATUS"
  fi
  echo "unexpected Python invocation: $*" >&2
  return 98
}
maybe() {
  local name="$1" required="$2"
  shift 2
  calls+=("$name|$required|$*")
  pass+=("$name")
}
"""
        report = """
for name in "${pass[@]}"; do printf '__PASS__\\t%s\\n' "$name"; done
for name in "${fail[@]}"; do printf '__FAIL__\\t%s\\n' "$name"; done
for name in "${skip[@]}"; do printf '__SKIP__\\t%s\\n' "$name"; done
for invocation in "${calls[@]}"; do printf '__CALL__\\t%s\\n' "$invocation"; done
printf '__PROBE_COUNT__\\t%s\\n' "$probe_calls"
"""
        environment = os.environ.copy()
        environment["CI_AVAILABLE_TOOLS"] = " ".join(tools)
        environment["CI_PROBE_STATUS"] = str(probe_status)
        result = subprocess.run(
            ["bash", "-c", fixtures + selection_block() + report],
            env=environment,
            capture_output=True,
            text=True,
            timeout=10,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stderr, "")
        observed = {"pass": [], "fail": [], "skip": [], "calls": [],
                    "probe_calls": 0, "output": result.stdout}
        for line in result.stdout.splitlines():
            marker, separator, value = line.partition("\t")
            if separator and marker in ("__PASS__", "__FAIL__", "__SKIP__"):
                observed[marker[2:-2].lower()].append(value)
            elif marker == "__CALL__":
                name, required, command = value.split("|", 2)
                observed["calls"].append((name, required, shlex.split(command)))
            elif marker == "__PROBE_COUNT__":
                observed["probe_calls"] = int(value)
        return observed

    def expected_calls(self, m0, phase2):
        return [
            ("sv-harness", "harness/sv/diff_test.py",
             ["python3", "harness/sv/diff_test.py", "--sim", m0]),
            ("sv2-harness", "harness/sv/diff_test2.py",
             ["python3", "harness/sv/diff_test2.py", "--sim", phase2]),
        ]

    def assert_no_admitted_simulator(self, observed):
        self.assertEqual(observed["calls"], [])
        self.assertEqual(observed["pass"], [])
        self.assertEqual(observed["fail"], [])
        self.assertEqual(
            observed["skip"], ["xcelium-oracle", "sv-harness", "sv2-harness"]
        )
        self.assertIn("no admitted simulator", observed["output"])

    def test_ready_xcelium_and_icarus_preserve_dual_verification(self):
        observed = self.invoke(("xrun", "iverilog", "vvp"), probe_status=0)
        self.assertEqual(observed["calls"], self.expected_calls("iverilog", "auto"))
        self.assertEqual(
            observed["pass"], ["xcelium-probe", "sv-harness", "sv2-harness"]
        )
        self.assertEqual(observed["fail"], [])
        self.assertEqual(observed["skip"], [])
        self.assertEqual(observed["probe_calls"], 1)

    def test_license_absence_reports_skip_and_selects_icarus_explicitly(self):
        observed = self.invoke(("xrun", "iverilog", "vvp"), probe_status=77)
        self.assertEqual(
            observed["calls"], self.expected_calls("iverilog", "iverilog")
        )
        self.assertEqual(observed["pass"], ["sv-harness", "sv2-harness"])
        self.assertEqual(observed["fail"], [])
        self.assertEqual(observed["skip"], ["xcelium-oracle"])
        self.assertIn("Xcelium license unavailable", observed["output"])
        self.assertEqual(observed["probe_calls"], 1)

    def test_unexpected_probe_error_remains_failure_with_icarus(self):
        for probe_status in (1, 2, 98):
            with self.subTest(probe_status=probe_status):
                observed = self.invoke(
                    ("xrun", "iverilog", "vvp"), probe_status=probe_status
                )
                self.assertEqual(
                    observed["calls"], self.expected_calls("iverilog", "iverilog")
                )
                self.assertEqual(observed["pass"], ["sv-harness", "sv2-harness"])
                self.assertEqual(observed["fail"], ["xcelium-probe"])
                self.assertEqual(observed["skip"], [])
                self.assertEqual(observed["probe_calls"], 1)

    def test_xcelium_only_license_absence_admits_no_simulator(self):
        observed = self.invoke(("xrun",), probe_status=77)
        self.assert_no_admitted_simulator(observed)
        self.assertEqual(observed["probe_calls"], 1)
        self.assertIn("Xcelium license unavailable", observed["output"])

    def test_without_xcelium_icarus_still_runs_both_harnesses(self):
        observed = self.invoke(("iverilog", "vvp"))
        self.assertEqual(
            observed["calls"], self.expected_calls("iverilog", "iverilog")
        )
        self.assertEqual(observed["pass"], ["sv-harness", "sv2-harness"])
        self.assertEqual(observed["fail"], [])
        self.assertEqual(observed["skip"], ["xcelium-oracle"])
        self.assertEqual(observed["probe_calls"], 0)

    def test_missing_vvp_falls_back_to_ready_xcelium(self):
        observed = self.invoke(("xrun", "iverilog"), probe_status=0)
        self.assertEqual(observed["calls"], self.expected_calls("xrun", "auto"))
        self.assertEqual(
            observed["pass"], ["xcelium-probe", "sv-harness", "sv2-harness"]
        )
        self.assertEqual(observed["fail"], [])
        self.assertEqual(observed["skip"], [])
        self.assertEqual(observed["probe_calls"], 1)

    def test_missing_vvp_without_xcelium_skips_both_harnesses(self):
        observed = self.invoke(("iverilog",))
        self.assert_no_admitted_simulator(observed)
        self.assertEqual(observed["probe_calls"], 0)

    def test_no_oracle_skips_without_claiming_checks(self):
        observed = self.invoke()
        self.assert_no_admitted_simulator(observed)
        self.assertEqual(observed["probe_calls"], 0)


if __name__ == "__main__":
    unittest.main()
