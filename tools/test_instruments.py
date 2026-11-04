#!/usr/bin/env python3
"""Check load readings and thread selection without running CI or triad."""

import os
import pathlib
import subprocess
import unittest


INSTRUMENTS = pathlib.Path(__file__).resolve().with_name("instruments.sh")
TRIAD = INSTRUMENTS.with_name("triad.sh")
LIVE_PROBES = """
awk() {
  case "$1" in
    -v) command awk "$@" ;;
    *) printf 'LIVE_PROBE\\n' >&2; printf '7.25\\n' ;;
  esac
}
sysctl() { printf 'LIVE_PROBE\\n' >&2; printf '{7.25 7.25 7.25}\\n'; }
"""


def isolated_choose_threads():
    source = TRIAD.read_text(encoding="utf-8")
    start = source.index("choose_threads() {")
    stop = source.index("\n}\n", start) + len("\n}\n")
    return source[start:stop]


class LoadReadingTests(unittest.TestCase):
    def run_reader(self, mock_load, body="read_load"):
        environment = dict(os.environ)
        environment.pop("BASH_ENV", None)
        environment.pop("LS_MOCK_LOAD", None)
        if mock_load is not None:
            environment["LS_MOCK_LOAD"] = mock_load
        script = 'source "$1"\n' + LIVE_PROBES + body
        return subprocess.run(
            ["bash", "--noprofile", "--norc", "-c", script,
             "isolated-instruments", str(INSTRUMENTS)],
            env=environment, capture_output=True, text=True, timeout=10,
        )

    def assert_mock_reading(self, value):
        completed = self.run_reader(value)
        self.assertEqual(completed.returncode, 0)
        self.assertEqual(completed.stdout, value + "\n")
        self.assertEqual(completed.stderr, "")

    def test_unset_mock_reads_the_live_instrument(self):
        completed = self.run_reader(None)
        self.assertEqual(completed.returncode, 0)
        self.assertEqual(completed.stdout, "7.25\n")
        self.assertEqual(completed.stderr, "LIVE_PROBE\n")

    def test_explicit_empty_mock_does_not_read_the_live_instrument(self):
        self.assert_mock_reading("")

    def test_valid_mock_is_preserved_exactly(self):
        self.assert_mock_reading("0.50")

    def test_invalid_mock_is_preserved_exactly(self):
        self.assert_mock_reading("unreadable-load")

    def test_reading_preserves_the_callers_mock_binding(self):
        body = """
printf 'before:%s:%s\\n' "${LS_MOCK_LOAD+x}" "${LS_MOCK_LOAD-}"
read_load
printf 'after:%s:%s\\n' "${LS_MOCK_LOAD+x}" "${LS_MOCK_LOAD-}"
"""
        original_environment = dict(os.environ)
        for value in (None, "", "0.50", "unreadable-load"):
            with self.subTest(mock_load=value):
                presence = "" if value is None else "x"
                binding = "" if value is None else value
                reading = "7.25" if value is None else value
                completed = self.run_reader(value, body)
                self.assertEqual(completed.returncode, 0)
                self.assertEqual(
                    completed.stdout,
                    "before:{0}:{1}\n{2}\nafter:{0}:{1}\n".format(
                        presence, binding, reading,
                    ),
                )
                self.assertEqual(
                    completed.stderr, "LIVE_PROBE\n" if value is None else "",
                )
        self.assertEqual(dict(os.environ), original_environment)

    def run_thread_choice(self, mock_load):
        settings = """
THREADS=2
THREADS_IDLE=4
IDLE_LOAD_MAX=10
IDLE_PRESS_MAX=50
LS_MOCK_PRESSURE='10.0 deterministic-pressure'
choose_threads
"""
        return self.run_reader(mock_load, isolated_choose_threads() + settings)

    def test_empty_load_chooses_conservative_threads_without_live_probes(self):
        completed = self.run_thread_choice("")
        self.assertEqual(completed.returncode, 0)
        self.assertEqual(
            completed.stdout, "2 (load unreadable — the conservative value)",
        )
        self.assertEqual(completed.stderr, "")

    def test_quiet_load_chooses_idle_threads_without_live_probes(self):
        completed = self.run_thread_choice("0.50")
        self.assertEqual(completed.returncode, 0)
        self.assertEqual(
            completed.stdout,
            "4 (load 0.50 under 10, memory pressure 10.0% under 50% "
            "per deterministic-pressure — quiet box)",
        )
        self.assertEqual(completed.stderr, "")

    def test_invalid_load_chooses_conservative_threads_without_live_probes(self):
        completed = self.run_thread_choice("unreadable-load")
        self.assertEqual(completed.returncode, 0)
        self.assertEqual(
            completed.stdout, "2 (load unreadable — the conservative value)",
        )
        self.assertEqual(completed.stderr, "")


if __name__ == "__main__":
    unittest.main()
