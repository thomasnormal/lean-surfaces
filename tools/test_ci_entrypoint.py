#!/usr/bin/env python3
"""Check the root CI entry point without invoking the real CI driver."""

import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest


ENTRYPOINT = Path(__file__).resolve().parents[1] / "check.sh"


class CiEntrypointTests(unittest.TestCase):
    def setUp(self):
        self.temporary_directory = tempfile.TemporaryDirectory(
            prefix="ci-entrypoint-tests-"
        )
        self.addCleanup(self.temporary_directory.cleanup)
        self.checkout = Path(self.temporary_directory.name) / "checkout with spaces"
        self.checkout.mkdir()
        self.entrypoint = self.checkout / "check.sh"
        shutil.copy2(ENTRYPOINT, self.entrypoint)
        self.tools_directory = self.checkout / "tools"
        self.tools_directory.mkdir()
        probe = (
            "import json, os, sys; "
            "print(json.dumps({'arguments': sys.argv[1:], 'directory': os.getcwd(), "
            "'environment': dict(os.environ)})); "
            "sys.exit(int(os.environ.get('CI_TEST_EXIT', '0')))"
        )
        driver = self.tools_directory / "ci.sh"
        driver.write_text(
            '#!/usr/bin/env bash\n'
            'cd "$(dirname "$0")/.." || exit 99\n'
            'exec "$CI_TEST_PYTHON" -c ' + shlex.quote(probe) + ' "$@"\n',
            encoding="utf-8",
        )
        driver.chmod(0o755)
        self.caller_directory = Path(self.temporary_directory.name) / "caller elsewhere"
        self.caller_directory.mkdir()

    def invoke(self, arguments=(), environment=None):
        child_environment = os.environ.copy()
        child_environment["CI_TEST_PYTHON"] = sys.executable
        if environment:
            child_environment.update(environment)
        result = subprocess.run(
            [str(self.entrypoint), *arguments],
            cwd=self.caller_directory,
            env=child_environment,
            capture_output=True,
            text=True,
            timeout=10,
        )
        self.assertEqual(result.stderr, "")
        return result, json.loads(result.stdout)

    def test_entrypoint_is_executable(self):
        self.assertTrue(os.access(ENTRYPOINT, os.X_OK))

    def test_invocation_from_elsewhere_with_checkout_spaces(self):
        result, observed = self.invoke()
        self.assertEqual(result.returncode, 0)
        self.assertEqual(observed["arguments"], [])
        self.assertEqual(observed["directory"], str(self.checkout))

    def test_forwards_arguments_without_reinterpreting_them(self):
        arguments = (
            "--require-build",
            "--verify-guards",
            "argument with spaces",
            "",
            "$(exit 86)",
            "*.lean",
            "quote'and\"double",
        )
        result, observed = self.invoke(arguments)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(observed["arguments"], list(arguments))

    def test_preserves_environment_and_ci_self_test_sentinel(self):
        environment = {
            "CI_TEST_MARKER": "value with spaces and $dollars",
            "LS_CI_SELF_TEST": "inherited sentinel",
        }
        result, observed = self.invoke(environment=environment)
        self.assertEqual(result.returncode, 0)
        for name, value in environment.items():
            with self.subTest(variable=name):
                self.assertEqual(observed["environment"][name], value)

    def test_preserves_nonzero_driver_exit_status(self):
        for exit_status in (1, 2, 7, 127):
            with self.subTest(exit_status=exit_status):
                result, observed = self.invoke(
                    environment={"CI_TEST_EXIT": str(exit_status)}
                )
                self.assertEqual(result.returncode, exit_status)
                self.assertEqual(observed["arguments"], [])


if __name__ == "__main__":
    unittest.main()
