#!/usr/bin/env python3
"""Check optional Spectre availability by completing a one-volt DC analysis.

Exit 0 means a verified analysis, 77 means an explicit license refusal, and
1 means a probe failure. Unexpected errors and timeouts are never skips.
"""

import math
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import tempfile

from spectre_test import parse_nutascii


PROBE_NODE = "lean_surfaces_spectre_ready"
PROBE_SOURCE = '''Lean surfaces Spectre readiness
Vprobe lean_surfaces_spectre_ready 0 DC 1
Rprobe lean_surfaces_spectre_ready 0 1k
.op
.end
'''


def diagnostic_codes(output):
    codes = []
    for line in output.splitlines():
        line = line.strip()
        if line == "Fatal error found by spectre.":
            continue
        if re.match(r"(?i)^(?:FATAL|ERROR)\b", line):
            match = re.match(r"(?i)^(?:FATAL|ERROR)\s*\(([^()\s]+)\):", line)
            codes.append(match.group(1) if match else None)
    return codes


def classify_result(returncode, output, analysis_verified):
    diagnostics = diagnostic_codes(output)
    if returncode == 0 and analysis_verified and not diagnostics:
        return 0
    if (returncode > 0 and not analysis_verified and diagnostics
            and all(code == "SPECTRE-209" for code in diagnostics)):
        return 77
    return 1


def analysis_ready(rawfile):
    rawfile = Path(rawfile)
    if not rawfile.is_file() or rawfile.is_symlink():
        return False
    try:
        text = rawfile.read_text()
        points = re.search(r"(?m)^\s*No\. Points:\s*(\d+)\s*$", text)
        if points is None or int(points.group(1)) != 1:
            return False
        names, rows = parse_nutascii(rawfile)
        if len(rows) != 1 or names.count(PROBE_NODE) != 1:
            return False
        voltage = rows[0][names.index(PROBE_NODE)]
        return math.isfinite(voltage) and abs(voltage - 1.0) <= 1e-9
    except (OSError, UnicodeError, ValueError, RuntimeError, IndexError):
        return False


def run_probe_command(command, workdir, timeout):
    process = subprocess.Popen(
        command, cwd=workdir, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        universal_newlines=True, start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
        return process.returncode, stdout + "\n" + stderr, False
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        return process.returncode, stdout + "\n" + stderr, True


def probe_spectre(binary="spectre", timeout=120):
    with tempfile.TemporaryDirectory(prefix="spectre-readiness-") as workdir:
        source = Path(workdir) / "probe.cir"
        source.write_text(PROBE_SOURCE)
        rawfile = Path(workdir) / "probe.raw"
        command = [binary, "-log", "-format", "nutascii", "-raw", str(rawfile),
                   "-outdir", workdir, "+lqtimeout", "1", "+lqsleep", "1",
                   str(source)]
        try:
            returncode, output, timed_out = run_probe_command(
                command, workdir, timeout,
            )
        except OSError as error:
            return 1, "Spectre probe could not start: %s" % error
        verified = analysis_ready(rawfile)
        receipt = "command: %s\nexit: %s\nanalysis verified: %s\n%s" % (
            shlex.join(command), returncode, verified, output,
        )
        if timed_out:
            return 1, "Spectre probe timed out after %ss\n%s" % (timeout, receipt)
        status = classify_result(returncode, output, verified)
        verdict = {0: "ready", 77: "license unavailable", 1: "failed"}[status]
        return status, "Spectre probe: %s\n%s" % (verdict, receipt)


def main():
    status, receipt = probe_spectre()
    print(receipt)
    return status


if __name__ == "__main__":
    raise SystemExit(main())
