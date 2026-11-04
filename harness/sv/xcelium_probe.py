#!/usr/bin/env python3
"""Admit an optional Xcelium oracle only after a completed SV simulation.

Exit 0 means ready, 77 means an explicit license refusal, and 1 means the
probe failed. Timeouts and unexpected diagnostics are never availability skips.
"""

import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import tempfile


SENTINEL = "LEAN_SURFACES_XCELIUM_READY"
PROBE_SOURCE = '''module probe;
  initial begin
    $display("LEAN_SURFACES_XCELIUM_READY");
    $finish;
  end
endmodule
'''


def classify_result(returncode, output):
    completed = SENTINEL in output.splitlines()
    diagnostics = re.findall(r"\*[EF],([A-Z0-9_]+):", output)
    if returncode == 0 and completed and not diagnostics:
        return 0
    if (returncode > 0 and not completed and diagnostics
            and all(code == "NOLICN" for code in diagnostics)):
        return 77
    return 1


def run_probe_command(command, workdir, timeout):
    process = subprocess.Popen(
        command, cwd=workdir, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        universal_newlines=True, start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
        return process.returncode, stdout + stderr, False
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        return process.returncode, stdout + stderr, True


def probe_xcelium(binary="xrun", timeout=120):
    with tempfile.TemporaryDirectory(prefix="xcelium-readiness-") as workdir:
        source = Path(workdir) / "probe.sv"
        source.write_text(PROBE_SOURCE)
        command = [binary, "-sv", "-q", "-timescale", "1ns/1ns", str(source)]
        try:
            returncode, output, timed_out = run_probe_command(
                command, workdir, timeout,
            )
        except OSError as error:
            return 1, "Xcelium probe could not start: %s" % error
        logfile = Path(workdir) / "xrun.log"
        if logfile.exists():
            output += "\n" + logfile.read_text(errors="replace")
        receipt = "command: %s\nexit: %s\n%s" % (
            shlex.join(command), returncode, output,
        )
        if timed_out:
            return 1, "Xcelium probe timed out after %ss\n%s" % (timeout, receipt)
        status = classify_result(returncode, output)
        verdict = {0: "ready", 77: "license unavailable", 1: "failed"}[status]
        return status, "Xcelium probe: %s\n%s" % (verdict, receipt)


def main():
    status, receipt = probe_xcelium()
    print(receipt)
    return status


if __name__ == "__main__":
    raise SystemExit(main())
