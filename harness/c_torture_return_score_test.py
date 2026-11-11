#!/usr/bin/env python3
"""Pin the torture scoreboard's main-return classification."""

import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    with tempfile.TemporaryDirectory(prefix="c-torture-return-") as temp:
        source = Path(temp) / "return.c"
        source.write_text("int main(void) { return 7; }\n")
        envelope = Path(temp) / "return.json"
        extract = subprocess.run(["python3", "extractors/c/extract.py", str(source), "-o", str(envelope)],
                                 cwd=ROOT, text=True, capture_output=True)
        if extract.returncode:
            raise RuntimeError(extract.stderr)
        payload = json.loads(envelope.read_text())
        manifest = Path(temp) / "manifest.json"
        manifest.write_text(json.dumps({"tests": [{"name": "return", "status": "parsed",
                                                     "envelope": str(envelope)}]}))
        run = subprocess.run(["lake", "env", "lean", "-j", "1", "--run",
                              "LeanModels/C/TortureMain.lean", str(manifest)],
                             cwd=ROOT, text=True, capture_output=True)
        if run.returncode != 0 or "failed" not in run.stdout:
            raise RuntimeError("expected failed score, got %s %r %r" %
                               (run.returncode, run.stdout, run.stderr))
        print("main-return-7: failed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
