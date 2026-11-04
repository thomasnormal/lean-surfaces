#!/usr/bin/env python3
"""es_scoreboard.py — run the ES scoreboard end to end, as ONE command.

    python3 harness/es_scoreboard.py --corpus <dir> [--expect 1816] [--fuel 2000]

One command because `tools/triad.sh` splits `--gates` on `;` without
respecting quoting — an inline pipeline in a gate list becomes N false gates,
which this lane has already paid for once (`2026-08-24-es-3`).

It: checks the corpus pin by content, builds the envelope list, runs
`es-score`, and re-derives the summary with `es_score.py` so two programs
answer the same question.

**AN ABSENT CORPUS IS A REPORTED STATE, NOT A SKIP.** If the fetched corpus is
missing, this prints `not-fetched N` and FAILS. A scoreboard that quietly
passes when it scored nothing is the unexercised-gate failure, and this lane
has met that one too.
"""

import argparse
import json
import os
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PIN = os.path.join(REPO, "docs", "es-scoreboard-corpus.json")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", default=os.environ.get("ES_CORPUS", ""),
                    help="directory holding the manifest and the envelopes")
    ap.add_argument("--fuel", type=int, default=2000)
    ap.add_argument("--expect", type=int)
    ap.add_argument("--expect-passed", type=int)
    a = ap.parse_args()

    pin = json.load(open(PIN))
    if not a.corpus or not os.path.isdir(a.corpus):
        print("test262 0/%d scored  (passed 0, failed 0)" % pin["admitted"])
        print("  the zeroes, kept apart: not-fetched %d" % pin["admitted"])
        print("REFUSED: no corpus at %r. The population is pinned in %s "
              "(test262 %s, manifest sha256 %s); fetch it and pass --corpus. "
              "A scoreboard with no corpus is a number about nothing."
              % (a.corpus, os.path.relpath(PIN, REPO), pin["test262"].split()[0][:12],
                 pin["manifest_sha256"][:16]), file=sys.stderr)
        return 2

    manifest = os.path.join(a.corpus, "es-scoreboard-manifest.jsonl")
    r = subprocess.run([sys.executable, os.path.join(REPO, "harness", "es_score_corpus.py"),
                        "--check", PIN, "--manifest", manifest],
                       capture_output=True, text=True, cwd=REPO)
    sys.stderr.write(r.stderr)
    if r.returncode != 0:
        return r.returncode
    print(r.stdout.strip())

    env_dir = os.path.join(a.corpus, "es-envelopes")
    names = sorted(n for n in os.listdir(env_dir) if n.endswith(".json"))
    prelude = [os.path.join(env_dir, n) for n in names
               if n.startswith("sta-") or n.startswith("assert-")]
    if len(prelude) != 2:
        print("REFUSED: expected exactly two prelude envelopes (sta, assert), found %d"
              % len(prelude), file=sys.stderr)
        return 2
    prelude.sort(key=lambda p: 0 if "/sta-" in p else 1)   # sta.js FIRST: assert.js uses Test262Error
    tests = [os.path.join(env_dir, n) for n in names if os.path.join(env_dir, n) not in prelude]
    listing = os.path.join(a.corpus, "es-score-envelopes.txt")
    open(listing, "w").write("\n".join(tests) + "\n")

    # BUILD, then RUN — two steps, not `lake exe`.
    #
    # The first version invoked `.lake/build/bin/es-score` directly and the
    # tenure went gates-RED with "is not built" — correctly, and for a reason
    # that was mine: `es-score` is a new `lean_exe` and is NOT in the
    # lakefile's `defaultTargets`, so `lake build <all default targets>` never
    # built it. Adding it there would make every OTHER lane's triad build this
    # tier's scoreboard binary — a fleet-wide cost for one lane's gate.
    #
    # `lake exe` would build-and-run in one step, but it writes build progress
    # to STDOUT, which is the same stream the per-test lines travel on. The
    # scorer would then see a non-data line and refuse — correctly, and
    # unhelpfully. Building separately keeps the data stream clean and puts
    # any build failure in its own message.
    exe = os.path.join(REPO, ".lake", "build", "bin", "es-score")
    build = subprocess.run(["lake", "build", "es-score"], capture_output=True,
                           text=True, cwd=REPO)
    if build.returncode != 0 or not os.path.isfile(exe):
        sys.stderr.write(build.stdout + build.stderr)
        print("REFUSED: could not build es-score", file=sys.stderr)
        return 2
    run = subprocess.run([exe, str(a.fuel), ",".join(prelude), listing],
                         capture_output=True, text=True, cwd=REPO)
    score = [sys.executable, os.path.join(REPO, "harness", "es_score.py")]
    if a.expect is not None:
        score += ["--expect", str(a.expect)]
    if a.expect_passed is not None:
        score += ["--expect-passed", str(a.expect_passed)]
    second = subprocess.run(score, input=run.stdout, capture_output=True, text=True, cwd=REPO)
    sys.stdout.write(second.stdout)
    sys.stderr.write(second.stderr)
    return second.returncode


if __name__ == "__main__":
    sys.exit(main())
