#!/usr/bin/env python3
"""Build the SV grammar census used by ``docs/sv-coverage.md``.

The frontend is pyslang.  We walk the checked-in SV examples, keep the first
witness for every ``SyntaxKind`` (tokens are excluded), extract each witness,
and run the resulting envelope through the self-check interpreter.  A grammar
row is ``MATCH`` when parsing/extraction and Lean execution both succeed;
``REFUSE`` records the interpreter's loud boundary.  The witness path is
retained so every number is reproducible and reviewable.
"""

import argparse
import importlib.util
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path

from pyslang.syntax import SyntaxTree

REPO = Path(__file__).resolve().parents[1]
DEFAULT_ROOT = REPO / "Examples" / "system-verilog"
TIMED_RUNNER = REPO / "harness" / "sv" / "conformance" / "timed_runner.lean"
def load_extractor():
    path = REPO / "extractors" / "sv" / "extract.py"
    spec = importlib.util.spec_from_file_location("sv_extractor", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def witnesses(root):
    found = {}
    for source in sorted(Path(root).rglob("*.sv")):
        try:
            text = source.read_text(encoding="utf-8")
            tree = SyntaxTree.fromText(text, name=str(source))
            def visit(node):
                kind = str(getattr(node, "kind", ""))
                if kind.startswith("SyntaxKind."):
                    found.setdefault(kind, source)
            tree.root.visit(visit)
        except Exception:
            # A malformed/unsupported source is still represented by the
            # extractor census; it cannot be a frontend grammar witness.
            continue
    return found


def run_batch(envelopes, fuel):
    runner = REPO / "harness" / "sv" / "conformance" / "runner.lean"
    listing = Path(tempfile.mktemp(prefix="sv-grammar-list-", suffix=".txt"))
    listing.write_text("".join(str(p) + "\n" for p in envelopes), encoding="utf-8")
    try:
        import subprocess
        env = os.environ.copy()
        env.setdefault("LEAN_NUM_THREADS", "1")
        p = subprocess.run(["systemd-run", "--user", "--scope", "-q",
                            "-p", "MemoryMax=24G", "-p", "CPUQuota=800%",
                            "lake", "env", "lean", "-j", "1",
                            "--run", str(runner), "--batch", str(listing),
                            "--fuel", str(fuel)], cwd=str(REPO), capture_output=True,
                           text=True, timeout=1800, env=env)
        if p.returncode:
            raise RuntimeError("self-check grammar runner failed (%d):\n%s\n%s" %
                               (p.returncode, p.stdout[-2000:], p.stderr[-2000:]))
        out = {}
        current = None
        for line in p.stdout.splitlines():
            if line.startswith("=== BEGIN "):
                current = line[len("=== BEGIN "):]
                out[current] = {"lines": []}
            elif line.startswith("=== END ") and current is not None:
                tail = line[len("=== END "):]
                path, status = tail.split(" status=", 1)
                parts = status.split(" ", 1)
                out[path]["status"] = parts[0]
                out[path]["detail"] = parts[1] if len(parts) == 2 else ""
                current = None
            elif current is not None:
                out[current]["lines"].append(line)
        return out
    finally:
        try:
            listing.unlink()
        except OSError:
            pass


def run_timed_batch(envelopes, fuel, ticks=16):
    """Run process witnesses through the scheduler-facing timed runner."""
    listing = Path(tempfile.mktemp(prefix="sv-grammar-timed-list-", suffix=".txt"))
    listing.write_text("".join(str(p) + "\n" for p in envelopes), encoding="utf-8")
    try:
        import subprocess
        env = os.environ.copy()
        env.setdefault("LEAN_NUM_THREADS", "1")
        p = subprocess.run(["systemd-run", "--user", "--scope", "-q",
                            "-p", "MemoryMax=24G", "-p", "CPUQuota=800%",
                            "lake", "env", "lean", "-j", "1", "--run",
                            str(TIMED_RUNNER), "--batch", str(listing),
                            "--fuel", str(fuel), "--ticks", str(ticks)],
                           cwd=str(REPO), capture_output=True, text=True,
                           timeout=1800, env=env)
        if p.returncode:
            raise RuntimeError("timed self-check grammar runner failed (%d):\n%s\n%s" %
                               (p.returncode, p.stdout[-2000:], p.stderr[-2000:]))
        out = {}
        current = None
        for line in p.stdout.splitlines():
            if line.startswith("=== BEGIN "):
                current = line[len("=== BEGIN "):]
                out[current] = {"lines": []}
            elif line.startswith("=== END ") and current is not None:
                tail = line[len("=== END "):]
                path, status = tail.split(" status=", 1)
                parts = status.split(" ", 1)
                out[path]["status"] = parts[0]
                out[path]["detail"] = parts[1] if len(parts) == 2 else ""
                current = None
            elif current is not None:
                out[current]["lines"].append(line)
        return out
    finally:
        try:
            listing.unlink()
        except OSError:
            pass


def needs_timed_runner(envelope):
    """Use the scheduler for retained process and timing-control witnesses."""
    try:
        payload = json.loads(Path(envelope).read_text(encoding="utf-8"))
        modules = payload.get("design", {}).get("modules", [])
        processes = modules[0].get("processes", []) if len(modules) == 1 else []
        process_kinds = {"Always", "AlwaysEvent", "AlwaysImplicit", "AlwaysComb", "AlwaysLatch",
                         "Assign", "AlwaysPosedge", "AlwaysFF"}

        def has_timing(node):
            if isinstance(node, dict):
                if node.get("kind") in ("Delay", "WaitEvent", "WaitCond", "Strobe",
                                         "Monitor"):
                    return True
                return any(has_timing(value) for value in node.values())
            if isinstance(node, list):
                return any(has_timing(value) for value in node)
            return False

        return any(p.get("kind") in process_kinds or has_timing(p.get("body"))
                   for p in processes)
    except (OSError, ValueError, TypeError):
        return False


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default=os.environ.get("SV_GRAMMAR_ROOT", str(DEFAULT_ROOT)))
    ap.add_argument("--fuel", type=int, default=1000000)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)
    found = witnesses(args.root)
    if not found:
        raise SystemExit("sv_grammar_census: no pyslang SyntaxKind witnesses")
    extractor = load_extractor()
    work = Path(tempfile.mkdtemp(prefix="sv-grammar-"))
    envelopes, metadata = [], []
    try:
        for i, (kind, source) in enumerate(sorted(found.items())):
            target = work / ("witness_%04d.sv" % i)
            shutil.copyfile(source, target)
            try:
                extractor.process_file(str(target))
                envelope = Path(str(target) + ".json")
                envelopes.append(envelope)
                metadata.append((kind, source, envelope, "parsed"))
            except Exception as exc:
                metadata.append((kind, source, None, "extract-error: %s" % exc))
        standard = [e for _, _, e, status in metadata
                    if e is not None and not needs_timed_runner(e)]
        timed = [e for _, _, e, status in metadata
                 if e is not None and needs_timed_runner(e)]
        model = {}
        if standard:
            model.update(run_batch(standard, args.fuel))
        if timed:
            model.update(run_timed_batch(timed, args.fuel))
        rows = []
        for kind, source, envelope, frontend in metadata:
            if envelope is None:
                rows.append({"kind": kind, "witness": str(source.relative_to(REPO)),
                             "frontend": frontend, "model": "extract-error",
                             "verdict": "REFUSE", "detail": frontend})
                continue
            m = model.get(str(envelope), {"status": "missing", "detail": "runner omitted witness"})
            status = m["status"]
            verdict = "MATCH" if frontend == "parsed" and status == "ok" else "REFUSE"
            rows.append({"kind": kind, "witness": str(source.relative_to(REPO)),
                         "frontend": frontend, "model": status, "verdict": verdict,
                         "detail": m.get("detail", "")})
        result = {"root": str(Path(args.root).resolve()), "witnesses": len(rows),
                  "match": sum(r["verdict"] == "MATCH" for r in rows),
                  "refuse": sum(r["verdict"] == "REFUSE" for r in rows),
                  "rows": rows}
        if args.json:
            print(json.dumps(result, sort_keys=True))
        else:
            print("%d SyntaxKind witnesses: %d MATCH, %d REFUSE" %
                  (result["witnesses"], result["match"], result["refuse"]))
            for row in rows:
                print("%-48s %-7s %s" % (row["kind"], row["verdict"], row["witness"]))
        return 0
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        print("sv_grammar_census: ERROR: %s" % exc, file=sys.stderr)
        sys.exit(2)
