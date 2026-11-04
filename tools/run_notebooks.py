#!/usr/bin/env python3
"""Headless executor for the lean_models Jupyter track.

Usage (any cwd; paths resolve against the repo root):

    python3 tools/run_notebooks.py [notebook.ipynb ...] [--timeout N]
                                   [--no-save]

Executes each notebook end-to-end via nbclient (default: every
``notebooks/*.ipynb``, sorted). Cells whose metadata tags contain
``expected-error`` are the tutorials' deliberately-failing cells (wrong
specs, wrong invariants — their error output is the lesson):

  * they are ALLOWED to fail (nbclient's native ``raises-exception`` tag is
    added in memory for the run, and stripped again before saving);
  * they are REQUIRED to fail — an expected-error cell that succeeds is
    reported as a failure (the tutorial would be showing a stale lesson).

Any other cell error is fatal. Executed notebooks are saved back in place
(outputs included — the failing cells' goal states stay visible on disk);
``--no-save`` checks without writing. Before saving, each cell's transient
``metadata.execution`` timestamps (nbclient bookkeeping) are stripped so a
rerun with unchanged outputs produces no metadata-only diff churn.

Exit code 0 iff every notebook ran clean. Requires nbformat + nbclient and
a ``python3`` kernelspec (ipykernel). ``lake build`` must have been run at
the repo root first — the magics reuse its artifacts. The default glob
covers every tutorial notebook, including ``03-systemverilog.ipynb``, whose
``%%svfile`` cells additionally need ``python3.12`` + pyslang (the SV
extractor) on the host.
"""

import argparse
import sys
import time
from pathlib import Path

import nbformat
from nbclient import NotebookClient
from nbclient.exceptions import CellExecutionError

REPO_ROOT = Path(__file__).resolve().parent.parent
NB_DIR = REPO_ROOT / "notebooks"
EXPECTED_TAG = "expected-error"
NATIVE_TAG = "raises-exception"


def cell_tags(cell):
    return cell.get("metadata", {}).get("tags", [])


def has_error_output(cell):
    return any(o.get("output_type") == "error" for o in cell.get("outputs", []))


def excerpt(cell, n=3):
    lines = cell.source.splitlines()
    head = "\n".join("    | " + ln for ln in lines[:n])
    return head + ("\n    | …" if len(lines) > n else "")


def run_notebook(path, timeout, save):
    nb = nbformat.read(str(path), as_version=4)

    # Mark expected-error cells with nbclient's native tolerance tag.
    added = []
    for cell in nb.cells:
        if cell.cell_type == "code" and EXPECTED_TAG in cell_tags(cell):
            if NATIVE_TAG not in cell_tags(cell):
                cell.metadata.setdefault("tags", []).append(NATIVE_TAG)
                added.append(cell)

    client = NotebookClient(
        nb,
        timeout=timeout,
        kernel_name=nb.metadata.get("kernelspec", {}).get("name", "python3"),
        allow_errors=False,
        resources={"metadata": {"path": str(path.parent)}},
    )
    t0 = time.monotonic()
    try:
        client.execute()
    except CellExecutionError as e:
        dt = time.monotonic() - t0
        idx = next(
            (i for i, c in enumerate(nb.cells)
             if c.cell_type == "code" and has_error_output(c)
             and EXPECTED_TAG not in cell_tags(c)),
            None,
        )
        print("FAIL  %s  (%.1fs)" % (path.name, dt))
        if idx is not None:
            print("  unexpected error in cell %d:" % idx)
            print(excerpt(nb.cells[idx]))
        print("  " + str(e).strip().splitlines()[-1])
        return False, dt

    dt = time.monotonic() - t0

    # Expected-error cells must actually have failed.
    ok = True
    for i, cell in enumerate(nb.cells):
        if cell.cell_type == "code" and EXPECTED_TAG in cell_tags(cell):
            if not has_error_output(cell):
                print("FAIL  %s  (%.1fs)" % (path.name, dt))
                print("  cell %d is tagged '%s' but ran WITHOUT error —"
                      % (i, EXPECTED_TAG))
                print("  the deliberate-failure lesson is stale; fix the cell"
                      " or drop the tag:")
                print(excerpt(cell))
                ok = False

    # Don't persist the in-memory tolerance tag.
    for cell in added:
        tags = cell_tags(cell)
        if NATIVE_TAG in tags:
            tags.remove(NATIVE_TAG)

    if ok:
        n_code = sum(1 for c in nb.cells if c.cell_type == "code")
        n_expected = sum(
            1 for c in nb.cells
            if c.cell_type == "code" and EXPECTED_TAG in cell_tags(c)
        )
        print("ok    %s  (%.1fs, %d code cells, %d expected-error)"
              % (path.name, dt, n_code, n_expected))

    if save:
        # Strip nbclient's per-cell execution timestamps: they change on
        # every run even when the outputs do not, and are pure diff churn.
        for cell in nb.cells:
            if cell.cell_type == "code":
                cell.metadata.pop("execution", None)
        nbformat.write(nb, str(path))
    return ok, dt


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="run_notebooks.py",
        description="Execute the tutorial notebooks headlessly; "
        "'expected-error'-tagged cells must fail, everything else must pass.",
    )
    parser.add_argument("notebooks", nargs="*", metavar="notebook.ipynb")
    parser.add_argument("--timeout", type=int, default=600,
                        help="per-cell timeout in seconds (default 600)")
    parser.add_argument("--no-save", action="store_true",
                        help="do not write executed outputs back to disk")
    opts = parser.parse_args(argv)

    if opts.notebooks:
        paths = [Path(p).resolve() for p in opts.notebooks]
    else:
        paths = sorted(NB_DIR.glob("*.ipynb"))
    paths = [p for p in paths if ".ipynb_checkpoints" not in p.parts]
    if not paths:
        print("no notebooks found under %s" % NB_DIR, file=sys.stderr)
        return 2

    failures = 0
    total = 0.0
    for p in paths:
        ok, dt = run_notebook(p, opts.timeout, save=not opts.no_save)
        total += dt
        if not ok:
            failures += 1
    print("-" * 60)
    print("%d notebook(s), %d failed, total %.1fs"
          % (len(paths), failures, total))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
