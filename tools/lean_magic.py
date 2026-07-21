"""IPython magics for the lean_models Jupyter track.

Load with::

    %load_ext lean_magic          # tools/ must be on sys.path

Magics provided (see notebooks/01-pipeline.ipynb for the guided tour):

``%%pyfile <name>.py``
    Write the cell body to the scratch working dir ``notebooks/work/``
    (gitignored), run the extractor on it, and report the envelope summary
    inline: functions found (with parameters) and any ``Unsupported`` nodes
    or per-function restrictions.  On success the persistent import header
    (``NotebookHeader``) is recompiled so subsequent ``%%lean`` cells load
    every extracted program from a single precompiled ``.olean``.

``%%lean [<name>]``
    Treat the cell as Lean code.  It is wrapped in a temp module
    (``import NotebookHeader`` + ``open LeanModels LeanModels.Python`` —
    the header carries ``import LeanModels`` and one ``load_program`` line
    per extracted file), checked with the toolchain's ``lean`` (cwd = repo
    root, env from ``lake env``), and the result is displayed prettified:
    on success any ``#py_check`` / ``#eval`` / trace output, on failure the
    error *with its goal state* — the whole point: iterate an invariant and
    see the stuck residual goal.  A failing cell raises ``LeanCellError``
    after displaying, so headless runners (tools/run_notebooks.py) see it.
    The optional ``<name>`` names the temp module for nicer messages.

``%pyrun <fn>(<args>)  [--fuel N]``
    Run the function through the verified interpreter via the
    ``leanmodels-run`` CLI on the working dir's envelope; pretty-print the
    canonical one-line JSON result.  ``<fn>`` may be dotted
    (``pymath.floordiv(-7, 2)``) to pick a file when names are ambiguous.

``%pydiff <fn> <args...>``
    Run BOTH CPython (on the working ``.py`` file, in a subprocess) and the
    Lean runner on the same call; show the two canonical outcomes side by
    side with a MATCH / MISMATCH verdict.  This is the project's
    differential-testing methodology in one line.  A MISMATCH raises
    ``DiffMismatchError`` after the table is displayed — a failed
    differential test is a failure, so headless runs
    (tools/run_notebooks.py) catch semantic regressions in untagged cells;
    tag a cell ``expected-error`` if the mismatch itself is the lesson.

Everything is anchored at the repo root (parent of ``tools/``); the magics
work regardless of the notebook server's cwd.  Python 3.9 compatible.

Extractor-side note (documented here because ``%%pyfile`` invokes it):
``extractors/python/extract.py`` embeds the source path in the companion
file's ``/- … -/`` header comment.  A path containing ``/-`` (any directory
segment starting with ``-``, e.g. under some scratch roots) would open a
*nested* Lean block comment — the extractor now detects such paths and
switches the whole header to inert ``--`` line comments (regression-tested
in the extractor).  The magics were always structurally immune anyway:
``%%pyfile`` names are ``STEM_RE``-validated identifiers extracted at the
repo-relative path ``notebooks/work/<name>.py``.
"""

import ast
import hashlib
import html
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
from pathlib import Path

from IPython.core.magic import Magics, cell_magic, line_magic, magics_class
from IPython.display import HTML, display

REPO_ROOT = Path(__file__).resolve().parent.parent
WORK_DIR = REPO_ROOT / "notebooks" / "work"
CELLS_DIR = WORK_DIR / "cells"
EXTRACTOR = REPO_ROOT / "extractors" / "python" / "extract.py"
RUNNER_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "leanmodels-run"
HEADER_NAME = "NotebookHeader"
HEADER_CACHE = WORK_DIR / "header_cache.meta"

STEM_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
MSG_RE = re.compile(
    r"^(?P<path>\S+?\.lean):(?P<line>\d+):(?P<col>\d+): "
    r"(?P<sev>error|warning|info): ?(?P<text>.*)$"
)
FUEL_RE = re.compile(r"\s+--fuel\s+(\d+)\s*$")

LEAN_CELL_TIMEOUT = 600
RUNNER_TIMEOUT = 120
CPYTHON_TIMEOUT = 15

# Canonicalizing CPython driver run in a subprocess by %pydiff (mirrors
# harness/diff_test.py: bool before int, UnboundLocalError -> NameError).
_CPY_DRIVER = r"""
import importlib.util, json, sys
path, fn = sys.argv[1], sys.argv[2]
args = [int(a) for a in sys.argv[3:]]
spec = importlib.util.spec_from_file_location("nbdiff_mod", path)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
def canon(v):
    if isinstance(v, bool):
        return {"t": "bool", "v": v}
    if isinstance(v, int):
        return {"t": "int", "v": str(v)}
    if isinstance(v, str):
        return {"t": "str", "v": v}
    if v is None:
        return {"t": "none"}
    if isinstance(v, list):
        return {"t": "list", "v": [canon(x) for x in v]}
    if isinstance(v, tuple):
        return {"t": "tuple", "v": [canon(x) for x in v]}
    raise ValueError("unmappable value of type %s" % type(v).__name__)
f = getattr(mod, fn, None)
if f is None:
    print(json.dumps({"status": "harness-error", "msg": "no function %r" % fn}))
    sys.exit(0)
try:
    v = f(*args)
except Exception as e:
    name = type(e).__name__
    if name == "UnboundLocalError":
        name = "NameError"
    print(json.dumps({"status": "exn", "exn": name}))
    sys.exit(0)
try:
    print(json.dumps({"status": "ok", "value": canon(v)}))
except ValueError as e:
    print(json.dumps({"status": "unmappable", "msg": str(e)}))
"""


class LeanCellError(Exception):
    """A %%lean cell reported errors (details were displayed above)."""


class ExtractionError(Exception):
    """A %%pyfile cell could not be extracted (details were displayed above)."""


class DiffMismatchError(Exception):
    """A %pydiff comparison found CPython and the Lean interpreter
    disagreeing (the side-by-side table was displayed above)."""


# ---------------------------------------------------------------------------
# Small display helpers (inline styles only; theme-neutral colors)
# ---------------------------------------------------------------------------

_SEV_COLOR = {
    "error": "#c62828",
    "warning": "#e6a817",
    "info": "#1976d2",
    "output": "#7a7a7a",
    "ok": "#2e7d32",
}


def _esc(s):
    return html.escape(str(s), quote=False)


def _banner(color, title, sub=None):
    subhtml = (
        '<span style="color:#888;font-size:85%%;margin-left:0.8em">%s</span>'
        % _esc(sub)
        if sub
        else ""
    )
    return (
        '<div style="font-family:monospace;font-size:13px;margin:2px 0">'
        '<span style="color:%s;font-weight:bold">%s</span>%s</div>'
        % (color, _esc(title), subhtml)
    )


def _block(color, label, body):
    label_html = (
        '<div style="color:%s;font-weight:bold;margin-bottom:2px">%s</div>'
        % (color, _esc(label))
        if label
        else ""
    )
    return (
        '<div style="border-left:3px solid %s;padding:2px 0 2px 10px;'
        'margin:4px 0;font-family:monospace;font-size:13px">%s'
        '<pre style="margin:0;white-space:pre-wrap;line-height:1.35">%s</pre>'
        "</div>" % (color, label_html, _esc(body))
    )


def _show(*fragments):
    display(HTML("".join(fragments)))


def _usage_error(msg):
    """Show a readable error banner, then return the UsageDisplayed to raise
    (keeps the class contract: the message was displayed before the raise)."""
    _show(_banner(_SEV_COLOR["error"], msg))
    return UsageDisplayed(msg)


# ---------------------------------------------------------------------------
# The magics
# ---------------------------------------------------------------------------

@magics_class
class LeanMagics(Magics):
    def __init__(self, shell):
        super().__init__(shell)
        self._env = None          # captured `lake env` environment
        self._lean_exe = None     # resolved lean binary
        self._header_ok = False   # NotebookHeader.olean is current
        self._header_err = None   # last header compile error text
        self._cell_counter = 0
        self.timings = []         # (magic, name, seconds) — latency log
        WORK_DIR.mkdir(parents=True, exist_ok=True)
        CELLS_DIR.mkdir(parents=True, exist_ok=True)

    # -- environment -------------------------------------------------------

    def _lake_env(self):
        """Environment for direct `lean` calls: `lake env` captured once
        (saves ~0.3s/cell of lake startup), work dir appended to LEAN_PATH."""
        if self._env is not None:
            return self._env
        env = dict(os.environ)
        try:
            proc = subprocess.run(
                ["lake", "env"], cwd=str(REPO_ROOT), capture_output=True,
                text=True, timeout=120,
            )
            if proc.returncode == 0:
                for ln in proc.stdout.splitlines():
                    if "=" in ln:
                        k, _, v = ln.partition("=")
                        env[k] = v
        except (OSError, subprocess.TimeoutExpired):
            pass  # fall through: plain environ + `lake env lean` fallback
        env["LEAN_PATH"] = (
            env.get("LEAN_PATH", "") + os.pathsep + str(WORK_DIR)
        ).lstrip(os.pathsep)
        self._env = env
        self._lean_exe = shutil.which("lean", path=env.get("PATH"))
        return env

    def _run_lean(self, path, extra_args=()):
        """Run `lean` on a file (cwd = repo root). Returns (rc, text, secs)."""
        env = self._lake_env()
        cmd = (
            [self._lean_exe] if self._lean_exe else ["lake", "env", "lean"]
        ) + list(extra_args) + [str(path)]
        t0 = time.monotonic()
        try:
            proc = subprocess.run(
                cmd, cwd=str(REPO_ROOT), env=env, capture_output=True,
                text=True, timeout=LEAN_CELL_TIMEOUT,
            )
        except subprocess.TimeoutExpired:
            return (124, "lean timed out after %ds on %s"
                    % (LEAN_CELL_TIMEOUT, Path(path).name),
                    time.monotonic() - t0)
        dt = time.monotonic() - t0
        out = (proc.stdout or "") + (proc.stderr or "")
        return proc.returncode, out, dt

    # -- envelope bookkeeping ----------------------------------------------

    def _envelopes(self):
        """[(stem, json_path)] for every extracted envelope in the work dir."""
        out = []
        for p in sorted(WORK_DIR.glob("*.json")):
            if STEM_RE.match(p.stem) and p.stem != HEADER_NAME:
                out.append((p.stem, p))
        return out

    def _functions_of(self, json_path):
        try:
            body = json.loads(json_path.read_text(encoding="utf-8"))["module"]["body"]
        except (OSError, ValueError, KeyError):
            return []
        return [s["name"] for s in body if s.get("kind") == "FunctionDef"]

    def _find_function(self, fname, modstem=None):
        """Locate the envelope defining `fname`. Returns (stem, json_path)."""
        envs = self._envelopes()
        if modstem is not None:
            for stem, p in envs:
                if stem == modstem:
                    if fname in self._functions_of(p):
                        return stem, p
                    raise _usage_error(
                        "'%s.json' defines no function '%s'" % (stem, fname)
                    )
            raise _usage_error(
                "no envelope '%s.json' in notebooks/work/ — extract it with "
                "%%%%pyfile %s.py first" % (modstem, modstem)
            )
        hits = [(stem, p) for stem, p in envs if fname in self._functions_of(p)]
        if not hits:
            raise _usage_error(
                "no extracted file defines '%s' — extract one with "
                "%%%%pyfile first (work dir: notebooks/work/)" % fname
            )
        if len(hits) > 1:
            raise _usage_error(
                "'%s' is defined in several files (%s) — disambiguate as "
                "<file>.%s(...)" % (fname, ", ".join(s for s, _ in hits), fname)
            )
        return hits[0]

    # -- the persistent header ---------------------------------------------

    def _header_key(self):
        parts = []
        for stem, p in self._envelopes():
            h = hashlib.sha256(p.read_bytes()).hexdigest()
            parts.append("%s %s" % (stem, h))
        return "\n".join(parts)

    def _rebuild_header(self, report=True):
        """(Re)compile NotebookHeader.olean iff the envelope set changed.
        Returns 'cached' | 'compiled' | 'failed' | 'empty'."""
        envs = self._envelopes()
        if not envs:
            self._header_ok = False
            return "empty"
        key = self._header_key()
        olean = WORK_DIR / (HEADER_NAME + ".olean")
        if (
            olean.exists()
            and HEADER_CACHE.exists()
            and HEADER_CACHE.read_text(encoding="utf-8") == key
        ):
            self._header_ok = True
            return "cached"
        lines = ["import LeanModels"]
        for stem, p in envs:
            rel = p.relative_to(REPO_ROOT).as_posix()
            lines.append('load_program %s from "%s"' % (stem, rel))
        src = WORK_DIR / (HEADER_NAME + ".lean")
        src.write_text("\n".join(lines) + "\n", encoding="utf-8")
        rc, out, dt = self._run_lean(
            src, extra_args=["--root=" + str(WORK_DIR), "-o", str(olean)]
        )
        if rc == 0:
            HEADER_CACHE.write_text(key, encoding="utf-8")
            self._header_ok = True
            self._header_err = None
            if report:
                _show(_banner(
                    _SEV_COLOR["ok"], "import header recompiled",
                    "%d program(s), %.1fs — %%%%lean cells now import it "
                    "precompiled" % (len(envs), dt),
                ))
            return "compiled"
        self._header_ok = False
        self._header_err = out
        if report:
            _show(
                _banner(_SEV_COLOR["warning"], "import header failed to compile",
                        "%%lean cells fall back to per-cell load_program"),
                _block(_SEV_COLOR["warning"], None, out.strip()),
            )
        return "failed"

    # -- %%pyfile ----------------------------------------------------------

    @cell_magic
    def pyfile(self, line, cell):
        """%%pyfile <name>.py — write the cell to notebooks/work/, extract."""
        name = line.strip()
        if name.endswith(".py"):
            name = name[:-3]
        if not STEM_RE.match(name) or "/" in name or name == HEADER_NAME:
            _show(_banner(
                _SEV_COLOR["error"], "usage: %%pyfile <name>.py",
                "name must be a bare identifier (it becomes the Lean module "
                "constant)",
            ))
            raise UsageDisplayed("bad %%pyfile name: %r" % line.strip())
        py_path = WORK_DIR / (name + ".py")
        py_path.write_text(cell if cell.endswith("\n") else cell + "\n",
                           encoding="utf-8")
        rel = py_path.relative_to(REPO_ROOT).as_posix()
        python3 = shutil.which("python3") or sys.executable
        t0 = time.monotonic()
        proc = subprocess.run(
            [python3, str(EXTRACTOR), rel, "--companion-dir", "notebooks/work"],
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=60,
        )
        dt = time.monotonic() - t0
        self.timings.append(("pyfile", name, dt))
        if proc.returncode != 0:
            _show(
                _banner(_SEV_COLOR["error"], "extraction failed: %s.py" % name),
                _block(_SEV_COLOR["error"], None,
                       (proc.stderr or proc.stdout).strip()),
            )
            raise UsageDisplayed("extractor failed for %s.py" % name)

        envl = json.loads((WORK_DIR / (name + ".json")).read_text(encoding="utf-8"))
        frags = [_banner(
            _SEV_COLOR["ok"], "extracted %s.py → %s.json" % (name, name),
            "%.2fs, schema v%s, sha256 %s…" % (
                dt, envl.get("schema_version", "?"),
                envl.get("source_sha256", "")[:12]),
        )]
        fn_lines, notes = [], []
        for s in envl["module"]["body"]:
            if s.get("kind") == "FunctionDef":
                fn_lines.append(
                    "def %s(%s)" % (s["name"],
                                    ", ".join(a["arg"] for a in s["args"]))
                )
                if s.get("args_unsupported"):
                    notes.append("%s: unsupported argument form (%s)"
                                 % (s["name"], s["args_unsupported"]))
                if s.get("locals_unsupported"):
                    notes.append("%s: %s" % (s["name"], s["locals_unsupported"]))
            else:
                notes.append("top-level %s statement (recorded, ignored by the "
                             "interpreter)" % s.get("kind"))
        frags.append(_block(
            _SEV_COLOR["info"], "functions",
            "\n".join(fn_lines) if fn_lines else "(none)",
        ))
        unsupported = []
        self._walk_unsupported(envl["module"], unsupported)
        if unsupported:
            frags.append(_block(
                _SEV_COLOR["warning"],
                "Unsupported nodes (representable, will not evaluate)",
                "\n".join(unsupported),
            ))
        if notes:
            frags.append(_block(_SEV_COLOR["warning"], "notes", "\n".join(notes)))
        nblocks = len(envl.get("lean_blocks", []))
        if nblocks:
            frags.append(_block(
                _SEV_COLOR["info"], None,
                "%d `# lean[` block(s) found — in notebooks, prefer %%%%lean "
                "cells" % nblocks,
            ))
        _show(*frags)
        self._rebuild_header()

    def _walk_unsupported(self, node, acc):
        if isinstance(node, dict):
            if node.get("kind") == "Unsupported":
                line = node.get("span", {}).get("lineno", "?")
                acc.append("line %s: %s   %s" % (
                    line, node.get("py_kind", "?"),
                    (node.get("text") or "").splitlines()[0][:80]
                    if node.get("text") else ""))
            if node.get("kind") == "Call" and node.get("call_unsupported"):
                line = node.get("span", {}).get("lineno", "?")
                acc.append("line %s: call with %s" % (line, node["call_unsupported"]))
            for v in node.values():
                self._walk_unsupported(v, acc)
        elif isinstance(node, list):
            for v in node:
                self._walk_unsupported(v, acc)

    # -- %%lean ------------------------------------------------------------

    @cell_magic
    def lean(self, line, cell):
        """%%lean [<name>] — check the cell as Lean code against the loaded
        programs; show #py_check/#eval output or the error with goal state."""
        name = line.strip()
        if name and (not STEM_RE.match(name) or name == HEADER_NAME):
            _show(_banner(_SEV_COLOR["error"],
                          "usage: %%lean [<name>]  (bare identifier)"))
            raise UsageDisplayed("bad %%lean name: %r" % name)
        if not name:
            self._cell_counter += 1
            name = "cell_%d" % self._cell_counter

        if not self._header_ok:
            self._rebuild_header(report=False)
        preamble = []
        if self._header_ok:
            preamble.append("import %s" % HEADER_NAME)
        else:
            preamble.append("import LeanModels")
            for stem, p in self._envelopes():
                rel = p.relative_to(REPO_ROOT).as_posix()
                preamble.append('load_program %s from "%s"' % (stem, rel))
        preamble.append("open LeanModels LeanModels.Python")
        preamble.append("")
        offset = len(preamble)

        path = CELLS_DIR / (name + ".lean")
        path.write_text("\n".join(preamble) + "\n" + cell +
                        ("" if cell.endswith("\n") else "\n"), encoding="utf-8")
        rc, out, dt = self._run_lean(path)
        self.timings.append(("lean", name, dt))

        blocks = self._parse_messages(out, path, offset)
        frags = []
        nerr = sum(1 for sev, _, _ in blocks if sev == "error")
        if rc == 0 and nerr == 0:
            frags.append(_banner(_SEV_COLOR["ok"],
                                 "✓ %s: all checks passed" % name,
                                 "%.1fs" % dt))
            if not blocks:
                frags.append(_block(_SEV_COLOR["output"], None,
                                    "(no output — definitions compiled, "
                                    "#py_check guards held, proofs checked)"))
        else:
            frags.append(_banner(
                _SEV_COLOR["error"],
                "✗ %s: %d error(s)" % (name, max(nerr, 1)), "%.1fs" % dt))
        for sev, label, body in blocks:
            frags.append(_block(_SEV_COLOR.get(sev, "#7a7a7a"), label, body))
        _show(*frags)
        if rc != 0 or nerr:
            raise LeanCellError(
                "Lean reported %d error(s) in %s — see the goal state above"
                % (max(nerr, 1), name)) from None
        return None

    def _parse_messages(self, out, path, offset):
        """Split lean CLI output into (severity, label, body) blocks, mapping
        file lines back to cell lines (bare lines, e.g. #eval output that lean
        prints without a position, become 'output' blocks)."""
        blocks = []
        cur = None  # [sev, label, [lines]]
        for ln in out.splitlines():
            m = MSG_RE.match(ln)
            if m:
                if cur:
                    blocks.append((cur[0], cur[1], "\n".join(cur[2]).rstrip()))
                sev = m.group("sev")
                fline = int(m.group("line"))
                cline = max(fline - offset, 1)
                where = ("cell line %d" % cline
                         if Path(m.group("path")).name == path.name
                         else Path(m.group("path")).name + (":%d" % fline))
                label = "%s (%s)" % (sev, where)
                cur = [sev, label, [m.group("text")] if m.group("text") else []]
            else:
                if cur is None:
                    cur = ["output", None, []]
                cur[2].append(ln)
        if cur:
            body = "\n".join(cur[2]).rstrip()
            if body or cur[1]:
                blocks.append((cur[0], cur[1], body))
        return blocks

    # -- %pyrun ------------------------------------------------------------

    @line_magic
    def pyrun(self, line):
        """%pyrun <fn>(<args>) [--fuel N] — run on the verified interpreter."""
        fuel = None
        m = FUEL_RE.search(line)
        if m:
            fuel = int(m.group(1))
            line = line[: m.start()]
        try:
            modstem, fname, args = self._parse_call(line)
        except (SyntaxError, ValueError) as e:
            _show(_banner(_SEV_COLOR["error"],
                          "usage: %pyrun fn(1, 2)  or  %pyrun file.fn(1, 2) "
                          "[--fuel N]", str(e)))
            raise UsageDisplayed(str(e)) from None
        stem, json_path = self._find_function(fname, modstem)
        res, dt = self._runner(json_path, fname, args, fuel)
        self.timings.append(("pyrun", fname, dt))
        call = "%s(%s)" % (fname, ", ".join(str(a) for a in args))
        _show(
            _banner(_SEV_COLOR["ok" if res.get("status") == "ok" else "warning"],
                    "%s ⇒ %s" % (call, _pretty_res(res)),
                    "leanmodels-run on %s.json, %.2fs" % (stem, dt)),
            _block(_SEV_COLOR["output"], None, json.dumps(res)),
        )
        return None

    def _parse_call(self, line):
        tree = ast.parse(line.strip(), mode="eval")
        if not isinstance(tree.body, ast.Call):
            raise ValueError("expected a call like fn(1, 2)")
        f = tree.body.func
        if isinstance(f, ast.Name):
            modstem, fname = None, f.id
        elif isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name):
            modstem, fname = f.value.id, f.attr
        else:
            raise ValueError("callee must be a name or file.name")
        args = []
        for a in tree.body.args:
            v = ast.literal_eval(a)
            if not isinstance(v, int) or isinstance(v, bool):
                raise ValueError("arguments must be integers (runner limitation)")
            args.append(v)
        if tree.body.keywords:
            raise ValueError("keyword arguments are not supported")
        return modstem, fname, args

    def _runner(self, json_path, fname, args, fuel=None):
        rel = json_path.relative_to(REPO_ROOT).as_posix()
        if RUNNER_BIN.exists():
            cmd = [str(RUNNER_BIN)]
        else:  # builds on first use
            cmd = ["lake", "exe", "leanmodels-run"]
        cmd += [rel, fname] + [str(a) for a in args]
        if fuel is not None:
            cmd += ["--fuel", str(fuel)]
        t0 = time.monotonic()
        try:
            proc = subprocess.run(cmd, cwd=str(REPO_ROOT), capture_output=True,
                                  text=True, timeout=RUNNER_TIMEOUT)
        except subprocess.TimeoutExpired:
            raise _usage_error("leanmodels-run timed out after %ds (wall "
                               "clock, not fuel) on %s" % (RUNNER_TIMEOUT, fname)
                               ) from None
        dt = time.monotonic() - t0
        if proc.returncode != 0:
            _show(_banner(_SEV_COLOR["error"], "leanmodels-run failed"),
                  _block(_SEV_COLOR["error"], None,
                         (proc.stderr or proc.stdout).strip()))
            raise UsageDisplayed("runner exited %d" % proc.returncode)
        lines = [ln for ln in proc.stdout.splitlines() if ln.strip()]
        return json.loads(lines[-1]), dt

    # -- %pydiff -----------------------------------------------------------

    @line_magic
    def pydiff(self, line):
        """%pydiff <fn> <args...> — CPython vs the Lean interpreter, side by
        side (also accepts %pydiff file.fn <args...>)."""
        toks = shlex.split(line)
        if not toks:
            _show(_banner(_SEV_COLOR["error"], "usage: %pydiff <fn> <args...>"))
            raise UsageDisplayed("empty %pydiff")
        fspec = toks[0]
        modstem, fname = (fspec.split(".", 1) if "." in fspec
                          else (None, fspec))
        try:
            args = [int(t) for t in toks[1:]]
        except ValueError:
            _show(_banner(_SEV_COLOR["error"],
                          "usage: %pydiff <fn> <int args...>"))
            raise UsageDisplayed("non-integer %pydiff args") from None
        stem, json_path = self._find_function(fname, modstem)
        py_path = WORK_DIR / (stem + ".py")

        python3 = shutil.which("python3") or sys.executable
        t0 = time.monotonic()
        try:
            proc = subprocess.run(
                [python3, "-c", _CPY_DRIVER, str(py_path), fname]
                + [str(a) for a in args],
                capture_output=True, text=True, timeout=CPYTHON_TIMEOUT,
            )
            cpy = (json.loads(proc.stdout.splitlines()[-1])
                   if proc.returncode == 0 and proc.stdout.strip()
                   else {"status": "harness-error",
                         "msg": (proc.stderr or "no output").strip()[-500:]})
        except subprocess.TimeoutExpired:
            cpy = {"status": "timeout"}
        cpy_dt = time.monotonic() - t0
        lean, lean_dt = self._runner(json_path, fname, args)
        self.timings.append(("pydiff", fname, cpy_dt + lean_dt))

        match = cpy == lean
        call = "%s(%s)" % (fname, ", ".join(str(a) for a in args))
        verdict = ("MATCH" if match else "MISMATCH")
        color = _SEV_COLOR["ok"] if match else _SEV_COLOR["error"]
        table = (
            '<table style="font-family:monospace;font-size:13px;'
            'border-collapse:collapse;margin:4px 0">'
            "<tr><th style='text-align:left;padding:2px 14px 2px 0'></th>"
            "<th style='text-align:left;padding:2px 14px 2px 0'>outcome</th>"
            "<th style='text-align:left;padding:2px 0'>canonical form</th></tr>"
            "<tr><td style='padding:2px 14px 2px 0'>CPython&nbsp;(%s)</td>"
            "<td style='padding:2px 14px 2px 0'>%s</td>"
            "<td style='color:#888;padding:2px 0'>%s</td></tr>"
            "<tr><td style='padding:2px 14px 2px 0'>Lean&nbsp;interpreter</td>"
            "<td style='padding:2px 14px 2px 0'>%s</td>"
            "<td style='color:#888;padding:2px 0'>%s</td></tr></table>"
            % (_esc(stem + ".py"), _esc(_pretty_res(cpy)),
               _esc(json.dumps(cpy)), _esc(_pretty_res(lean)),
               _esc(json.dumps(lean)))
        )
        _show(
            _banner(color, "%s — %s" % (call, verdict),
                    "CPython %.2fs, Lean runner %.2fs" % (cpy_dt, lean_dt)),
            '<div style="border-left:3px solid %s;padding-left:10px">%s</div>'
            % (color, table),
        )
        if cpy.get("status") == "harness-error":
            raise UsageDisplayed("CPython side failed: %s" % cpy.get("msg"))
        if not match:
            raise DiffMismatchError(
                "%s: CPython and the Lean interpreter disagree — see the "
                "table above (tag the cell 'expected-error' if the mismatch "
                "is the lesson)" % call) from None
        return None


class UsageDisplayed(Exception):
    """Raised after a self-explanatory error was already displayed."""


def _pretty_value(v):
    t = v.get("t")
    if t == "none":
        return "None"
    if t == "bool":
        return "True" if v["v"] else "False"
    if t == "int":
        return v["v"]
    if t == "str":
        return repr(v["v"])
    if t in ("list", "tuple"):
        inner = ", ".join(_pretty_value(x) for x in v["v"])
        return ("(%s%s)" % (inner, "," if len(v["v"]) == 1 else "")
                if t == "tuple" else "[%s]" % inner)
    return json.dumps(v)


def _pretty_res(res):
    status = res.get("status")
    if status == "ok":
        return _pretty_value(res["value"])
    if status == "exn":
        return "raises %s" % res["exn"]
    if status == "timeout":
        return "timeout (out of fuel)"
    if status == "unsupported":
        return "unsupported: %s" % res.get("msg", "")
    if status == "unmappable":
        return "ok, outside the canonical value set (%s)" % res.get("msg", "")
    return "%s: %s" % (status, res.get("msg", ""))


def load_ipython_extension(ipython):
    magics = LeanMagics(ipython)
    ipython.register_magics(magics)
    runner = ("binary" if RUNNER_BIN.exists()
              else "lake exe (will build on first %pyrun)")
    _show(
        _banner(_SEV_COLOR["info"], "lean_magic loaded"),
        _block(
            _SEV_COLOR["info"], None,
            "repo root : %s\nwork dir  : %s (scratch, gitignored)\n"
            "runner    : %s\nmagics    : %%%%pyfile  %%%%lean  %%pyrun  %%pydiff"
            % (REPO_ROOT, WORK_DIR.relative_to(REPO_ROOT), runner),
        ),
    )
