#!/usr/bin/env python3
"""rename_to_proglib.py -- rename the Lean library `LeanModels` to `Proglib` (step 2 of the
lean-surfaces -> proglib rename), as a pure, reproducible function of a tree.

Run from anywhere; Python >= 3.9, standard library only, no network, no Lean.

    python3 tools/rename_to_proglib.py apply [-C DIR] [--dry-run] [--json FILE]
    python3 tools/rename_to_proglib.py --check [-C DIR | --rev REV] [--limit N]
    python3 tools/rename_to_proglib.py --regenerate [-C DIR] [--write]
    python3 tools/rename_to_proglib.py --tree REV [-C DIR]
    python3 tools/rename_to_proglib.py --transplant --old-base OLD --new-base NEW [--merge] BRANCH [--to REF]
    python3 tools/rename_to_proglib.py --self-test
    python3 tools/rename_to_proglib.py --version

Every mode prints `rename_to_proglib v<N> <sha256 of this script and its allowlist>` first;
the rename commit quotes that line, and --transplant refuses to run under a different one.
Exit 0 success, 1 a residue or a difference, 2 a refusal.  Every git child runs with
GIT_NO_LAZY_FETCH=1: in a partial clone a missing blob is a loud refusal, never a fetch.

WHAT IT COMPUTES.  S, a function from a tree (paths, modes, bytes) to a tree.  Nothing else
enters it: no clock, locale, environment, network or history.  The rename commit is exactly
S(tree(base)) and contains nothing else, so anyone can recompute it and compare tree ids
(`--tree REV` prints the id of S(tree(REV)) without touching a working tree).  A branch crosses
the rename by having each of its trees rewritten by S (`--transplant`), never by merging or
rebasing across the rename commit: no diff is applied, so no conflict and no rename detection.
--transplant refuses unless NEW's parent chain contains OLD, tree(NEW) = S(tree(OLD)), NEW's
message quotes this script's version line (when it quotes one), BRANCH contains OLD and does
not contain NEW; it warns about files the branch never changed whose renamed version still
differs from NEW's (a hash pin the branch left stale).

THE RULE: a file is LIVING or KEPT, decided per FILE by its path, never per line.
  * A LIVING file follows the rename completely: every spelling of the old name in every
    region (code, strings, name literals, comments, docstrings, captured #guard_msgs text).
  * A KEPT file keeps every byte: records (history), the HDL sources whose bytes oracle results
    pin, svGolf (it moves later, with its pin), generated snapshots only their generator may
    change, and this tool.  KEPT paths are the `path` entries of rename_to_proglib.allow, which
    is read from next to this script, never from the target tree.
  The only old strings left inside living files are the allowlist's `token` and `line` entries
  and saved notebook outputs; each entry carries its reason.

THE MAP.  One constant, LIB; the others derive from it.  Plain substring replacement on bytes,
longest spelling first, in ONE pass (a new spelling is never the input of a rule, so S(S(t)) =
S(t)).  No word boundaries: `\\nLeanModels/...` inside a shell printf is an occurrence too.
    <guillemets>lean-models<guillemets> -> PKG    the root package as lake-manifest.json writes it
    leanmodels-                         -> PKG-   the runner leanmodels-run, temp-dir prefixes
    lean-models                         -> PKG    the Lake package
    lean_models                         -> PKG    the project name in prose
    LeanModels                          -> LIB    module root, namespace, directory, lean_lib
Tracked paths follow the same map (LeanModels/ -> Proglib/, LeanModels.lean -> Proglib.lean).

FILE CLASSES (first match wins; the class decides which rules run):
    SELF      this script, its allowlist and its test                    untouched
    KEEP      an allowlist `path` entry                                   untouched except F2, F5
    GITLINK, SYMLINK                                                       refused if they need renaming
    BINARY    a NUL byte, or not UTF-8                                    untouched (a hit is a residue;
              hits inside the compressed streams of a PDF count, so a byte scan cannot miss them)
    NOTEBOOK  *.ipynb: the map on cell `source` strings only; outputs are saved results and stay;
              written back as json.dumps(nb, indent=1, ensure_ascii=False) + "\\n" (refused if
              the unmodified notebook does not round-trip that way)
    LAKE      lakefile.toml, lake-manifest.json (root)                     the map
    LEAN      *.lean                                                      the map
    DATA      *.json                                                      the map, on bytes (never re-serialized)
    CODE      *.py *.sh *.go *.yml *.yaml *.toml *.baseline *.mjs *.js, executable files   the map
    DOCS      *.md *.tex *.txt, other non-executable extensionless files   the map, F3 on *.md
    OTHER     any other text file (reported as UNCLASSIFIED when edited)   the map
  The map runs on bytes, so line endings, BOMs, final newlines, invalid UTF-8 and file modes are
  preserved exactly.  `token` literals are masked before the map and restored after; lines that
  match a `line` entry are left as they are.

FIXUPS (exact text, idempotent: each matches the OLD text only).
  F1 README.md: the note "The Lean library is still imported as `LeanModels`; a later, announced
     commit renames it to `Proglib`." becomes "The Lean library, formerly `LeanModels`, is now
     `Proglib` ...", kept by a `line` entry.
  F2 CHANGELOG.md (a record): one bullet is inserted above the step-1 bullet, if absent.
  F3 *.md alignment, in code blocks only (fenced blocks, and indented blocks outside lists): on a
     line, the shrink accumulated by replacements is added to the next run of two or more spaces,
     then reset, so columns of trailing comments and diagrams stay where they were.  Prose is never
     re-padded, and neither are blocks that docs_check compares with the tree (path-marked): they
     must stay verbatim.
  F4 pin transport: a 64-hex or 40-hex token in a LAKE/LEAN/CODE/DATA/OTHER file that equals the
     sha256 or the git blob id of the PRE-rename bytes of a tracked file is replaced by the hash of
     that file's POST-rename bytes.  A token that matches no file stays (a stale pin stays stale).
     Pins in prose (DOCS), records and notebooks are records of a measurement and are never
     edited; they are listed.  Holders are processed after the files they pin; a cycle refuses.
  F5 (only with the allowlist line `class record-marker-paths`, which the committed allowlist does
     NOT carry: records keep every byte) in KEPT docs that tools/docs_check.py reads, the path
     token of a docs_check marker line that names a renamed path is renamed; nothing else.
  F6 *.lean: the step-1 leftover "`lean-surfaces` is a" (the project name, in two docstrings that
     describe the project in the present tense) becomes "`proglib` is a".

The design and its reasons: the rename plan of 2026-11-10 (sections 1-3), summarised in the
allowlist's comments.  Delete this script, its allowlist and its test once every live branch has
crossed.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import zlib

VERSION = 2
LIB = "Proglib"            # THE casing constant: module root, namespace, directory, root file, lean_lib
PKG = LIB.lower()          # Lake package, project name in prose, executable and temp-dir prefix
EXE = PKG + "-run"         # the runner
RENAME_DATE = "2026-11-12"  # set when this script lands on master; used by fixup F2 only

OLD_LIB = "LeanModels"
OLD_PKG = "lean-models"

HERE = os.path.dirname(os.path.abspath(__file__))
ALLOW_PATH = os.path.join(HERE, "rename_to_proglib.allow")
SELF_PATHS = ("tools/rename_to_proglib.py", "tools/rename_to_proglib.allow",
              "tools/test_rename_to_proglib.py")

RULES = (
    (("«" + OLD_PKG + "»").encode("utf-8"), PKG.encode("ascii")),
    (b"leanmodels-", (PKG + "-").encode("ascii")),
    (OLD_PKG.encode("ascii"), PKG.encode("ascii")),
    (b"lean_models", PKG.encode("ascii")),
    (OLD_LIB.encode("ascii"), LIB.encode("ascii")),
)
RULE_MAP = dict(RULES)
_ALT = b"|".join(re.escape(o) for o, _ in RULES)
TOKEN_RE = re.compile(_ALT)
ALIGN_RE = re.compile(_ALT + rb"| {2,}(?=\S)")
CHECK_RE = re.compile(rb"lean[-_]?models", re.IGNORECASE)
HEX_RE = re.compile(rb"(?<![0-9A-Fa-f])(?:[0-9a-f]{64}|[0-9a-f]{40})(?![0-9A-Fa-f])")
GENERATED_RE = re.compile(rb"AUTOGENERATED|GENERATED by|Generated by|DO NOT EDIT|do not edit by hand")
PDF_STREAM_RE = re.compile(rb"stream\r?\n(.*?)endstream", re.S)
VERSION_LINE_RE = re.compile(r"^rename_to_proglib v\d+ [0-9a-f]{64}$", re.M)
IDENT = frozenset(b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_")

CODE_EXTS = (".py", ".sh", ".go", ".yml", ".yaml", ".toml", ".baseline", ".mjs", ".js")
DOC_EXTS = (".md", ".tex", ".txt")
PIN_CLASSES = ("LAKE", "LEAN", "CODE", "DATA", "OTHER")
TEXT_CLASSES = ("LAKE", "LEAN", "CODE", "DATA", "DOCS", "OTHER")
NULL_OID = "0" * 40

F1_OLD = (b"The Lean library is still imported as `LeanModels`; a later, announced commit\n"
          b"renames it to `Proglib`.*")
F1_NEW = ("The Lean library, formerly `LeanModels`, is now `%s` (`import %s`);\n"
          "records dated before the rename keep the old names.*" % (LIB, LIB)).encode("utf-8")
F2_ANCHOR = b"- Renamed the repository from `lean-surfaces` to `proglib`"
F2_MARK = b"- Renamed the Lean library from `LeanModels` to `"
F2_TEXT = ("- Renamed the Lean library from `LeanModels` to `%s` (%s): the\n"
           "  directory `LeanModels/` is now `%s/`, the root file `LeanModels.lean` is\n"
           "  `%s.lean`, the Lake package `lean-models` is `%s` and the runner\n"
           "  `leanmodels-run` is `%s`. Records dated before the rename keep the\n"
           "  old names; branches cross with `tools/rename_to_proglib.py --transplant`.\n\n"
           % (LIB, RENAME_DATE, LIB, LIB, PKG, EXE)).encode("utf-8")
F6_OLD = b"`lean-surfaces` is a"
F6_NEW = ("`%s` is a" % PKG).encode("ascii")


class Refusal(Exception):
    """A tree S refuses to rename (exit 2)."""


# --------------------------------------------------------------------------------------------
# small helpers
# --------------------------------------------------------------------------------------------

def rename_bytes(data, counts=None):
    def sub(m):
        old = m.group(0)
        if counts is not None:
            key = old.decode("utf-8")
            counts[key] = counts.get(key, 0) + 1
        return RULE_MAP[old]
    return TOKEN_RE.sub(sub, data)


def rename_str(s):
    return rename_bytes(s.encode("utf-8", "surrogateescape")).decode("utf-8", "surrogateescape")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def blob_id(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def is_binary(data):
    if b"\0" in data:
        return True
    try:
        data.decode("utf-8")
    except UnicodeDecodeError:
        return True
    return False


def hidden_hits(data):
    """Old spellings inside the Flate-compressed streams of a PDF, which no byte scan sees."""
    if not data.startswith(b"%PDF"):
        return 0
    n = 0
    for m in PDF_STREAM_RE.finditer(data):
        try:
            n += len(CHECK_RE.findall(zlib.decompressobj().decompress(m.group(1))))
        except zlib.error:
            pass
    return n


def all_hits(data):
    return len(CHECK_RE.findall(data)) + hidden_hits(data)


def bump(d, key, n=1):
    d[key] = d.get(key, 0) + n


def glob_to_re(glob):
    """`**/` = any number of directories, `**` = anything, `*` and `?` stay inside one segment."""
    out, i = [], 0
    while i < len(glob):
        if glob.startswith("**/", i):
            out.append("(?:.*/)?")
            i += 3
            continue
        if glob.startswith("**", i):
            out.append(".*")
            i += 2
            continue
        c = glob[i]
        if c == "*":
            out.append("[^/]*")
        elif c == "?":
            out.append("[^/]")
        elif c == "[":
            j = glob.find("]", i + 1)
            if j < 0:
                out.append(re.escape(c))
            else:
                out.append("[" + glob[i + 1:j] + "]")
                i = j + 1
                continue
        else:
            out.append(re.escape(c))
        i += 1
    return re.compile("^" + "".join(out) + "$")


def git(args, cwd, data=None, env=None):
    p = subprocess.run(["git"] + list(args), cwd=cwd, input=data, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, env=env)
    if p.returncode != 0:
        raise Refusal("git %s failed: %s" % (" ".join(args), p.stderr.decode("utf-8", "replace").strip()))
    return p.stdout


def version_line(allow_path=ALLOW_PATH):
    h = hashlib.sha256()
    with open(os.path.abspath(__file__), "rb") as fh:
        h.update(fh.read())
    h.update(b"\0")
    with open(allow_path, "rb") as fh:
        h.update(fh.read())
    return "rename_to_proglib v%d %s" % (VERSION, h.hexdigest())


# --------------------------------------------------------------------------------------------
# the allowlist
# --------------------------------------------------------------------------------------------

class Entry(object):
    def __init__(self, kind, glob, arg, reason, lineno):
        self.kind, self.glob, self.arg, self.reason, self.lineno = kind, glob, arg, reason, lineno
        self.key = "%s %s%s" % (kind, glob, (" " + arg) if arg else "")
        self.rx = glob_to_re(rename_str(glob)) if kind in ("path", "token", "line") else None
        self.literal = arg.encode("utf-8") if kind == "token" else None
        self.line_rx = re.compile(arg) if kind == "line" else None

    def matches(self, path):
        # globs are written in old names; both sides go through the map, so one entry covers a
        # file before and after the move
        return bool(self.rx.match(rename_str(path)))


class Rules(object):
    CLASSES = ("notebook-outputs", "record-marker-paths")

    def __init__(self, text, origin="<rules>"):
        self.entries = []
        for n, raw in enumerate(text.splitlines(), 1):
            line = raw.rstrip()
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            fields = line.split("\t")
            if len(fields) < 2 or not fields[-1].startswith("# ") or not fields[-1][2:].strip():
                raise Refusal("%s:%d: an entry is <kind>TAB<field>...TAB# <reason>" % (origin, n))
            reason = fields[-1][2:].strip()
            body = [f for f in fields[:-1] if f != ""]
            kind = body[0]
            if kind == "path" and len(body) == 2:
                self.entries.append(Entry("path", body[1], None, reason, n))
            elif kind in ("token", "line") and len(body) == 3:
                self.entries.append(Entry(kind, body[1], body[2], reason, n))
            elif kind == "class" and len(body) == 2 and body[1] in self.CLASSES:
                self.entries.append(Entry("class", body[1], None, reason, n))
            else:
                raise Refusal("%s:%d: unknown or malformed entry %r" % (origin, n, line))

    @classmethod
    def load(cls, path=ALLOW_PATH):
        with open(path, "r", encoding="utf-8") as fh:
            return cls(fh.read(), path)

    def path_entry(self, path):
        for e in self.entries:
            if e.kind == "path" and e.matches(path):
                return e
        return None

    def of_kind(self, kind, path):
        return [e for e in self.entries if e.kind == kind and e.matches(path)]

    def has_class(self, name):
        return any(e.kind == "class" and e.glob == name for e in self.entries)


# --------------------------------------------------------------------------------------------
# reading trees: {path: (mode, data)}; data is the blob (a symlink's target; a gitlink's oid)
# --------------------------------------------------------------------------------------------

def read_worktree(root):
    items = {}
    for rec in git(["ls-files", "-s", "-z"], root).split(b"\0"):
        if not rec:
            continue
        meta, path = rec.split(b"\t", 1)
        mode, oid, stage = meta.decode("ascii").split()
        if stage != "0":
            raise Refusal("unmerged path %s" % path.decode("utf-8", "replace"))
        p = path.decode("utf-8", "surrogateescape")
        full = os.path.join(root, p)
        if mode == "160000":
            data = oid.encode("ascii")
        elif mode == "120000":
            data = os.readlink(full).encode("utf-8", "surrogateescape")
        else:
            with open(full, "rb") as fh:
                data = fh.read()
        items[p] = (mode, data)
    return items


class Repo(object):
    """Object-level access to a repository: read trees, write blobs and trees, never a worktree."""

    def __init__(self, root):
        self.root = root
        self._cat = None
        self._blobs = {}

    def close(self):
        if self._cat is not None:
            self._cat.stdin.close()
            self._cat.wait()
            self._cat = None

    def rev(self, rev, kind="commit"):
        return git(["rev-parse", "--verify", "%s^{%s}" % (rev, kind)], self.root).decode().strip()

    def blob(self, oid):
        if oid in self._blobs:
            return self._blobs[oid]
        if self._cat is None:
            self._cat = subprocess.Popen(["git", "cat-file", "--batch"], cwd=self.root,
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self._cat.stdin.write(oid.encode("ascii") + b"\n")
        self._cat.stdin.flush()
        header = self._cat.stdout.readline().split()
        if len(header) != 3:
            raise Refusal("cannot read object %s (in a partial clone, fetch the blobs of the commits "
                          "first; this script never fetches)" % oid)
        size = int(header[2])
        data = self._cat.stdout.read(size)
        self._cat.stdout.read(1)
        self._blobs[oid] = data
        return data

    def ls_tree(self, rev):
        """{path: (mode, oid)} of REV's tree, without reading any blob."""
        out = {}
        for rec in git(["ls-tree", "-r", "-z", "--full-tree", self.rev(rev, "tree")], self.root).split(b"\0"):
            if not rec:
                continue
            meta, path = rec.split(b"\t", 1)
            mode, typ, oid = meta.decode("ascii").split()
            out[path.decode("utf-8", "surrogateescape")] = (mode, oid)
        return out

    def read_tree(self, rev, oids=None):
        """{path: (mode, data)}; fills OIDS (a dict) with {path: blob id} when given."""
        items = {}
        for p, (mode, oid) in self.ls_tree(rev).items():
            items[p] = (mode, oid.encode("ascii") if mode == "160000" else self.blob(oid))
            if oids is not None:
                oids[p] = oid
        return items

    def write_tree(self, items):
        """The tree id of {path: (mode, data)}; writes the blobs it needs into the object store."""
        oids = {}
        need = []
        for p, (mode, data) in items.items():
            if mode == "160000":
                oids[p] = data.decode("ascii")
            else:
                oids[p] = blob_id(data)
                need.append(p)
        present = set()
        if need:
            out = git(["cat-file", "--batch-check"], self.root,
                      data=b"".join(oids[p].encode() + b"\n" for p in need))
            for line in out.splitlines():
                f = line.split()
                if len(f) == 3:
                    present.add(f[0].decode())
        missing = sorted(set(p for p in need if oids[p] not in present), key=lambda p: oids[p])
        tmp = tempfile.mkdtemp(prefix="rename-to-proglib-")
        try:
            if missing:
                files, seen = [], set()
                for i, p in enumerate(missing):
                    if oids[p] in seen:
                        continue
                    seen.add(oids[p])
                    f = os.path.join(tmp, "b%d" % i)
                    with open(f, "wb") as fh:
                        fh.write(items[p][1])
                    files.append(f)
                written = git(["hash-object", "-w", "--no-filters", "--stdin-paths"], self.root,
                              data="".join(f + "\n" for f in files).encode()).split()
                if len(written) != len(files):
                    raise Refusal("hash-object wrote %d of %d blobs" % (len(written), len(files)))
            env = dict(os.environ, GIT_INDEX_FILE=os.path.join(tmp, "index"))
            git(["read-tree", "--empty"], self.root, env=env)
            info = b"".join(("%s %s\t" % (items[p][0], oids[p])).encode() + p.encode("utf-8", "surrogateescape")
                            + b"\0" for p in sorted(items))
            git(["update-index", "-z", "--index-info"], self.root, data=info, env=env)
            return git(["write-tree"], self.root, env=env).decode().strip()
        finally:
            shutil.rmtree(tmp, ignore_errors=True)


# --------------------------------------------------------------------------------------------
# markdown: the fenced blocks docs_check reads (mirrors tools/docs_check.py parse_blocks/classify)
# --------------------------------------------------------------------------------------------

HTML_MARKER_RE = re.compile(r"<!--\s*docs-check:\s*(\S+)\s*-->")
MARKER_EXTS = (".py", ".lean", ".json", ".md", ".sv", ".toml")


def fenced_blocks(lines):
    """[(fence_index, close_index, marker)], marker = None | ("html", i, path) | ("first", i, path).
    Indices are 0-based into `lines` (str, no line ends)."""
    blocks, i, n = [], 0, len(lines)
    while i < n:
        raw = lines[i]
        if raw.strip().startswith("```"):
            indent = raw[:len(raw) - len(raw.lstrip())]
            j = i + 1
            while j < n and lines[j].strip() != "```":
                j += 1
            marker = None
            prev = lines[i - 1] if i > 0 else ""
            m = HTML_MARKER_RE.search(prev)
            if m:
                marker = ("html", i - 1, m.group(1))
            elif i + 1 < j:
                first = lines[i + 1]
                if indent and first.startswith(indent):
                    first = first[len(indent):]
                first = first.strip()
                rest = None
                for leader in ("-- ", "# "):
                    if first.startswith(leader):
                        rest = first[len(leader):].strip()
                        break
                if rest is not None and not rest.startswith("(illustrative") and rest.split():
                    token = rest.split()[0]
                    if ("/" in token or token.endswith(MARKER_EXTS)) and "illustrative" not in rest[len(token):]:
                        marker = ("first", i + 1, token)
            blocks.append((i, j, marker))
            i = j + 1
        else:
            i += 1
    return blocks


LIST_ITEM_RE = re.compile(r"^\s*(?:[-*+]|\d+[.)])\s")


def indented_code_lines(lines):
    """0-based indices of lines in indented code blocks: chunks of lines indented by four or more
    spaces (or a tab) that open after a blank line, outside lists (the nearest non-blank line above
    the chunk starts at column 0 and is not a list item), and outside fenced blocks."""
    fenced = set()
    for (i, j, _) in fenced_blocks(lines):
        fenced.update(range(i, j + 1))
    out, i, n = set(), 0, len(lines)
    while i < n:
        indented = (lines[i].startswith("    ") or lines[i].startswith("\t")) and lines[i].strip()
        if not indented or i in fenced or i == 0 or lines[i - 1].strip():
            i += 1
            continue
        k = i - 1
        while k >= 0 and not lines[k].strip():
            k -= 1
        above = lines[k] if k >= 0 else ""
        if k < 0 or above[:1] in (" ", "\t") or LIST_ITEM_RE.match(above):
            i += 1
            continue
        j = i
        while j < n and j not in fenced and (lines[j].startswith("    ") or lines[j].startswith("\t")
                                               or not lines[j].strip()):
            if lines[j].strip():
                out.add(j)
            j += 1
        i = j
    return out


def in_docs_corpus(path):
    return path in ("README.md", "AGENTS.md") or (path.startswith("docs/") and path.endswith(".md"))


# --------------------------------------------------------------------------------------------
# the report
# --------------------------------------------------------------------------------------------

class Report(object):
    def __init__(self):
        self.files = {}          # class -> {"files": n, "edited": n}
        self.replaced = {}       # spelling -> n
        self.replaced_by_class = {}
        self.moved = []
        self.fixups = []         # (id, path, line, note)
        self.kept = {}           # entry key -> occurrences left in place
        self.residue_hint = []   # (path, note): old spellings apply cannot rename (binary, metadata)
        self.generated = []
        self.unclassified = []
        self.suspicious = []
        self.aligned = []
        self.pins_transported = []
        self.pins_unmatched = []
        self.pins_not_scanned = []
        self.collapsed = []
        self.hit_files = 0
        self.hits = 0
        self.added_by_fixups = 0

    def as_json(self):
        return {k: v for k, v in sorted(self.__dict__.items())}

    def print(self, out=sys.stdout, full=False):
        w = out.write
        w("files with an old spelling: %d; occurrences: %d; replaced: %d; kept: %d; added by fixup F2: "
          "%d\n" % (self.hit_files, self.hits, sum(self.replaced.values()), sum(self.kept.values()),
                    self.added_by_fixups))
        w("by class (files / edited / occurrences replaced):\n")
        for c in sorted(self.files):
            w("  %-9s %5d %5d %6d\n" % (c, self.files[c]["files"], self.files[c]["edited"],
                                        sum(self.replaced_by_class.get(c, {}).values())))
        w("replaced by spelling: %s\n" % ", ".join("%s %d" % (k, self.replaced[k]) for k in sorted(self.replaced)))
        w("paths moved: %d\n" % len(self.moved))
        w("fixups: %d\n" % len(self.fixups))
        for f in self.fixups:
            w("  %s %s:%s %s\n" % f)
        w("F3 lines re-padded: %d\n" % len(self.aligned))
        for a in self.aligned:
            w("  %s\n" % a)
        w("pins transported: %d\n" % len(self.pins_transported))
        for p in self.pins_transported:
            w("  %s:%d %s %s %s -> %s\n" % tuple(p))
        w("other hex tokens in those holders, matching no tracked file (stale or external; left): %d\n"
          % len(self.pins_unmatched))
        for p in self.pins_unmatched:
            w("  %s:%d %s\n" % tuple(p))
        w("pins in prose or records of a changed file (never edited): %d\n" % len(self.pins_not_scanned))
        for p in self.pins_not_scanned:
            w("  %s:%d %s pins %s\n" % tuple(p))
        w("kept by allowlist entry (occurrences):\n")
        for k in sorted(self.kept):
            w("  %6d  %s\n" % (self.kept[k], k))
        w("generated files edited by the map (regenerate or show equal): %d\n" % len(self.generated))
        for g in self.generated:
            w("  %s\n" % g)
        w("UNCLASSIFIED files edited: %d\n" % len(self.unclassified))
        for u in self.unclassified:
            w("  %s\n" % u)
        w("old spellings the map cannot reach (residues for --check): %d\n" % len(self.residue_hint))
        for r in self.residue_hint:
            w("  %s: %s\n" % r)
        w("suspicious (glued to identifier characters on both sides): %d\n" % len(self.suspicious))
        for s in self.suspicious:
            w("  %s\n" % s)
        if self.collapsed:
            w("identical old/new path pairs collapsed: %d\n" % len(self.collapsed))
            for c in self.collapsed:
                w("  %s\n" % c)
        if full:
            for m in self.moved:
                w("  moved %s -> %s\n" % tuple(m))


# --------------------------------------------------------------------------------------------
# S
# --------------------------------------------------------------------------------------------

def classify(path, mode, data, rules):
    if path in SELF_PATHS:
        return "SELF", None
    e = rules.path_entry(path)
    if e is not None:
        return "KEEP", e
    if mode == "160000":
        return "GITLINK", None
    if mode == "120000":
        return "SYMLINK", None
    if is_binary(data):
        return "BINARY", None
    if path.endswith(".ipynb"):
        return "NOTEBOOK", None
    if path in ("lakefile.toml", "lake-manifest.json"):
        return "LAKE", None
    base = path.rsplit("/", 1)[-1]
    ext = os.path.splitext(base)[1]
    if ext == ".lean":
        return "LEAN", None
    if ext == ".json":
        return "DATA", None
    if ext in CODE_EXTS or mode == "100755":
        return "CODE", None
    if ext in DOC_EXTS or ext == "":
        return "DOCS", None
    return "OTHER", None


def align_sub(line, counts):
    """F3 on one line: the map, with the accumulated shrink added to the next space run."""
    state = {"d": 0, "wide": False}

    def sub(m):
        s = m.group(0)
        if s[:1] == b" ":
            d, state["d"] = state["d"], 0
            if d > 0:
                state["wide"] = True
                return s + b" " * d
            if d < 0:
                state["wide"] = True
                return s[:max(2, len(s) + d)]
            return s
        new = RULE_MAP[s]
        bump(counts, s.decode("utf-8"))
        state["d"] += len(s.decode("utf-8")) - len(new.decode("utf-8"))
        return new
    return ALIGN_RE.sub(sub, line), state["wide"]


def rewrite_text(path, cls, data, rules, rep):
    """The map on a living text file, with token masking, line protection and F3 (*.md)."""
    tokens = rules.of_kind("token", path)
    protect = rules.of_kind("line", path)
    counts = {}
    lines = data.splitlines(True)
    align_lines = set()
    if path.endswith(".md"):
        text_lines = [l.decode("utf-8", "surrogateescape").rstrip("\r\n") for l in lines]
        for (i, j, marker) in fenced_blocks(text_lines):
            if marker is None:
                align_lines.update(range(i + 1, j))
        align_lines.update(indented_code_lines(text_lines))
    out = []
    for idx, line in enumerate(lines):
        if not TOKEN_RE.search(line):
            out.append(line)
            continue
        text = line.decode("utf-8", "surrogateescape")
        guard = [e for e in protect if e.line_rx.search(text)]
        if guard:
            bump(rep.kept, guard[0].key, len(CHECK_RE.findall(line)))
            out.append(line)
            continue
        stash = []
        for e in tokens:
            if e.literal in line:
                bump(rep.kept, e.key, line.count(e.literal) * len(CHECK_RE.findall(e.literal)))
                ph = b"\0%d\0" % len(stash)
                stash.append(e.literal)
                line = line.replace(e.literal, ph)
        for m in TOKEN_RE.finditer(line):
            before = line[m.start() - 1] if m.start() > 0 else None
            after = line[m.end()] if m.end() < len(line) else None
            if before in IDENT and after in IDENT:
                rep.suspicious.append("%s:%d" % (path, idx + 1))
        if idx in align_lines:
            new, wide = align_sub(line, counts)
            if wide:
                rep.aligned.append("%s:%d" % (path, idx + 1))
                rep.fixups.append(("F3", path, idx + 1, "re-padded"))
        else:
            new = rename_bytes(line, counts)
        for k, lit in enumerate(stash):
            new = new.replace(b"\0%d\0" % k, lit)
        out.append(new)
    for k, v in counts.items():
        bump(rep.replaced, k, v)
        bump(rep.replaced_by_class.setdefault(cls, {}), k, v)
    return b"".join(out)


def iter_strings(obj):
    if isinstance(obj, str):
        yield obj
    elif isinstance(obj, list):
        for x in obj:
            for s in iter_strings(x):
                yield s
    elif isinstance(obj, dict):
        for k in sorted(obj):
            for s in iter_strings(k):
                yield s
            for s in iter_strings(obj[k]):
                yield s


def nb_dump(nb):
    return (json.dumps(nb, indent=1, ensure_ascii=False) + "\n").encode("utf-8")


def rewrite_notebook(path, data, rules, rep):
    nb = json.loads(data.decode("utf-8"))
    if nb_dump(nb) != data:
        raise Refusal("%s: the notebook does not round-trip through json.dumps(indent=1, "
                      "ensure_ascii=False); refusing to re-serialize it" % path)
    counts = {}
    kept = 0
    for cell in nb.get("cells", []):
        src = cell.get("source")
        if isinstance(src, list):
            cell["source"] = [rename_bytes(s.encode("utf-8"), counts).decode("utf-8") for s in src]
        elif isinstance(src, str):
            cell["source"] = rename_bytes(src.encode("utf-8"), counts).decode("utf-8")
        for s in iter_strings(cell.get("outputs", [])):
            kept += len(CHECK_RE.findall(s.encode("utf-8")))
        rest = {k: v for k, v in cell.items() if k not in ("source", "outputs")}
        for s in iter_strings(rest):
            if CHECK_RE.search(s.encode("utf-8")):
                rep.residue_hint.append((path, "cell metadata holds an old spelling"))
    for s in iter_strings({k: v for k, v in nb.items() if k != "cells"}):
        if CHECK_RE.search(s.encode("utf-8")):
            rep.residue_hint.append((path, "notebook metadata holds an old spelling"))
    if kept:
        bump(rep.kept, "class notebook-outputs", kept)
    for k, v in counts.items():
        bump(rep.replaced, k, v)
        bump(rep.replaced_by_class.setdefault("NOTEBOOK", {}), k, v)
    return nb_dump(nb) if counts else data


def fixup_f1(data, rep):
    if F1_OLD in data:
        line = data[:data.index(F1_OLD)].count(b"\n") + 1
        rep.fixups.append(("F1", "README.md", line, "rename note rewritten"))
        return data.replace(F1_OLD, F1_NEW, 1)
    return data


def fixup_f2(data, rep):
    if F2_MARK in data:
        return data
    at = data.find(b"\n" + F2_ANCHOR)
    if at < 0:
        rep.fixups.append(("F2", "CHANGELOG.md", 0, "anchor bullet absent; nothing inserted"))
        return data
    rep.fixups.append(("F2", "CHANGELOG.md", data[:at + 1].count(b"\n") + 1, "bullet inserted"))
    rep.added_by_fixups += len(CHECK_RE.findall(F2_TEXT))
    return data[:at + 1] + F2_TEXT + data[at + 1:]


def fixup_f5(path, data, rep):
    """In a KEPT doc, rename the path token of docs_check marker lines naming renamed paths."""
    lines = data.splitlines(True)
    text_lines = [l.decode("utf-8", "surrogateescape").rstrip("\r\n") for l in lines]
    changed = False
    for (_, _, marker) in fenced_blocks(text_lines):
        if marker is None:
            continue
        _, i, token = marker
        new_token = rename_str(token)
        if new_token == token:
            continue
        old = token.encode("utf-8", "surrogateescape")
        if old not in lines[i]:
            continue
        lines[i] = lines[i].replace(old, new_token.encode("utf-8", "surrogateescape"), 1)
        rep.fixups.append(("F5", path, i + 1, "marker path %s -> %s" % (token, new_token)))
        counts = {}
        rename_bytes(old, counts)
        for k, v in counts.items():
            bump(rep.replaced, k, v)
            bump(rep.replaced_by_class.setdefault("KEEP", {}), k, v)
        changed = True
    return b"".join(lines) if changed else data


def fixup_f6(path, data, rep):
    rep.fixups.append(("F6", path, data[:data.index(F6_OLD)].count(b"\n") + 1,
                       "step-1 project name in a docstring"))
    return data.replace(F6_OLD, F6_NEW)


def transform(path, cls, entry, data, rules, rep):
    hits = all_hits(data) if cls != "GITLINK" else 0
    if hits:
        rep.hit_files += 1
        rep.hits += hits
    if cls == "SELF":
        if hits:
            bump(rep.kept, "self " + path, hits)
        return data
    if cls == "KEEP":
        new = data
        if path == "CHANGELOG.md":
            new = fixup_f2(new, rep)
        if rules.has_class("record-marker-paths") and in_docs_corpus(path):
            before = len(CHECK_RE.findall(new))
            new = fixup_f5(path, new, rep)
            hits -= before - len(CHECK_RE.findall(new))
        if hits:
            bump(rep.kept, entry.key, hits)
        return new
    if cls in ("GITLINK", "SYMLINK"):
        return data
    if cls == "BINARY":
        if hits:
            rep.residue_hint.append((path, "binary file with %d old spelling(s)" % hits))
        return data
    orig = data
    if cls == "LEAN" and F6_OLD in data:
        data = fixup_f6(path, data, rep)
    if not TOKEN_RE.search(data):
        if hits:
            rep.residue_hint.append((path, "%d spelling(s) outside the map" % hits))
        return data
    if cls == "NOTEBOOK":
        return rewrite_notebook(path, data, rules, rep)
    if path == "README.md":
        data = fixup_f1(data, rep)
    new = rewrite_text(path, cls, data, rules, rep)
    if path == "lakefile.toml":
        before = lake_exes(orig)
        after = lake_exes(new)
        if after != [rename_str(n) for n in before]:
            raise Refusal("lakefile.toml: the [[lean_exe]] order changed")
    if cls == "OTHER" and new != orig:
        rep.unclassified.append(path)
    if new != orig and GENERATED_RE.search(b"".join(orig.splitlines(True)[:5])):
        rep.generated.append(path)
    return new


def lake_exes(data):
    names, in_exe = [], False
    for line in data.decode("utf-8", "replace").splitlines():
        s = line.strip()
        if s.startswith("[["):
            in_exe = s == "[[lean_exe]]"
            continue
        m = re.match(r'name\s*=\s*"([^"]*)"', s)
        if in_exe and m:
            names.append(m.group(1))
            in_exe = False
    return names


class Memo(object):
    """Caches for computing S on many trees of one repository in one run (--transplant).  S is a
    function of (path, mode, bytes) per file plus the pin index, so a file version seen before is
    not transformed, hashed or scanned again.  With a memo the Report is incomplete (--transplant
    discards it); the tree is the same, which --self-test asserts."""

    def __init__(self):
        self.xform = {}    # (path, mode, blob id) -> (class, bytes after the map and fixups)
        self.sha = {}      # blob id -> sha256 of the blob
        self.hexes = {}    # (path, mode, blob id) -> [(offset, hex token)] in the bytes after the map


def hex_tokens(data):
    return [(m.start(), m.group(0).decode()) for m in HEX_RE.finditer(data)]


def transport_pins(items, post, cls_of, rep, memo=None, oids=None):
    """F4.  items: path -> (mode, pre bytes); post: path -> bytes after the map and the fixups."""
    pre_index = {}
    for p, (mode, data) in items.items():
        if mode in ("100644", "100755"):
            if memo is not None:
                b = oids[p]
                s = memo.sha.get(b)
                if s is None:
                    s = memo.sha[b] = sha256(data)
            else:
                s, b = sha256(data), blob_id(data)
            pre_index.setdefault(s, set()).add(p)
            pre_index.setdefault(b, set()).add(p)
    changed = set(p for p in post if post[p] != items[p][1])
    holders = {}
    for p in sorted(post):
        if cls_of[p] not in PIN_CLASSES:
            continue
        if memo is not None:
            key = (p, items[p][0], oids[p])
            toks = memo.hexes.get(key)
            if toks is None:
                toks = memo.hexes[key] = hex_tokens(post[p])
        else:
            toks = hex_tokens(post[p])
        refs = [(pos, tok) for pos, tok in toks if tok in pre_index]
        if refs:
            holders[p] = refs
    # pins in prose, records and notebooks are listed, never edited (report only: skipped with a memo)
    for p in sorted(post) if memo is None else ():
        if cls_of[p] in PIN_CLASSES or items[p][0] not in ("100644", "100755"):
            continue
        for m in HEX_RE.finditer(post[p]):
            tok = m.group(0).decode()
            for t in sorted(pre_index.get(tok, ())):
                if t in changed:
                    rep.pins_not_scanned.append([p, post[p][:m.start()].count(b"\n") + 1, tok[:12], t])
    final = dict(post)
    state = {}

    def visit(p, stack):
        if state.get(p) == "done":
            return
        if state.get(p) == "open":
            raise Refusal("pin cycle: %s" % " -> ".join(stack + [p]))
        state[p] = "open"
        for _, tok in holders.get(p, ()):
            for t in sorted(pre_index[tok]):
                if t != p and t in holders:
                    visit(t, stack + [p])
        state[p] = "done"
        if p not in holders:
            return
        data = final[p]
        pieces, last, moved = [], 0, False
        for pos, tok in holders[p]:
            targets = sorted(pre_index[tok])
            fn = sha256 if len(tok) == 64 else blob_id
            news = set(fn(final[t]) for t in targets)
            if len(news) > 1:
                raise Refusal("%s: pin %s names %d files whose renamed bytes differ: %s"
                              % (p, tok[:12], len(targets), ", ".join(targets)))
            new = news.pop()
            if new != tok:
                pieces.append(data[last:pos])
                pieces.append(new.encode("ascii"))
                last = pos + len(tok)
                moved = True
                rep.pins_transported.append([p, data[:pos].count(b"\n") + 1, "/".join(targets),
                                             "sha256" if len(tok) == 64 else "blob", tok[:12], new[:12]])
        if moved:
            pieces.append(data[last:])
            final[p] = b"".join(pieces)
            for m in HEX_RE.finditer(data):
                if m.group(0).decode() not in pre_index:
                    rep.pins_unmatched.append([p, data[:m.start()].count(b"\n") + 1, m.group(0).decode()[:12]])

    for p in sorted(holders):
        visit(p, [])
    return final


def compute(items, rules, memo=None, oids=None):
    """S.  items: {path: (mode, data)} -> ({path: (mode, data)}, Report).  MEMO (with OIDS, the
    blob id of every path) caches per-file work across trees; the tree it gives is the same."""
    rep = Report()
    post, cls_of, newpath = {}, {}, {}
    for path in sorted(items):
        mode, data = items[path]
        key = (path, mode, oids[path]) if memo is not None else None
        if key is not None and key in memo.xform:
            cls, new = memo.xform[key]
            np = path if cls == "SELF" else rename_str(path)
        else:
            cls, entry = classify(path, mode, data, rules)
            np = path if cls == "SELF" else rename_str(path)
            if cls == "SYMLINK" and (np != path or TOKEN_RE.search(data)):
                raise Refusal("symlink %s (-> %s) needs renaming; resolve it by hand first"
                              % (path, data.decode("utf-8", "replace")))
            if cls == "GITLINK" and np != path:
                raise Refusal("gitlink %s needs renaming; resolve it by hand first" % path)
            new = transform(path, cls, entry, data, rules, rep)
            if key is not None:
                memo.xform[key] = (cls, new)
        cls_of[path] = cls
        c = rep.files.setdefault(cls, {"files": 0, "edited": 0})
        c["files"] += 1
        if new != data:
            c["edited"] += 1
        post[path] = new
        newpath[path] = np
    final = transport_pins(items, post, cls_of, rep, memo, oids)
    out, src = {}, {}
    for path in sorted(items):
        np = newpath[path]
        val = (items[path][0], final[path])
        if np != path:
            rep.moved.append([path, np])
        if np in out:
            if out[np] != val:
                raise Refusal("path collision: %s and %s both become %s, with different content; "
                              "delete one of them (in old names) first" % (src[np], path, np))
            rep.collapsed.append(np)
            continue
        out[np] = val
        src[np] = path
    return out, rep


# --------------------------------------------------------------------------------------------
# apply (working tree), --tree (object level)
# --------------------------------------------------------------------------------------------

def apply_worktree(root, rules, dry_run=False, out=sys.stdout, json_path=None):
    status = git(["status", "--porcelain=v1", "-z", "--untracked-files=all"], root).split(b"\0")
    dirty = [s for s in status if s and not s.startswith(b"??")]
    if dirty:
        raise Refusal("the working tree has %d tracked change(s); commit or stash them first "
                      "(first: %s)" % (len(dirty), dirty[0].decode("utf-8", "replace")))
    items = read_worktree(root)
    new, rep = compute(items, rules)
    removed = sorted(p for p in items if p not in new)
    changed = sorted(p for p in new if items.get(p) != new[p])
    for p in changed:
        if p not in items and os.path.lexists(os.path.join(root, p)):
            raise Refusal("%s is an untracked or ignored file in the way of a renamed path" % p)
    rep.print(out)
    if json_path:
        with open(json_path, "w", encoding="utf-8") as fh:
            json.dump(rep.as_json(), fh, indent=1, sort_keys=True)
            fh.write("\n")
    if dry_run:
        out.write("dry run: %d path(s) would be removed, %d written\n" % (len(removed), len(changed)))
        return rep
    for p in removed:
        os.unlink(os.path.join(root, p))
    for p in removed:
        d = os.path.dirname(os.path.join(root, p))
        while d and os.path.abspath(d) != os.path.abspath(root) and os.path.isdir(d) and not os.listdir(d):
            os.rmdir(d)
            d = os.path.dirname(d)
    oids = {}
    regular = []
    for p in changed:
        mode, data = new[p]
        full = os.path.join(root, p)
        os.makedirs(os.path.dirname(full) or root, exist_ok=True)
        if os.path.lexists(full):
            os.unlink(full)
        if mode == "120000":
            os.symlink(data.decode("utf-8", "surrogateescape"), full)
            oids[p] = git(["hash-object", "-w", "--stdin"], root, data=data).decode().strip()
        elif mode == "160000":
            raise Refusal("gitlink %s cannot be written by apply" % p)
        else:
            with open(full, "wb") as fh:
                fh.write(data)
            os.chmod(full, 0o755 if mode == "100755" else 0o644)
            regular.append(p)
    if regular:
        written = git(["hash-object", "-w", "--no-filters", "--stdin-paths"], root,
                      data="".join(p + "\n" for p in regular).encode("utf-8", "surrogateescape")).split()
        for p, o in zip(regular, written):
            oids[p] = o.decode()
    info = b""
    for p in removed:
        info += ("0 %s\t" % NULL_OID).encode() + p.encode("utf-8", "surrogateescape") + b"\0"
    for p in changed:
        info += ("%s %s\t" % (new[p][0], oids[p])).encode() + p.encode("utf-8", "surrogateescape") + b"\0"
    if info:
        git(["update-index", "-z", "--index-info"], root, data=info)
    subprocess.run(["git", "update-index", "-q", "--refresh"], cwd=root,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    out.write("applied: %d path(s) removed, %d written (all staged)\n" % (len(removed), len(changed)))
    return rep


def s_tree(repo, rev, rules, memo=None):
    oids = {} if memo is not None else None
    new, rep = compute(repo.read_tree(rev, oids), rules, memo, oids)
    return repo.write_tree(new), rep


# --------------------------------------------------------------------------------------------
# --check
# --------------------------------------------------------------------------------------------

IMPORT_RE = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(.+)$")


def run_check(items, rules, out=sys.stdout, limit=200):
    residues, allowed = [], {}
    paths = set(items)
    for p in sorted(items):
        mode, data = items[p]
        keep = p in SELF_PATHS or rules.path_entry(p) is not None
        if CHECK_RE.search(p.encode("utf-8", "surrogateescape")) and not keep:
            residues.append((p, 0, "a tracked path has an old spelling"))
        if mode == "160000":
            continue
        hidden = hidden_hits(data)
        if not hidden and not CHECK_RE.search(data):
            continue
        n = len(CHECK_RE.findall(data)) + hidden
        e = rules.path_entry(p)
        if p in SELF_PATHS and e is None:
            bump(allowed, "self " + p, n)
            continue
        if e is not None:
            bump(allowed, e.key, n)
            continue
        if is_binary(data):
            residues.append((p, 0, "binary file holds %d old spelling(s), %d of them inside compressed "
                             "PDF streams" % (n, hidden)))
            continue
        if p.endswith(".ipynb"):
            check_notebook(p, data, residues, allowed, rules)
            continue
        tokens = rules.of_kind("token", p)
        protect = rules.of_kind("line", p)
        for lineno, line in enumerate(data.splitlines(True), 1):
            if not CHECK_RE.search(line):
                continue
            text = line.decode("utf-8", "surrogateescape")
            guard = [e for e in protect if e.line_rx.search(text)]
            if guard:
                bump(allowed, guard[0].key, len(CHECK_RE.findall(line)))
                continue
            spans = []
            for e in tokens:
                start = line.find(e.literal)
                while start >= 0:
                    spans.append((start, start + len(e.literal), e))
                    start = line.find(e.literal, start + 1)
            bad = False
            for m in CHECK_RE.finditer(line):
                cover = [s for s in spans if s[0] <= m.start() and m.end() <= s[1]]
                if cover:
                    bump(allowed, cover[0][2].key)
                else:
                    bad = True
            if bad:
                residues.append((p, lineno, text.strip()[:200]))
    lower = {}
    for p in sorted(paths):
        lower.setdefault(p.lower(), []).append(p)
    for k in sorted(lower):
        if len(lower[k]) > 1:
            residues.append((lower[k][0], 0, "paths differ only by case: %s" % ", ".join(lower[k])))
    unresolved = checked_imports = 0
    for p in sorted(paths):
        if not p.endswith(".lean") or p in SELF_PATHS or rules.path_entry(p) is not None:
            continue
        for lineno, line in enumerate(items[p][1].decode("utf-8", "replace").splitlines(), 1):
            m = IMPORT_RE.match(line)
            if not m:
                continue
            for mod in m.group(1).split("--")[0].split():
                clean = mod.replace("«", "").replace("»", "")
                if clean == LIB or clean.startswith(LIB + "."):
                    checked_imports += 1
                    target = clean.replace(".", "/") + ".lean"
                    if target not in paths:
                        unresolved += 1
                        residues.append((p, lineno, "import %s names no tracked file (%s)" % (mod, target)))
    if "lakefile.toml" in items:
        exes = lake_exes(items["lakefile.toml"][1])
        if not exes or exes[0] != EXE:
            residues.append(("lakefile.toml", 0, "the first [[lean_exe]] is %r, not %r (tools/triad.sh "
                             "takes the first one as the runner)" % (exes[0] if exes else None, EXE)))
    out.write("allowed occurrences by entry:\n")
    for e in rules.entries:
        if e.kind == "class" and e.glob == "record-marker-paths":
            continue
        out.write("  %6d  %s\n" % (allowed.get(e.key, 0), e.key))
    for k in sorted(k for k in allowed if k.startswith("self ")):
        out.write("  %6d  %s\n" % (allowed[k], k))
    stale = [e.key for e in rules.entries
             if not (e.kind == "class" and e.glob == "record-marker-paths") and not allowed.get(e.key)]
    out.write("entries that allow nothing in this tree (they still keep those files untouched; "
              "stale if the file is gone): %d\n" % len(stale))
    for s in stale:
        out.write("  %s\n" % s)
    out.write("imports of %s modules checked: %d, unresolved: %d\n" % (LIB, checked_imports, unresolved))
    out.write("residues: %d\n" % len(residues))
    for r in residues[:limit]:
        out.write("  %s:%d: %s\n" % r)
    if len(residues) > limit:
        out.write("  ... %d more (raise --limit)\n" % (len(residues) - limit))
    return 1 if residues else 0


def check_notebook(p, data, residues, allowed, rules):
    try:
        nb = json.loads(data.decode("utf-8"))
    except ValueError:
        residues.append((p, 0, "not valid JSON, and it holds an old spelling"))
        return
    for i, cell in enumerate(nb.get("cells", [])):
        for s in iter_strings(cell.get("source", [])):
            if CHECK_RE.search(s.encode("utf-8")):
                residues.append((p, 0, "cells[%d].source: %s" % (i, s.strip()[:160])))
        n = sum(len(CHECK_RE.findall(s.encode("utf-8"))) for s in iter_strings(cell.get("outputs", [])))
        if n:
            if rules.has_class("notebook-outputs"):
                bump(allowed, "class notebook-outputs", n)
            else:
                residues.append((p, 0, "cells[%d].outputs: %d old spelling(s)" % (i, n)))
        rest = {k: v for k, v in cell.items() if k not in ("source", "outputs")}
        for s in iter_strings(rest):
            if CHECK_RE.search(s.encode("utf-8")):
                residues.append((p, 0, "cells[%d] metadata: %s" % (i, s.strip()[:160])))
    for s in iter_strings({k: v for k, v in nb.items() if k != "cells"}):
        if CHECK_RE.search(s.encode("utf-8")):
            residues.append((p, 0, "notebook metadata: %s" % s.strip()[:160]))


# --------------------------------------------------------------------------------------------
# --regenerate: the generators that need no Lean
# --------------------------------------------------------------------------------------------

SV_REFUSALS_SNIPPET = (
    "import os, sys\n"
    "sys.dont_write_bytecode = True\n"
    "root = sys.argv[1]\n"
    "sys.path.insert(0, os.path.join(root, 'tools'))\n"
    "import gen_sv_refusals as g\n"
    "data, want = g.rendered(root)\n"
    "sys.stdout.buffer.write(want[g.OUT_MD].encode('utf-8'))\n")

LEAN_HOST_COMMANDS = """\
On a Lean host (not here), the bar for the rename commit:
  lake exe cache get && lake build              # default targets: %(LIB)s, Examples, %(EXE)s, circuit-dc-runner, c-torture-run
  lake build <each %(LIB)s module that no default target imports>   # 22 at the rehearsal; build them by name
  lake env lean <scratch file that #checks %(LIB)s.Python.Monadic.evalOpenList, %(LIB)s.Python.flattenStarCallArgs,
                 %(LIB)s.Sv.PDesign.instantiateHD2, %(LIB)s.Sv.PDesign.instantiateHDAlias2>   # the single-backtick names
  python3 harness/diff_test.py && tools/leanpy --compare harness/scripts/gen_script.py && python3 tools/docs_check.py
  python3 harness/coverage_page.py --check ; python3 harness/lean_axiom_census.py --gate (as tools/ci.sh runs it)
  lake env lean <each .lean outside the build: extractors/cpp/*.lean, harness/**/*.lean, tools/*.lean, docs/*.lean>
  the tinyxml2 literals: print each of the six by its exporter's own print stage and compare with the tree
  docs/sv-coverage.md rows 708/806: harness/sv_coverage_page.py --check (needs the SV runner and pyslang)
  the shell self-tests (tools/triad.sh, check.sh, check_run2_ratchet.sh, check_sv_chain.sh, sites.sh, laws.sh,
  substrate.sh, editions.sh, diagnose.sh --self-test); optionally `lake update` in a scratch copy (manifest diff: none)
""" % {"LIB": LIB, "EXE": EXE}


def run_regenerate(root, write, out=sys.stdout, python39="python3.9"):
    failures = 0
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")   # leave no __pycache__ in the target tree

    def compare(rel, produced):
        nonlocal failures
        full = os.path.join(root, rel)
        with open(full, "rb") as fh:
            have = fh.read()
        if produced == have:
            out.write("  same       %s\n" % rel)
            return
        if write:
            with open(full, "wb") as fh:
                fh.write(produced)
            out.write("  WROTE      %s\n" % rel)
        else:
            failures += 1
            out.write("  DIFFERS    %s (run --regenerate --write, then review the diff)\n" % rel)

    out.write("generators that need no Lean:\n")
    tmp = tempfile.mkdtemp(prefix="rename-to-proglib-regen-")
    try:
        p = subprocess.run([python39, "extractors/python/extract.py", "--out", tmp, "--companion-dir", tmp,
                            "Examples/python/sum_to/sum_to.py"], cwd=root, env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if p.returncode != 0:
            failures += 1
            out.write("  FAILED     extract.py on sum_to.py: %s\n" % p.stderr.decode("utf-8", "replace").strip())
        else:
            with open(os.path.join(tmp, "SumTo.lean"), "rb") as fh:
                compare("Examples/python/sum_to/SumTo.lean", fh.read())
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    p = subprocess.run([sys.executable, "-I", "-c", SV_REFUSALS_SNIPPET, root], cwd=root, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode != 0:
        failures += 1
        out.write("  FAILED     gen_sv_refusals render: %s\n" % p.stderr.decode("utf-8", "replace").strip()[-400:])
    else:
        compare("docs/sv-refusals.md", p.stdout)
    # envelope_fresh.py leaves one temp directory per envelope behind; give it its own TMPDIR
    scratch = tempfile.mkdtemp(prefix="rename-to-proglib-envfresh-")
    try:
        p = subprocess.run([python39, "harness/envelope_fresh.py", "--tier", "python"], cwd=root,
                           env=dict(env, TMPDIR=scratch), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    last = [l for l in p.stdout.decode("utf-8", "replace").splitlines() if l.startswith("envelope_fresh[")]
    out.write("  %-10s harness/envelope_fresh.py --tier python: %s\n"
              % ("same" if p.returncode == 0 else "DIFFERS", last[-1] if last else "(no summary)"))
    if p.returncode != 0:
        failures += 1
    out.write("reported, not a pass criterion (red before the rename; compare before and after):\n")
    p = subprocess.run([sys.executable, "tools/gen_sv_refusals.py", "--check"], cwd=root, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    errs = [l for l in p.stdout.decode("utf-8", "replace").splitlines() if "ERROR" in l]
    out.write("  tools/gen_sv_refusals.py --check: exit %d, %d ERROR line(s)\n" % (p.returncode, len(errs)))
    p = subprocess.run(["bash", "tools/check_run2_ratchet.sh"], cwd=root, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    tail = [l.strip() for l in p.stdout.decode("utf-8", "replace").splitlines() if "mentions" in l]
    out.write("  tools/check_run2_ratchet.sh: exit %d, %s\n" % (p.returncode, tail[-1] if tail else ""))
    out.write(LEAN_HOST_COMMANDS)
    return 1 if failures else 0


# --------------------------------------------------------------------------------------------
# --transplant
# --------------------------------------------------------------------------------------------

def commit_meta(repo, sha):
    raw = git(["cat-file", "commit", sha], repo.root)
    head, _, msg = raw.partition(b"\n\n")
    env = {}
    for line in head.split(b"\n"):
        for key, var in ((b"author ", "AUTHOR"), (b"committer ", "COMMITTER")):
            if line.startswith(key):
                rest = line[len(key):].decode("utf-8", "surrogateescape")
                m = re.match(r"^(.*) <(.*)> (\d+ [+-]\d{4})$", rest)
                if not m:
                    raise Refusal("cannot parse the %s line of %s" % (key.decode().strip(), sha))
                env["GIT_%s_NAME" % var], env["GIT_%s_EMAIL" % var], env["GIT_%s_DATE" % var] = m.groups()
    return env, msg


def make_commit(repo, tree, parents, env, msg):
    e = dict(os.environ)
    e.update(env)
    args = ["commit-tree", tree]
    for p in parents:
        args += ["-p", p]
    return git(args, repo.root, data=msg, env=e).decode().strip()


def add_trailer(repo, msg, trailer):
    return git(["interpret-trailers", "--trailer", trailer], repo.root, data=msg)


def is_ancestor(root, a, b):
    return subprocess.run(["git", "merge-base", "--is-ancestor", a, b], cwd=root).returncode == 0


def untouched_but_changed(repo, old_c, tip, new_c, head):
    """Paths the branch never changed (same blob at OLD and at its tip) whose transplanted version
    differs from NEW's.  S is per file except pin transport, so each one holds a hash pin of a file
    the branch changed and left stale; S keeps a stale pin stale, so the pin reads as reverted."""
    o, t, n, h = (repo.ls_tree(r) for r in (old_c, tip, new_c, head))
    out = []
    for p in sorted(o):
        if t.get(p) != o[p]:
            continue
        np = p if p in SELF_PATHS else rename_str(p)
        if n.get(np) != h.get(np):
            out.append(np)
    return out


def run_transplant(root, rules, old_base, new_base, branch, merge, to_ref, out=sys.stdout):
    repo = Repo(root)
    memo = Memo()
    try:
        old_c, new_c, tip = repo.rev(old_base), repo.rev(new_base), repo.rev(branch)
        version = version_line()
        if old_c == new_c:
            raise Refusal("--old-base and --new-base are the same commit %s" % old_c[:12])
        quoted = VERSION_LINE_RE.findall(git(["log", "-1", "--format=%B", new_c], root).decode("utf-8", "replace"))
        if quoted and version not in quoted:
            raise Refusal("%s was made by `%s`, and this script is `%s`: run the copy that made it, e.g. "
                          "mkdir /tmp/r2p && git archive %s tools/rename_to_proglib.py tools/rename_to_proglib.allow"
                          " | tar -x -C /tmp/r2p && python3 /tmp/r2p/tools/rename_to_proglib.py --transplant ..."
                          % (new_base, quoted[0], version, old_base))
        if not quoted:
            out.write("note: %s quotes no version line (a dry run?); only the tree check below binds the "
                      "script to it\n" % new_base)
        if not is_ancestor(root, old_c, new_c):
            raise Refusal("%s is not an ancestor of %s: the rename commit's parent is the old base"
                          % (old_base, new_base))
        if is_ancestor(root, new_c, tip):
            raise Refusal("%s already contains %s: it has crossed the rename already (transplant the "
                          "original old-name branch, never its transplant)" % (branch, new_base))
        want, _ = s_tree(repo, old_c, rules, memo)
        have = repo.rev(new_c, "tree")
        if want != have:
            raise Refusal("tree(%s) = %s is not S(tree(%s)) = %s: a different script version or a wrong "
                          "base" % (new_base, have[:12], old_base, want[:12]))
        if not is_ancestor(root, old_c, tip):
            raise Refusal("%s does not contain %s: catch up onto the old base first (step 0, in old names)"
                          % (branch, old_base))
        name = branch[len("refs/heads/"):] if branch.startswith("refs/heads/") else branch
        ref = to_ref or "refs/heads/%s-proglib" % name
        if subprocess.run(["git", "rev-parse", "--verify", "-q", ref], cwd=root,
                          stdout=subprocess.DEVNULL).returncode == 0:
            raise Refusal("%s exists already; pass --to with a fresh ref" % ref)

        def renamed(c):
            try:
                return s_tree(repo, c, rules, memo)[0]
            except Refusal as e:
                subject = git(["log", "-1", "--format=%s", c], root).decode("utf-8", "replace").strip()
                raise Refusal("at commit %s (%s): %s" % (c[:12], subject[:60], e))

        if merge:
            tree = renamed(tip)
            msg = ("Transplant %s onto %s across the %s rename\n\nThe tree is S(tree(%s)), computed by "
                   "tools/rename_to_proglib.py (%s).\n\nRenamed-from: %s\n" % (name, new_c[:12], LIB, tip[:12],
                                                                               version, tip)).encode()
            env, _ = commit_meta(repo, tip)
            head = make_commit(repo, tree, [new_c, tip], env, msg)
            count = 1
        else:
            merges = git(["rev-list", "--merges", "%s..%s" % (old_c, tip)], root).split()
            if merges:
                raise Refusal("%s..%s has %d merge commit(s): replay needs a linear range; use --merge, or "
                              "linearize first with `git rebase %s`" % (old_base, branch, len(merges), old_base))
            commits = git(["rev-list", "--reverse", "--topo-order", "%s..%s" % (old_c, tip)], root).decode().split()
            head = new_c
            for c in commits:
                tree = renamed(c)
                env, msg = commit_meta(repo, c)
                msg = add_trailer(repo, msg, "Renamed-from: %s" % c)
                head = make_commit(repo, tree, [head], env, msg)
            count = len(commits)
        git(["update-ref", ref, head, ""], root)
        out.write("transplanted %d commit(s) of %s onto %s: %s = %s\n" % (count, branch, new_c[:12], ref, head))
        stale = untouched_but_changed(repo, old_c, tip, new_c, head)
        if stale:
            out.write("WARNING: %d file(s) differ from %s although %s never changed them. Each holds a hash "
                      "pin of a file the branch changed without updating this pin; the rename keeps a stale "
                      "pin stale, so it now reads as a revert of the rename commit's re-pin. Re-pin it in a "
                      "follow-up commit:\n" % (len(stale), new_base, branch))
            for p in stale:
                out.write("  %s\n" % p)
        if merge:
            out.write("MERGE mode: from now on this branch follows master by `git merge` only; a rebase "
                      "would replay its old-name commits\n")
        return head
    finally:
        repo.close()



# --------------------------------------------------------------------------------------------
# --self-test
# --------------------------------------------------------------------------------------------

FIXTURE_RULES = (
    "path\tCHANGELOG.md\t# record\n"
    "path\tdocs/backlog/**\t# record\n"
    "path\t**/*.sv\t# HDL source\n"
    "path\tsvgolf/**\t# moves later\n"
    "path\tbin.dat\t# binary fixture\n"
    "path\tdocs/brief.pdf\t# a kept PDF\n"
    "token\tLeanModels/VerilogA/Envelope.lean\tlean-models.veriloga.openvaf-ast.v1\t# wire format id\n"
    "line\tREADME.md\tformerly `LeanModels`\t# the rename note\n"
    "line\tdocs/sv-coverage.md\tLeanModels\\.Loud\\.unsupported\t# captured output\n"
    "class\tnotebook-outputs\t# saved outputs\n"
    "class\trecord-marker-paths\t# docs_check markers in records\n")


def _pdf(text):
    return (b"%PDF-1.5\n%\xe2\xe3\xcf\xd3\n1 0 obj\n<< /Filter /FlateDecode >>\nstream\n"
            + zlib.compress(text) + b"\nendstream\nendobj\n%%EOF\n")


def _fixture_files():
    basic = b"namespace LeanModels\ndef x := 1\nend LeanModels\n-- see `leanmodels-run`\n"
    nb = {"cells": [{"cell_type": "code", "execution_count": 1, "metadata": {},
                     "outputs": [{"output_type": "stream", "name": "stdout",
                                  "text": ["leanmodels-run on tri.json, 0.04s\n"]}],
                     "source": ["open LeanModels.Sv\n", "#eval 1"]}],
          "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    return {
        "LeanModels.lean": ("100644", b"import LeanModels.Core.Basic\n"),
        "LeanModels/Core/Basic.lean": ("100644", basic),
        "LeanModels/VerilogA/Envelope.lean": ("100644", b'def schema := "lean-models.veriloga.openvaf-ast.v1"\n'
                                              b"-- LeanModels.VerilogA\n"),
        "lakefile.toml": ("100644", b'name = "lean-models"\ndefaultTargets = ["LeanModels", "leanmodels-run"]\n'
                          b'[[lean_lib]]\nname = "LeanModels"\n[[lean_exe]]\nname = "leanmodels-run"\n'
                          b'root = "Main"\n[[lean_exe]]\nname = "other"\nroot = "LeanModels.Other"\n'),
        "lake-manifest.json": ("100644", ('{"name": "«lean-models»"}\n').encode("utf-8")),
        "README.md": ("100644", b"# x\n\n*Renamed: was `lean-surfaces`.\n" + F1_OLD + b"\n\n```\n"
                      b"LeanModels.lean   # root\n```\n\nSee `LeanModels/Core/Basic.lean`.  Next.\n"),
        "CHANGELOG.md": ("100644", b"# Changelog\n\n## Unreleased\n\n" + F2_ANCHOR +
                         b" (2026-11-10).\n  LeanModels stays.\n"),
        "docs/backlog/x.md": ("100644", b"```\n-- LeanModels/Core/Basic.lean (excerpt)\ndef x := 1\n```\n"
                              b"LeanModels history\n"),
        "docs/guide.md": ("100644", b"```lean\n-- LeanModels/Core/Basic.lean\nnamespace LeanModels  -- x\n```\n"
                          b"\n### Rule\n\n    LeanModels/<L>/   -- x\n\n- item\n\n    LeanModels/y   z\n"),
        "docs/sv-coverage.md": ("100644", b"| halted: LeanModels.Loud.unsupported (LeanModels.RefusalCause) |\n"
                                b"| LeanModels.Sv |\n"),
        "notebooks/n.ipynb": ("100644", nb_dump(nb)),
        "x.sv": ("100644", b"// LeanModels/Sv/A.lean\n"),
        "data/pins.json": ("100644", ('{"a": "%s", "blob": "%s", "stale": "%s"}\n'
                                      % (sha256(basic), blob_id(basic), "ab" * 32)).encode()),
        "docs/notes.md": ("100644", ("measured: %s\n" % sha256(basic)).encode()),
        "tools/run.sh": ("100755", b'exec .lake/build/bin/leanmodels-run "$@"\n'),
        "tools/x.py": ("100644", b"# the lean_models project\nP = 'LeanModels/Core'\n"),
        "tools/rename_to_proglib.allow": ("100644", b"path\tLeanModels\t# self\n"),
        "bin.dat": ("100644", b"\0LeanModels"),
        "docs/brief.pdf": ("100644", _pdf(b"BT (LeanModels/Sv/**) Tj ET")),
        "svgolf/a.lean": ("100644", b"import LeanModels.Sv\n"),
        "Main.lean": ("100644", b"import LeanModels\n"),
        "LeanModels/C.lean": ("100644", b"/-! because `lean-surfaces` is a\nfamily -/\nimport LeanModels.Core.Basic\n"),
    }


def _write_files(root, files):
    for p, (mode, data) in files.items():
        full = os.path.join(root, p)
        os.makedirs(os.path.dirname(full) or root, exist_ok=True)
        with open(full, "wb") as fh:
            fh.write(data)
        os.chmod(full, 0o755 if mode == "100755" else 0o644)


def run_self_test(out=sys.stdout):
    failures = []

    def ok(name, cond):
        out.write("  %s %s\n" % ("ok  " if cond else "FAIL", name))
        if not cond:
            failures.append(name)

    saved = dict(os.environ)
    tmp = tempfile.mkdtemp(prefix="rename-to-proglib-selftest-")
    os.environ.update({"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
                       "GIT_AUTHOR_NAME": "T", "GIT_AUTHOR_EMAIL": "t@example.invalid",
                       "GIT_COMMITTER_NAME": "T", "GIT_COMMITTER_EMAIL": "t@example.invalid",
                       "GIT_AUTHOR_DATE": "1700000000 +0000", "GIT_COMMITTER_DATE": "1700000000 +0000"})
    sink = open(os.devnull, "w")
    try:
        rules = Rules(FIXTURE_RULES, "<fixture>")
        root = os.path.join(tmp, "repo")
        os.makedirs(root)
        git(["init", "-q", "-b", "master"], root)
        _write_files(root, _fixture_files())
        git(["add", "-A"], root)
        git(["commit", "-q", "-m", "base"], root)
        base = git(["rev-parse", "HEAD"], root).decode().strip()

        def read(p):
            with open(os.path.join(root, p), "rb") as fh:
                return fh.read()

        out.write("apply:\n")
        rep = apply_worktree(root, rules, out=sink)
        tree1 = git(["write-tree"], root).decode().strip()
        ok("the library moves", os.path.isfile(os.path.join(root, "Proglib/Core/Basic.lean"))
           and os.path.isfile(os.path.join(root, "Proglib.lean"))
           and not os.path.exists(os.path.join(root, "LeanModels")))
        basic = read("Proglib/Core/Basic.lean")
        ok("namespaces and the runner follow", basic == b"namespace Proglib\ndef x := 1\nend Proglib\n"
           b"-- see `proglib-run`\n")
        ok("imports follow", read("Proglib.lean") == b"import Proglib.Core.Basic\n")
        env = read("Proglib/VerilogA/Envelope.lean")
        ok("a protected token stays, the rest follows",
           env == b'def schema := "lean-models.veriloga.openvaf-ast.v1"\n-- Proglib.VerilogA\n')
        lake = read("lakefile.toml")
        ok("the lakefile follows, exe order kept", b'name = "proglib"' in lake
           and b'["Proglib", "proglib-run"]' in lake and lake_exes(lake) == ["proglib-run", "other"]
           and b'root = "Proglib.Other"' in lake)
        ok("the manifest name loses its guillemets", read("lake-manifest.json") == b'{"name": "proglib"}\n')
        readme = read("README.md")
        ok("F1 rewrites the note and keeps it", F1_NEW in readme and F1_OLD not in readme)
        ok("F3 re-pads a code block", b"Proglib.lean      # root\n" in readme)
        ok("F3 leaves prose spacing alone", b"See `Proglib/Core/Basic.lean`.  Next." in readme)
        cl = read("CHANGELOG.md")
        ok("F2 inserts the bullet above the anchor, past text stays",
           cl.index(F2_MARK) < cl.index(F2_ANCHOR) and b"  LeanModels stays.\n" in cl)
        ok("F5 renames a record's marker path only",
           read("docs/backlog/x.md") == b"```\n-- Proglib/Core/Basic.lean (excerpt)\ndef x := 1\n```\n"
           b"LeanModels history\n")
        guide = read("docs/guide.md")
        ok("a marked block is renamed but never re-padded",
           guide.startswith(b"```lean\n-- Proglib/Core/Basic.lean\nnamespace Proglib  -- x\n```\n"))
        ok("F3 re-pads an indented code block, not a list continuation",
           guide.endswith(b"\n    Proglib/<L>/      -- x\n\n- item\n\n    Proglib/y   z\n"))
        ok("a protected line stays", read("docs/sv-coverage.md") ==
           b"| halted: LeanModels.Loud.unsupported (LeanModels.RefusalCause) |\n| Proglib.Sv |\n")
        nb = json.loads(read("notebooks/n.ipynb").decode())
        ok("notebook: source follows, outputs stay", nb["cells"][0]["source"][0] == "open Proglib.Sv\n"
           and nb["cells"][0]["outputs"][0]["text"][0].startswith("leanmodels-run on"))
        ok("HDL, svGolf, binary, self untouched",
           read("x.sv") == b"// LeanModels/Sv/A.lean\n" and read("svgolf/a.lean") == b"import LeanModels.Sv\n"
           and read("bin.dat") == b"\0LeanModels" and read("tools/rename_to_proglib.allow") == b"path\tLeanModels\t# self\n")
        ok("a kept PDF stays byte-identical", read("docs/brief.pdf") == _fixture_files()["docs/brief.pdf"][1])
        ok("F6: the step-1 project name in a Lean docstring follows",
           read("Proglib/C.lean") == b"/-! because `proglib` is a\nfamily -/\nimport Proglib.Core.Basic\n")
        no_f5 = Rules("".join(l for l in FIXTURE_RULES.splitlines(True) if "record-marker-paths" not in l))
        rec = "docs/backlog/x.md"
        ok("without `class record-marker-paths` a record keeps every byte (F5 off)",
           compute({rec: _fixture_files()[rec]}, no_f5)[0][rec] == _fixture_files()[rec])
        pins = json.loads(read("data/pins.json").decode())
        ok("F4: a valid pin is transported (sha256 and blob id)",
           pins["a"] == sha256(basic) and pins["blob"] == blob_id(basic))
        ok("F4: a stale pin stays stale", pins["stale"] == "ab" * 32)
        ok("F4: a pin in prose is listed, not edited", read("docs/notes.md").decode().strip().endswith(
            sha256(_fixture_files()["LeanModels/Core/Basic.lean"][1]))
           and any(p[0] == "docs/notes.md" for p in rep.pins_not_scanned))
        ok("modes are kept", os.access(os.path.join(root, "tools/run.sh"), os.X_OK)
           and read("tools/run.sh") == b'exec .lake/build/bin/proglib-run "$@"\n')
        ok("prose project name follows", read("tools/x.py") == b"# the proglib project\nP = 'Proglib/Core'\n")
        st = git(["status", "--porcelain"], root).splitlines()
        ok("apply stages everything it does (no unstaged or untracked change)",
           st and all(l[1:2] == b" " and not l.startswith(b"??") for l in st))
        ok("--check is clean on the result", run_check(read_worktree(root), rules, out=sink) == 0)
        git(["commit", "-q", "-m", "rename"], root)
        r2 = git(["rev-parse", "HEAD"], root).decode().strip()
        apply_worktree(root, rules, out=sink)
        ok("idempotent: a second apply changes nothing", git(["write-tree"], root).decode().strip() == tree1)
        repo = Repo(root)
        t_obj, _ = s_tree(repo, base, rules)
        repo.close()
        ok("--tree (object level) equals apply", t_obj == tree1)
        clone = os.path.join(tmp, "clone")
        git(["clone", "-q", root, clone], tmp)
        git(["checkout", "-q", base], clone)
        apply_worktree(clone, rules, out=sink)
        ok("deterministic: a fresh checkout gives the same tree", git(["write-tree"], clone).decode().strip() == tree1)

        out.write("check:\n")
        with open(os.path.join(root, "Proglib/Core/Late.lean"), "wb") as fh:
            fh.write(b"import Proglib.Core.Missing\n-- LeanModels.Core\n")
        git(["add", "-A"], root)
        buf = _Buf()
        rc = run_check(read_worktree(root), rules, out=buf)
        ok("--check finds a residue and an unresolved import", rc == 1 and "Late.lean:2" in buf.text
           and "names no tracked file" in buf.text)
        with open(os.path.join(root, "docs/hidden.pdf"), "wb") as fh:
            fh.write(_pdf(b"BT (LeanModels/Rv/**) Tj ET"))
        git(["add", "-A"], root)
        buf = _Buf()
        run_check(read_worktree(root), rules, out=buf)
        ok("--check sees an old spelling inside a compressed PDF stream",
           "docs/hidden.pdf:0: binary file holds 1 old spelling(s), 1 of them inside compressed" in buf.text)
        ok("--check reads a revision", run_check(Repo(root).read_tree(r2), rules, out=sink) == 0)
        git(["reset", "-q", "--hard"], root)

        out.write("refusals:\n")
        with open(os.path.join(root, "Proglib.lean"), "ab") as fh:
            fh.write(b"-- dirty\n")
        ok("a dirty tree is refused", _refuses(lambda: apply_worktree(root, rules, out=sink)))
        git(["checkout", "-q", "--", "Proglib.lean"], root)
        items = read_worktree(root)
        items["LeanModels/Core/Basic.lean"] = ("100644", b"different\n")
        why = _refusal(lambda: compute(items, rules))
        ok("a path collision is refused, naming both paths", why is not None
           and "LeanModels/Core/Basic.lean and Proglib/Core/Basic.lean both become" in why)
        items = read_worktree(root)
        items["link"] = ("120000", b"LeanModels/Core")
        ok("a symlink that needs renaming is refused", _refuses(lambda: compute(items, rules)))
        items = read_worktree(root)
        items["nb2.ipynb"] = ("100644", json.dumps({"cells": [{"source": ["LeanModels"]}]}, indent=2).encode())
        ok("a notebook that does not round-trip is refused", _refuses(lambda: compute(items, rules)))
        same = dict(items)
        del same["nb2.ipynb"]
        same["LeanModels/Core/Basic.lean"] = ("100644", _fixture_files()["LeanModels/Core/Basic.lean"][1])
        try:
            got, _ = compute(same, rules)
            ok("an identical old/new pair collapses", "LeanModels/Core/Basic.lean" not in got)
        except Refusal:
            ok("an identical old/new pair collapses", False)

        out.write("transplant:\n")
        git(["checkout", "-q", "-b", "lane", base], root)
        with open(os.path.join(root, "LeanModels/Core/New.lean"), "wb") as fh:
            fh.write(b"import LeanModels.Core.Basic\n")
        git(["add", "-A"], root)
        git(["commit", "-q", "-m", "lane: add a file under the old directory\n\nCo-Authored-By: X <x@x>"], root)
        with open(os.path.join(root, "LeanModels/Core/Basic.lean"), "ab") as fh:
            fh.write(b"-- lane edit of LeanModels.Core.Basic\n")
        git(["commit", "-q", "-am", "lane: edit"], root)
        lane_tip = git(["rev-parse", "HEAD"], root).decode().strip()
        buf = _Buf()
        head = run_transplant(root, rules, base, r2, "lane", False, None, out=buf)
        ok("a pin the lane left stale is named (F-3): data/pins.json pins the old Basic.lean",
           "WARNING: 1 file(s) differ" in buf.text and "  data/pins.json\n" in buf.text)
        repo = Repo(root)
        commits = git(["rev-list", "--reverse", "%s..%s" % (r2, head)], root).decode().split()
        origs = git(["rev-list", "--reverse", "%s..%s" % (base, lane_tip)], root).decode().split()
        ok("replay: one commit per lane commit, parented on R2",
           len(commits) == 2 and git(["rev-parse", commits[0] + "^"], root).decode().strip() == r2)
        ok("replay: every tree is S(tree(original))",
           all(repo.rev(c, "tree") == s_tree(repo, o, rules)[0] for c, o in zip(commits, origs)))
        ok("replay: the lane's new file lands under the new directory",
           b"import Proglib.Core.Basic\n" == repo.read_tree(head).get("Proglib/Core/New.lean", ("", b""))[1])
        msg = git(["log", "-1", "--format=%B", commits[0]], root)
        ok("replay: message, trailers and Renamed-from kept",
           b"Co-Authored-By: X <x@x>\nRenamed-from: " + origs[0].encode() in msg)
        again = run_transplant(root, rules, base, r2, "lane", False, "refs/heads/lane-again", out=sink)
        ok("replay is deterministic (same commit ids)", again == head)
        ok("the same commit as old and new base is refused",
           _refuses(lambda: run_transplant(root, rules, base, base, "lane", False, "refs/heads/x", out=sink)))
        base_tree = repo.rev(base, "tree")
        bogus = git(["commit-tree", base_tree, "-p", base, "-m", "not S"], root).decode().strip()
        ok("a new base whose tree is not S(tree(old)) is refused",
           "is not S(tree(" in (_refusal(lambda: run_transplant(root, rules, base, bogus, "lane", False,
                                                                 "refs/heads/x", out=sink)) or ""))
        r2_tree = repo.rev(r2, "tree")
        other = git(["commit-tree", r2_tree, "-p", base, "-m", "rename\n\nrename_to_proglib v9 " + "0" * 64],
                    root).decode().strip()
        ok("a new base made by another script version is refused (F-4)",
           "and this script is" in (_refusal(lambda: run_transplant(root, rules, base, other, "lane", False,
                                                                    "refs/heads/x", out=sink)) or ""))
        same = git(["commit-tree", r2_tree, "-p", base, "-m", "rename\n\n" + version_line()], root).decode().strip()
        ok("a new base quoting this script's version line is accepted",
           run_transplant(root, rules, base, same, "lane", False, "refs/heads/lane-v", out=sink) is not None)
        ok("a branch that crossed already is refused (F-5)",
           "already contains" in (_refusal(lambda: run_transplant(root, rules, base, r2, "lane-proglib", False,
                                                                  "refs/heads/x", out=sink)) or ""))
        memo = Memo()
        ok("a memo gives the same trees as none (base, rename, every lane commit)",
           all(s_tree(repo, c, rules, memo)[0] == s_tree(repo, c, rules)[0] for c in [base, r2] + origs + [base]))
        git(["checkout", "-q", "-b", "side", base], root)
        with open(os.path.join(root, "side.txt"), "wb") as fh:
            fh.write(b"LeanModels side\n")
        git(["add", "-A"], root)
        git(["commit", "-q", "-m", "side"], root)
        git(["checkout", "-q", "lane"], root)
        git(["merge", "-q", "--no-edit", "side"], root)
        merged = git(["rev-parse", "HEAD"], root).decode().strip()
        ok("replay refuses a merge commit",
           _refuses(lambda: run_transplant(root, rules, base, r2, "lane", False, "refs/heads/y", out=sink)))
        mh = run_transplant(root, rules, base, r2, "lane", True, "refs/heads/lane-merge", out=sink)
        parents = git(["log", "-1", "--format=%P", mh], root).decode().split()
        ok("merge mode: parents (R2, tip), tree S(tip)", parents == [r2, merged]
           and repo.rev(mh, "tree") == s_tree(repo, merged, rules)[0])
        repo.close()
    finally:
        sink.close()
        os.environ.clear()
        os.environ.update(saved)
        shutil.rmtree(tmp, ignore_errors=True)
    out.write("self-test: %d failure(s)\n" % len(failures))
    return 1 if failures else 0


class _Buf(object):
    def __init__(self):
        self.text = ""

    def write(self, s):
        self.text += s


def _refuses(fn):
    return _refusal(fn) is not None


def _refusal(fn):
    """The message of the Refusal FN raises, or None."""
    try:
        fn()
    except Refusal as e:
        return str(e)
    return None


# --------------------------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", nargs="?", help="apply")
    ap.add_argument("branch", nargs="?", help="the branch to transplant")
    ap.add_argument("-C", dest="root", default=None, help="the repository (default: the current directory)")
    ap.add_argument("--dry-run", action="store_true", help="apply: compute and report, write nothing")
    ap.add_argument("--json", metavar="FILE", help="apply: also write the report as JSON")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--rev", metavar="REV", help="--check: read REV through git instead of the working tree")
    ap.add_argument("--limit", type=int, default=200, help="--check: residues printed (default 200)")
    ap.add_argument("--regenerate", action="store_true")
    ap.add_argument("--write", action="store_true", help="--regenerate: write instead of compare")
    ap.add_argument("--python39", default="python3.9", help="--regenerate: the pinned Python frontend")
    ap.add_argument("--tree", metavar="REV", help="print the id of S(tree(REV)); writes objects, no worktree")
    ap.add_argument("--transplant", action="store_true")
    ap.add_argument("--old-base")
    ap.add_argument("--new-base")
    ap.add_argument("--merge", action="store_true")
    ap.add_argument("--to", metavar="REF")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--version", action="store_true", help="print the version line only")
    a = ap.parse_args(argv)
    os.environ["GIT_NO_LAZY_FETCH"] = "1"     # no network: a partial clone's missing blob refuses loudly
    print(version_line())
    sys.stdout.flush()
    if a.version:
        return 0
    root = a.root or os.getcwd()
    try:
        if a.self_test:
            return run_self_test()
        rules = Rules.load()
        if a.transplant:
            branch = a.branch or a.mode
            if not (a.old_base and a.new_base and branch):
                ap.error("--transplant needs --old-base, --new-base and BRANCH")
            run_transplant(root, rules, a.old_base, a.new_base, branch, a.merge, a.to)
            return 0
        top = git(["rev-parse", "--show-toplevel"], root).decode().strip()
        if a.check:
            items = Repo(top).read_tree(a.rev) if a.rev else read_worktree(top)
            return run_check(items, rules, limit=a.limit)
        if a.regenerate:
            return run_regenerate(top, a.write, python39=a.python39)
        if a.tree:
            repo = Repo(top)
            try:
                tree, rep = s_tree(repo, a.tree, rules)
            finally:
                repo.close()
            rep.print(sys.stdout)
            print("S(tree(%s)) = %s" % (a.tree, tree))
            return 0
        if a.mode == "apply":
            apply_worktree(top, rules, dry_run=a.dry_run, json_path=a.json)
            return 0
        ap.print_help()
        return 2
    except Refusal as e:
        print("rename_to_proglib: REFUSED: %s" % e, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
