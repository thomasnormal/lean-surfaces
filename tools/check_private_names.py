#!/usr/bin/env python3
"""check_private_names.py -- keep private site names out of the public tree.

Run from anywhere:  python3 tools/check_private_names.py
                    python3 tools/check_private_names.py --self-test
                    python3 tools/check_private_names.py --hash 'NAME'

This repository is public. Internal host names, internal tool names, private
organizations and repositories, and per-user machine paths must not appear in
any tracked file (prose, comments, data, notebooks and their stored outputs).
Where a script needs such a value it reads an environment variable instead
(e.g. `SV_XCELIUM_SSH_HOST` / `SV_XCELIUM_GATE`, docs/sv-xcelium-reference.md).

The names themselves are NOT in this file: `HASHES` holds the sha256 hex
digest of each lower-cased name, so the guard does not publish what it guards.
To add one, print its digest with `--hash 'NAME'` and paste the digest (never
the name) into `HASHES`. The owner's public name in prose is not private.

WHAT IS COMPARED. Every tracked file (`git ls-files`; a file with a NUL byte
in its first 8 KiB is binary and skipped) is lower-cased and split into WORDS
(maximal runs of `[a-z0-9]`). Candidates are hashed and looked up:

  * every word                                    (`name`)
  * every two adjacent words joined by `-` or `_`  (`two-part` hosts, user
    names and path segments: `/x/two-part/y`, `ssh two_part`, `a-two-part-b`)
  * every two adjacent words separated by whitespace only (`two words`)
  * each of the above with every digit run replaced by `#`, so one digest
    covers a numbered family (`host-#` matches `host-0`, `host-17`)

ALLOWLIST. `ALLOW` maps a repo-relative path to digests tolerated in that file
(history-quoting files only). It is empty: history is not rewritten, but the
current tree carries none of the names.

Exit 0 when no tracked file carries a listed name; 1 listing every hit as
`path:line: private name 'token'`; 2 on a usage or git error. Stdlib only.
"""

import hashlib
import os
import re
import secrets
import shutil
import subprocess
import sys
import tempfile

# sha256 of each lower-cased private name (see the docstring; never the names).
HASHES = frozenset({
    "22401eb8e24d09c96e0d26fa62f49d46d910cec1d4a9d0fff8d490c76163994b",
    "a0a84efbcb3ef4854b77444558c9e921523d81b94531e78423d54b9e47070a33",
    "5d7f1e7bbc8415ebb16dd570748b3e7c3fde218389bc3661b0a234e15dbf39bd",
    "9f14cdb6ad4921a0a23bd3d8ca6a5c027aba51295a0be35b094565226847d7d3",
    "d7b82b3ed87a0c49f268db9889b20e35ef80b91aaee7819eb37903aaf8b05add",
    "239f3848caba0f6e702977686267118cc98bf4391c583afae960bc2aea05dd20",
    "c4dec94f85d5d7a6e26cea96fdafc53628961f1eff5e8265a3d98f6cbb8a5ca8",
    "a542ea2b200ae38dabdd323cdf81dcd2a685b1a76e1f595be0f37f44504e0115",
    "e7196477f72e5d6dde768067498cc55340df3a104e97a5ed7f875f82efddd258",
    "2c3faf16f4269242d659c5abd69a7e746fb1ff19df69fd2bca1d695be902708f",
    "9c2b977bf0a4ebcfc75c19e9f996a739af114684cb2c965216f4c1994a109803",
})

# repo-relative path -> digests tolerated there. Prefer none.
ALLOW = {}

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WORD = re.compile(r"[a-z0-9]+")
DIGITS = re.compile(r"[0-9]+")
BINARY_PROBE = 8192


def digest(name):
    return hashlib.sha256(name.lower().encode("utf-8")).hexdigest()


def candidates(text):
    """Yield (token, offset) for every candidate of lower-cased `text`."""
    prev = None
    for m in WORD.finditer(text):
        w = m.group()
        yield w, m.start()
        if prev is not None:
            sep = text[prev.end():m.start()]
            if sep in ("-", "_"):
                yield prev.group() + "-" + w, prev.start()
            elif sep and sep.isspace():
                yield prev.group() + " " + w, prev.start()
        prev = m


def scan_text(text, hashes, cache):
    """[(offset, token)] of the listed names in `text`."""
    hits = []
    for tok, off in candidates(text.lower()):
        for form in ((tok, DIGITS.sub("#", tok)) if any(c.isdigit() for c in tok) else (tok,)):
            h = cache.get(form)
            if h is None:
                h = cache[form] = hashlib.sha256(form.encode("utf-8")).hexdigest()
            if h in hashes:
                hits.append((off, tok))
                break
    return hits


def tracked_files(root):
    env = {k: v for k, v in os.environ.items()
           if k not in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE")}
    p = subprocess.run(["git", "-C", root, "ls-files", "-z"], stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, env=env)
    if p.returncode != 0:
        raise RuntimeError("git ls-files failed in %s: %s" % (root, p.stderr.decode(errors="replace").strip()))
    return [f for f in p.stdout.decode("utf-8", "surrogateescape").split("\0") if f]


def scan(root, hashes=HASHES, allow=None):
    """Returns (files scanned, [(path, line, token)])."""
    allow = ALLOW if allow is None else allow
    cache = {}
    findings = []
    n = 0
    for rel in tracked_files(root):
        path = os.path.join(root, rel)
        if not os.path.isfile(path) or os.path.islink(path):
            continue
        with open(path, "rb") as f:
            data = f.read()
        if b"\0" in data[:BINARY_PROBE]:
            continue
        n += 1
        text = data.decode("utf-8", "replace")
        ok = allow.get(rel, frozenset())
        for off, tok in scan_text(text, hashes, cache):
            if digest(tok) in ok or digest(DIGITS.sub("#", tok)) in ok:
                continue
            findings.append((rel, text.count("\n", 0, off) + 1, tok))
    return n, findings


def self_test():
    """Plant synthetic names (hashed at run time) in a scratch git repo and
    check that every planted form is caught and nothing else is."""
    word = "zq" + secrets.token_hex(4)
    pair = ("zq" + secrets.token_hex(3), "x" + secrets.token_hex(2))
    spaced = ("zq" + secrets.token_hex(3), "y" + secrets.token_hex(2))
    family = "zq" + "".join(secrets.choice("abcdefghjkmnpqrstuvwxyz") for _ in range(8))  # no digits
    hashes = frozenset({digest(word), digest("%s-%s" % pair), digest("%s %s" % spaced),
                        digest(family + "-#")})
    failures = []

    def expect(cond, what):
        if not cond:
            failures.append(what)

    expect(all(re.fullmatch(r"[0-9a-f]{64}", h) for h in HASHES), "HASHES are 64-hex digests")
    expect(not (hashes & HASHES), "synthetic digests are fresh")
    tmp = tempfile.mkdtemp(prefix="check-private-names-")
    try:
        env = {k: v for k, v in os.environ.items()
               if k not in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE")}
        subprocess.run(["git", "init", "-q", tmp], check=True, env=env)
        planted = {
            "docs/a.md": ("intro\nrun it on %s today\n" % word.upper(), [(2, word)]),
            "paths.txt": ("x=/var/tmp/%s-%s/bin/tool\n" % pair, [(1, "%s-%s" % pair)]),
            "under.py": ("HOST = 'ssh %s_%s'\n" % (pair[0].upper(), pair[1]), [(1, "%s-%s" % pair)]),
            "inner.json": ('{"p": "/tmp/c-home-%s-%s-models/x"}\n' % pair, [(1, "%s-%s" % pair)]),
            "spaced.md": ("one\ntwo %s\n  %s three\n" % spaced, [(2, "%s %s" % spaced)]),
            "family.txt": ("a %s-0 b\nc %s-17\n" % (family, family),
                           [(1, family + "-0"), (2, family + "-17")]),
            "clean.md": ("%s%s and %s.%s are not the name\n" % (pair[0], pair[1], spaced[0], spaced[1]), []),
            "notebook.ipynb": ('{"outputs": ["repo root : /scratch/%s/wt\\n"]}\n' % word, [(1, word)]),
        }
        for rel, (body, _) in planted.items():
            os.makedirs(os.path.dirname(os.path.join(tmp, rel)) or tmp, exist_ok=True)
            with open(os.path.join(tmp, rel), "w") as f:
                f.write(body)
        with open(os.path.join(tmp, "blob.bin"), "wb") as f:
            f.write(b"\0\1" + word.encode())
        with open(os.path.join(tmp, "untracked.md"), "w") as f:
            f.write(word + "\n")
        subprocess.run(["git", "-C", tmp, "add", "--", *planted, "blob.bin"], check=True, env=env)
        n, found = scan(tmp, hashes, allow={})
        expect(n == len(planted), "binary file skipped (%d text files scanned)" % n)
        want = sorted((rel, line, tok) for rel, (_, hits) in planted.items() for line, tok in hits)
        expect(sorted(found) == want, "planted forms caught exactly: got %s" % sorted(found))
        n2, found2 = scan(tmp, hashes, allow={"docs/a.md": frozenset({digest(word)})})
        expect(("docs/a.md", 2, word) not in found2 and len(found2) == len(want) - 1, "allowlist")
        _, real = scan(tmp, HASHES, allow={})
        expect(real == [], "synthetic names are not real ones")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    for f in failures:
        print("check_private_names self-test FAILED: %s" % f)
    if not failures:
        print("check_private_names self-test: ok (8 planted forms, binary/untracked/allowlist rows)")
    return 1 if failures else 0


def main(argv):
    if argv[:1] == ["--self-test"]:
        return self_test()
    if argv[:1] == ["--hash"] and len(argv) == 2:
        print(digest(argv[1]))
        return 0
    if argv:
        print(__doc__.split("\n\n")[1])
        return 2
    try:
        n, findings = scan(REPO)
    except RuntimeError as e:
        print("check_private_names: %s" % e)
        return 2
    for rel, line, tok in findings:
        print("%s:%d: private name %r (rewrite it generically; see tools/check_private_names.py)"
              % (rel, line, tok))
    print("check_private_names: %d tracked text files, %d finding(s)" % (n, len(findings)))
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
