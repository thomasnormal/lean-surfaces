#!/usr/bin/env python3
"""c_corpus_fetch.py — gcc.c-torture AT A PIN, into a cache OUTSIDE this repo.

WHY THIS EXISTS.  `docs/c23-goal.md` §2: the GCC testsuite is
GPL-3.0-or-later and is **not vendorable**.  The ruling there is *fetch at
test time, pin by revision, vendor nothing*, and this is that ruling as
code.  What the repository keeps is `docs/c-torture-pin.json` — names and
HASHES, no source — which is not the corpus and is what makes a refetch
verifiable offline.

THE PIN IS TWO HASHES, and they answer different questions.

  git blob sha1  what GitHub says the file is AT THE REVISION.  Recomputed
                 locally as sha1("blob <len>\\0" + bytes), so the check does
                 not trust the transport or the host.
  sha256         what the bytes ARE, recorded by us.  A refetch that
                 matches this needs no network to be believed, and a host
                 that silently rewrote history cannot pass it.

A pin by revision alone would be a claim about a server's history.  A pin
by content is a claim about the bytes, and only the second survives the
server.

THE NEVER-VENDOR GUARD IS EXECUTED, NOT PROMISED.  The cache root is
refused if it resolves inside this repository, and the check is on the
RESOLVED path so that a symlink or a `..` cannot walk back in.
"""
import argparse, hashlib, json, os, subprocess, sys, urllib.request
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CENSUS = REPO / "docs" / "c23-suite-census.json"
PIN_OUT = REPO / "docs" / "c-torture-pin.json"
SUBDIR = "gcc/testsuite/gcc.c-torture/execute"


def die(msg, code=2):
    print("c_corpus_fetch: " + msg, file=sys.stderr)
    sys.exit(code)


def blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def default_cache() -> Path:
    return Path(os.environ.get("LS_C_CORPUS_CACHE",
                               Path(os.environ.get("TMPDIR", "/tmp")) / "ls-c-torture"))


def guard_outside_repo(cache: Path) -> Path:
    """The corpus is GPL: refuse to write it anywhere inside this tree.

    Checked on the RESOLVED path, so a symlink or a `..` cannot walk back
    in — the guard has to survive the thing that would defeat a textual
    comparison."""
    r = cache.resolve()
    if r == REPO or REPO in r.parents:
        die("cache %s is INSIDE the repository (%s). gcc.c-torture is GPL-3.0-or-later "
            "and docs/c23-goal.md §2 rules it NOT vendorable; the cache must live "
            "outside the tree. Set LS_C_CORPUS_CACHE." % (r, REPO))
    return r


def read_pin():
    c = json.loads(CENSUS.read_text())["corpora"]["gcc-torture-exec"]
    return c["slug"], c["rev"]


def api_listing(slug, rev):
    url = ("https://api.github.com/repos/%s/contents/%s?ref=%s&per_page=100"
           % (slug, SUBDIR, rev))
    req = urllib.request.Request(url, headers={"User-Agent": "lean-surfaces-c-lane"})
    with urllib.request.urlopen(req, timeout=120) as r:
        return json.load(r)


def fetch_one(slug, rev, name, dest):
    url = "https://raw.githubusercontent.com/%s/%s/%s/%s" % (slug, rev, SUBDIR, name)
    req = urllib.request.Request(url, headers={"User-Agent": "lean-surfaces-c-lane"})
    with urllib.request.urlopen(req, timeout=60) as r:
        data = r.read()
    dest.write_bytes(data)
    return data


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cache", default=None)
    ap.add_argument("--limit", type=int, default=300,
                    help="first N by name — the census's own sample rule (default 300)")
    ap.add_argument("--offline", action="store_true",
                    help="verify the cache against docs/c-torture-pin.json; no network")
    ap.add_argument("--manifest", default=None, help="write the run manifest here")
    ap.add_argument("--write-pin", action="store_true",
                    help="(re)write docs/c-torture-pin.json — hashes only, never source")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()

    if a.selftest:
        return selftest()

    slug, rev = read_pin()
    cache = guard_outside_repo(Path(a.cache) if a.cache else default_cache()) / rev
    src = cache / "src"
    env = cache / "env"
    src.mkdir(parents=True, exist_ok=True)
    env.mkdir(parents=True, exist_ok=True)

    if a.offline:
        if not PIN_OUT.exists():
            die("--offline needs %s, which does not exist yet" % PIN_OUT)
        pin = json.loads(PIN_OUT.read_text())
        names = [t["name"] for t in pin["tests"]]
        want = {t["name"]: t for t in pin["tests"]}
    else:
        listing = api_listing(slug, rev)
        if not isinstance(listing, list):
            die("GitHub contents API said: %s" % listing.get("message"))
        names = sorted(x["name"] for x in listing if x["name"].endswith(".c"))[:a.limit]
        want = {x["name"]: {"blob_sha1": x["sha"]} for x in listing}

    tests = []
    for n in names:
        f = src / n
        rec = {"name": n}
        if a.offline:
            if not f.exists():
                rec.update(status="absent", envelope=None, why="not in cache")
                tests.append(rec)
                continue
            data = f.read_bytes()
        else:
            data = f.read_bytes() if f.exists() else fetch_one(slug, rev, n, f)
        b, s = blob_sha1(data), hashlib.sha256(data).hexdigest()
        exp = want.get(n, {})
        if exp.get("blob_sha1") and exp["blob_sha1"] != b:
            die("%s: git blob sha MISMATCH at pin %s (want %s, got %s)"
                % (n, rev, exp["blob_sha1"], b))
        if exp.get("sha256") and exp["sha256"] != s:
            die("%s: sha256 MISMATCH against the committed pin (want %s, got %s)"
                % (n, exp["sha256"], s))
        rec.update(blob_sha1=b, sha256=s)
        out = env / (n[:-2] + ".json")
        r = subprocess.run([sys.executable, str(REPO / "extractors" / "c" / "extract.py"),
                            str(f), "--source-name", "%s/%s" % (SUBDIR, n),
                            "-o", str(out)], capture_output=True, text=True)
        if r.returncode == 0:
            rec.update(status="parsed", envelope=str(out), why="")
        else:
            first = next((l for l in r.stderr.splitlines() if ": error:" in l), "")
            rec.update(status="rejected", envelope=None,
                       why=(first.strip() or "clang rejected it under the pinned profile"))
        tests.append(rec)

    manifest = {"pin": {"slug": slug, "rev": rev, "subdir": SUBDIR},
                "cache": str(cache), "tests": tests}
    mpath = Path(a.manifest) if a.manifest else (cache / "manifest.json")
    mpath.write_text(json.dumps(manifest, indent=1) + "\n")

    if a.write_pin:
        # HASHES ONLY.  No source, no diagnostics text that could quote source.
        PIN_OUT.write_text(json.dumps(
            {"pin": manifest["pin"],
             "note": "hashes only — gcc.c-torture is GPL-3.0-or-later and is never vendored "
                     "(docs/c23-goal.md §2). These lines are a fingerprint, not the corpus.",
             "tests": [{"name": t["name"], "blob_sha1": t.get("blob_sha1"),
                        "sha256": t.get("sha256"), "status": t["status"]} for t in tests]},
            indent=1) + "\n")

    n_parsed = sum(1 for t in tests if t["status"] == "parsed")
    print("c_corpus_fetch: %d at pin %s  (%d parsed, %d rejected by the frontend)"
          % (len(tests), rev[:12], n_parsed, len(tests) - n_parsed))
    print("c_corpus_fetch: cache %s  manifest %s" % (cache, mpath))
    return 0


def selftest():
    ok = True

    def check(name, got, want):
        nonlocal ok
        good = got == want
        ok = ok and good
        print("  %-52s %s" % (name, "ok" if good else "FAIL got=%r want=%r" % (got, want)))

    check("blob_sha1 of empty", blob_sha1(b""),
          "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391")
    check("blob_sha1 of 'a\\n'", blob_sha1(b"a\n"),
          "78981922613b2afb6025042ff6bd878ac1994e85")
    # the guard is EXECUTED, both ways, and through a symlink-shaped path
    for bad in [REPO, REPO / "docs", REPO / "docs" / ".." / "harness"]:
        try:
            guard_outside_repo(Path(bad))
            check("guard refuses %s" % bad, "allowed", "refused")
        except SystemExit:
            check("guard refuses inside-repo path", "refused", "refused")
    try:
        guard_outside_repo(Path("/tmp/ls-c-torture-selftest"))
        check("guard allows an outside path", "allowed", "allowed")
    except SystemExit:
        check("guard allows an outside path", "refused", "allowed")
    print("c_corpus_fetch --selftest:", "ok" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
