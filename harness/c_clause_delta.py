#!/usr/bin/env python3
"""clause_delta.py — measure the C17 -> C23 delta at CLAUSE granularity.

Inputs are PDF-to-text extractions of the two public working drafts:
    N2310  ISO/IEC 9899:2017 draft (carries change bars rendered as ':' runs)
    N3220  ISO/IEC 9899:2024 draft

The question: how much of the normative surface is textually unchanged?
That decides whether a second Lean edition surface should be a full copy,
a base+delta layering, or version-parameterized definitions.

MATCHING RULE. Clauses are matched by their ANCESTOR-TITLE PATH, not by
number: C23 renumbered 6.5 and 6.8 wholesale (C17's `6.5.7 Bitwise shift
operators` is C23's `6.5.8 Bitwise shift operators`), so number-matching
measures the renumbering and not the change. The path is
(top-level clause number, parent titles..., own title); top-level numbers
1..7 and annexes A..M are stable across the two editions.

IDENTITY. Two different PDF renderings never produce byte-identical text,
so this instrument reports BOTH exact identity and a similarity ratio, and
treats ratio >= 0.995 as "identical modulo extraction noise". Exact-equal
is reported separately and is a floor, not the headline.

Refusal paths, all loud: a missing input; a document that yields zero body
clauses (an instrument fault, never a finding); an implausible clause count.

Output: JSON on --out, sorted, deterministic. No ISO text beyond TITLES.
"""
import argparse
import difflib
import json
import re
import sys
from pathlib import Path

HEADING = re.compile(r"^[ \t]*((?:[0-9]+|[A-M])(?:\.[0-9]+){1,4})[ \t]+([A-Za-z][^\n]{0,90})$")

NOISE_PAT = [
    r"©?\s*ISO(?:/IEC)?\b.*",              # running headers, both editions
    r"N\d{4}\b.*",                          # N2310 / N3220 banners
    r"\d{1,4}",                             # bare page numbers
    r"§\s*[0-9A-M.]+",                      # section stamps
    r".{0,40}§\s*[0-9A-M.]+\s*",            # "Portability issues — 588  § J.2"
    r"(?:Language|Library|Portability issues|Environment)\s*[—–-]?\s*\d*",
    r"\(en\)\s*[—–-]?.*",
    r"[\s—–:.]*",                           # rules, dashes, leftover punctuation
]
NOISE = re.compile(r"^\s*(?:" + "|".join(NOISE_PAT) + r")\s*$")
DIFFMARK = re.compile(r"[:∶]{3,}")
WS = re.compile(r"\s+")
FF = "\x0c"

NEAR_IDENTICAL = 0.995


def load(path):
    p = Path(path)
    if not p.is_file():
        sys.exit(f"clause_delta: no such file: {path}")
    return p.read_text(encoding="utf-8", errors="replace").replace(FF, "\n").splitlines()


def find_headings(lines):
    out = []
    for i, ln in enumerate(lines):
        m = HEADING.match(ln)
        if not m:
            continue
        num, title = m.group(1), m.group(2).strip()
        if re.search(r"(?:\.\s?){4,}\s*\d+\s*$", title) or re.search(r"\s{3,}\d{1,4}$", title):
            continue  # table-of-contents row (dotted leader / trailing page number)
        out.append((i, num, title))
    return out


def body_clauses(lines):
    """Body occurrences only.

    DEDUP RULE: keep the LAST occurrence of a number whose following 40 lines
    contain a paragraph-shaped line (>= 40 chars, not itself a heading). ToC
    rows are followed by more ToC rows and never qualify.
    """
    chosen = {}
    for idx, num, title in find_headings(lines):
        window = lines[idx + 1: idx + 41]
        if any(len(w.strip()) >= 40 and not HEADING.match(w) for w in window):
            chosen[num] = (idx, title)
    return chosen


def normalize(chunk):
    kept = []
    for ln in chunk:
        ln = DIFFMARK.sub(" ", ln)
        if NOISE.match(ln):
            continue
        kept.append(ln)
    return WS.sub(" ", " ".join(kept)).strip()


def bodies(lines, chosen):
    all_head_idx = sorted(i for i, _n, _t in find_headings(lines))
    out = {}
    for num, (idx, title) in chosen.items():
        nxt = next((h for h in all_head_idx if h > idx), len(lines))
        out[num] = (title, normalize(lines[idx + 1: nxt]))
    return out


def tkey(t):
    return WS.sub(" ", t.lower()).strip().rstrip(".")


def path_of(num, table):
    """(top-level number, parent titles..., own title) — stable under renumbering."""
    parts = num.split(".")
    chain = [parts[0]]
    for k in range(2, len(parts) + 1):
        anc = ".".join(parts[:k])
        chain.append(tkey(table[anc][0]) if anc in table else anc)
    return tuple(chain)


def top_level(num):
    return num.split(".")[0]


SUBTREES = {
    "5.1.2.3 program execution (sequencing)": ["5.1.2.3"],
    "6.2.1-6.2.4 scope / linkage / storage duration": ["6.2.1", "6.2.2", "6.2.3", "6.2.4"],
    "6.2.5 types": ["6.2.5"],
    "6.3 conversions": ["6.3"],
    "6.5 expressions and operators": ["6.5"],
    "6.6 constant expressions": ["6.6"],
    "6.7 declarations": ["6.7"],
    "6.8 statements": ["6.8"],
    "6.10 preprocessing directives": ["6.10"],
    "J.2 undefined behavior": ["J.2"],
    "J.3 implementation-defined behavior": ["J.3"],
}


def in_subtree(num, prefixes):
    return any(num == p or num.startswith(p + ".") for p in prefixes)


THIN = 200  # a body this short is a heading with no prose of its own


def _row(a, b, na, nb, how):
    xa, xb = a[na][1], b[nb][1]
    exact = xa == xb
    ratio = 1.0 if exact else round(difflib.SequenceMatcher(None, xa, xb).ratio(), 4)
    thin = len(xa) < THIN or len(xb) < THIN
    return {
        "status": "identical" if ratio >= NEAR_IDENTICAL else "changed",
        "exact": exact, "c17": na, "c23": nb, "renumbered": na != nb,
        "matched_by": how, "thin": thin,
        "title": b[nb][0], "ratio": ratio,
        "len_c17": len(xa), "len_c23": len(xb),
    }


def classify(a, b):
    """a, b: num -> (title, text). Rows keyed by the C17 number when the clause
    exists there, otherwise `+<C23 number>`.

    Two matching passes. (1) ANCESTOR-TITLE PATH — the primary rule, stable
    under the C23 renumbering. (2) RESCUE by (top-level number, own title), for
    clauses whose PARENT was retitled: C23 retitled several clause-7 parents,
    which breaks the path of children that did not themselves change.
    """
    pa = {path_of(n, a): n for n in a}
    pb = {path_of(n, b): n for n in b}
    rows = {}
    used_b = set()

    for p, na in sorted(pa.items()):
        nb = pb.get(p)
        if nb is not None:
            rows[na] = _row(a, b, na, nb, "path")
            used_b.add(nb)

    left_a = sorted(n for n in a if n not in rows)
    left_b = sorted(n for n in b if n not in used_b)
    by_title = {}
    for n in left_b:
        by_title.setdefault((top_level(n), tkey(b[n][0])), []).append(n)
    for na in left_a:
        cands = by_title.get((top_level(na), tkey(a[na][0])))
        if cands:
            nb = cands.pop(0)
            rows[na] = _row(a, b, na, nb, "title-rescue")
            used_b.add(nb)
        else:
            rows[na] = {"status": "removed", "c17": na, "c23": None, "matched_by": None,
                        "title": a[na][0], "ratio": None, "thin": len(a[na][1]) < THIN,
                        "len_c17": len(a[na][1]), "len_c23": None}
    for nb in sorted(n for n in b if n not in used_b):
        rows[f"+{nb}"] = {"status": "added", "c17": None, "c23": nb, "matched_by": None,
                          "title": b[nb][0], "ratio": None, "thin": len(b[nb][1]) < THIN,
                          "len_c17": None, "len_c23": len(b[nb][1])}
    return rows


def tally(rows, pred=lambda r: True):
    """Ratio statistics EXCLUDE `thin` rows — a clause whose body is a heading
    over subclauses has no prose to compare, and scoring it would be noise."""
    t = {"identical": 0, "changed": 0, "added": 0, "removed": 0}
    exact = renum = thin = 0
    for r in rows.values():
        if not pred(r):
            continue
        t[r["status"]] += 1
        exact += 1 if r.get("exact") else 0
        renum += 1 if r.get("renumbered") else 0
        thin += 1 if r.get("thin") else 0
    t["total"] = sum(t[k] for k in ("identical", "changed", "added", "removed"))
    t["exact_text_equal"] = exact
    t["renumbered"] = renum
    t["thin"] = thin
    subst = [r for r in rows.values()
             if pred(r) and r["status"] in ("identical", "changed") and not r["thin"]]
    ident = sum(1 for r in subst if r["status"] == "identical")
    t["matched_substantive"] = len(subst)
    t["identical_substantive"] = ident
    t["pct_identical_of_matched"] = round(100.0 * ident / len(subst), 1) if subst else None
    ch = [r["ratio"] for r in subst if r["status"] == "changed"]
    t["mean_ratio_of_changed"] = round(sum(ch) / len(ch), 4) if ch else None
    return t


def which(rows, num_field, prefixes=None, top=None):
    def pred(r):
        n = r[num_field] or r["c23"] or r["c17"]
        if n is None:
            return False
        if prefixes is not None:
            return in_subtree(n, prefixes)
        return top_level(n) == top
    return pred


def j2_items(lines, chosen):
    """The enumerated UB bullets. C17 renders them as em-dash bullets; C23
    NUMBERED them, `(1)`, `(2)`, ... — itself a C23 change."""
    if "J.2" not in chosen:
        return None
    idx = chosen["J.2"][0]
    all_head_idx = sorted(i for i, _n, _t in find_headings(lines))
    nxt = next((h for h in all_head_idx if h > idx), len(lines))
    kept = [DIFFMARK.sub(" ", ln) for ln in lines[idx + 1:nxt]
            if not NOISE.match(DIFFMARK.sub(" ", ln))]
    text = "\n".join(kept)
    parts = re.split(r"\n\s*\(\d+\)\s+", text)
    if len(parts) < 20:
        parts = re.split(r"\n\s*[—–-]\s+", text)
    items = parts[1:]
    return [WS.sub(" ", it).strip() for it in items]


FURNITURE = re.compile(
    r"(?:©\s*ISO[^.]*|§\s*[0-9A-M.]+|ISO/IEC\s*9899[^\s]*|N\d{4}\b|"
    r"All rights reserved|working draft|Portability issues)", re.I)


def norm_item(s):
    """Compare UB bullets modulo (a) mid-line page furniture that survives the
    per-line filter once lines are joined, and (b) the trailing clause citation,
    which moved with the renumbering: '... (6.5.7).' -> '...'."""
    s = FURNITURE.sub(" ", s)
    s = re.sub(r"\(\s*[0-9A-M][0-9A-M.,;:\s]*\)\s*[.—–-]*\s*$", "", s.strip())
    return WS.sub(" ", s.lower()).strip().rstrip(".").strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("c17")
    ap.add_argument("c23")
    ap.add_argument("-o", "--out", required=True)
    args = ap.parse_args()

    la, lb = load(args.c17), load(args.c23)
    ca, cb = body_clauses(la), body_clauses(lb)
    for name, c in (("C17", ca), ("C23", cb)):
        if not c:
            sys.exit(f"clause_delta: {name} yielded ZERO body clauses — instrument fault, not a finding")
        if len(c) < 200:
            sys.exit(f"clause_delta: {name} yielded only {len(c)} body clauses — implausible, refusing")

    a, b = bodies(la, ca), bodies(lb, cb)
    rows = classify(a, b)

    out = {
        "instrument": "clause_delta.py",
        "inputs": {"c17": Path(args.c17).name, "c23": Path(args.c23).name},
        "near_identical_threshold": NEAR_IDENTICAL,
        "body_clauses": {"c17": len(a), "c23": len(b)},
        "headline": tally(rows),
        "by_top_level": {},
        "by_subtree": {},
        "ratio_buckets": {},
        "most_changed": [],
        "rows": rows,
    }
    tops = sorted({top_level(r["c17"] or r["c23"]) for r in rows.values()})
    out["by_top_level"] = {t: tally(rows, which(rows, "c17", top=t)) for t in tops}
    out["by_subtree"] = {k: tally(rows, which(rows, "c23", prefixes=p))
                         for k, p in sorted(SUBTREES.items())}

    buckets = {">=0.995 (identical)": 0, "0.95-0.995": 0, "0.80-0.95": 0, "<0.80": 0}
    for r in rows.values():
        x = r["ratio"]
        if x is None:
            continue
        if x >= 0.995:
            buckets[">=0.995 (identical)"] += 1
        elif x >= 0.95:
            buckets["0.95-0.995"] += 1
        elif x >= 0.80:
            buckets["0.80-0.95"] += 1
        else:
            buckets["<0.80"] += 1
    out["ratio_buckets"] = buckets

    changed = sorted(((r["ratio"], r["c23"] or r["c17"], r["title"])
                      for r in rows.values()
                      if r["status"] == "changed" and not r["thin"]))
    out["most_changed"] = [{"clause": n, "title": t, "ratio": x} for x, n, t in changed[:30]]
    out["added_list"] = sorted((r["c23"], r["title"]) for r in rows.values()
                               if r["status"] == "added" and not r["thin"])
    out["removed_list"] = sorted((r["c17"], r["title"]) for r in rows.values() if r["status"] == "removed")
    out["renumbered_list"] = sorted((r["c17"], r["c23"], r["title"])
                                    for r in rows.values() if r.get("renumbered"))

    ia, ib = j2_items(la, ca), j2_items(lb, cb)
    if ia and ib:
        sa = {norm_item(x) for x in ia}
        sb = {norm_item(x) for x in ib}
        out["j2"] = {"c17_items": len(ia), "c23_items": len(ib),
                     "identical_modulo_citation": len(sa & sb),
                     "only_c17": len(sa - sb), "only_c23": len(sb - sa),
                     "only_c23_sample": sorted(sb - sa)[:10]}
    else:
        out["j2"] = {"error": "J.2 not located or not parseable in one or both documents"}

    Path(args.out).write_text(json.dumps(out, indent=2, sort_keys=True, default=str) + "\n")
    print(f"body clauses: C17 {len(a)}  C23 {len(b)}")
    print("headline:", json.dumps(out["headline"]))
    print("buckets:", json.dumps(buckets))
    print("J.2:", json.dumps({k: v for k, v in out["j2"].items() if k != "only_c23_sample"}))
    for k, v in out["by_subtree"].items():
        print(f"  {k:48s} total={v['total']:4d} ident={v['identical']:4d} "
              f"chg={v['changed']:4d} add={v['added']:3d} rm={v['removed']:3d} "
              f"pct={v['pct_identical_of_matched']}")


if __name__ == "__main__":
    main()
