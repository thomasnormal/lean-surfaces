#!/usr/bin/env python3
"""es_census.py — how big is ECMA-262, and how much of test262 is in reach?

The ECMAScript tier (`docs/es-charter.md`) is scored against test262, and its
Lean definitions are meant to stand one-per-abstract-operation against the
spec.  Before pricing any of that, this measures the two artifacts:

    python3 harness/es_census.py --spec <ecma262>/spec.html \
                                 --tests <test262> \
                                 --engine <engine262> \
                                 --acorn <dir>/node_modules/acorn/dist/acorn.mjs \
                                 -o docs/es262-census.json
    python3 harness/es_census.py --spec … --tests … --compare docs/es262-census.json
    python3 harness/es_census.py --self-test

Any of --spec / --tests / --engine may be given alone; --acorn adds the
frontend probe and needs --tests.  --spec takes ANY spec.html, so an edition
tag is censused by `git show es2026:spec.html > f && … --spec f`, which is
how docs/es-charter.md §1.4.1's edition delta was taken.

THE SPEC SIDE.  ECMA-262 is written in ecmarkup, an HTML dialect in which the
normative content is machine-tagged: `<emu-clause type="abstract operation">`
marks an abstract operation, `<emu-alg>` marks a numbered-step algorithm,
`<emu-grammar>` marks a grammar production.  So "how many definitions would a
one-Lean-definition-per-abstract-operation tier owe?" is a COUNT, not an
estimate, and this instrument takes it.

Steps are the spec's OWN numbering: `<emu-alg>` bodies are markdown ordered
lists (`1. Let _x_ be …`), NOT `<li>` elements.  A first version of this
instrument counted `<li>` and reported ZERO steps across 2,301 algorithms —
a plausible-looking table with nothing in it.  Zero steps is now a REFUSAL,
because a zero where a count belongs is an instrument fault.

THE TEST SIDE.  Every test262 file carries YAML frontmatter between the
tokens `/*---` and `---*/` (test262's own INTERPRETING.md is normative for
the keys).  The parser here is RESTRICTED: it understands exactly the shapes
the corpus uses and REFUSES loudly on anything else, naming the file and the
line.  A metadata guess would silently mis-bucket a test.

THE FRONTEND SIDE.  --acorn shells out to harness/es/acorn_probe.mjs, ONE
node process for the whole batch, exactly one row per job.  It measures the
ESTree node-type vocabulary over the language-core slice and checks the
parser's accept/reject verdict against test262's own
`negative: {phase: parse}` metadata.  Disagreements are reported by
DIRECTION: an over-reject is usually a feature-gated proposal, an
under-reject is an EARLY-ERROR obligation the parser does not carry.

THE JOIN.  A test's `esid` is a spec clause id.  So is every `#sec-…` anchor
engine262 writes in a JSDoc comment.  Joining both against the clause ids the
pinned spec actually defines measures two things no single corpus can: how
much of the suite is addressed at a clause that still exists, and how much of
the spec a working JS-hosted implementation of it has had to name.

REFUSAL PATHS (all three are exercised by --self-test):
  * a path that does not exist                       -> exit 2
  * a source that yields ZERO clauses or ZERO tests  -> exit 2
    (an empty census is an instrument fault, never a finding)
  * frontmatter the restricted parser cannot read    -> exit 2, file named

Python >= 3.9, stdlib only.  Deterministic: sorted output, byte-identical on
a double run.
"""

import argparse
import collections
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

SCHEMA = "es-census-0.1"

# ---------------------------------------------------------------------------
# THE EDITION PIN.  `docs/family-architecture.md` §1.1-§1.5: a tier names its
# edition with a TOKEN that is a valid Lean identifier and never renames, and
# every envelope carries it as `language_version`.  The token and the pinned
# REVISION of that edition's text are deliberately different strings — the
# token names the edition (ES2026), the revision names the bytes this tier
# extracts from (the `es2026-errata` tag).
#
# This constant is the fallback only.  The authority is `docs/es-edition.json`,
# written by --write-edition and verified by --edition, so the census, the
# extractor and the envelope all read ONE artifact and a spec from another
# edition REFUSES rather than being silently censused.
EDITION_TOKEN = "ES2026"

# ---------------------------------------------------------------------------
# The core slice, as the charter defines it.  Kept here so the number and the
# definition cannot drift apart: docs/es-charter.md quotes this table.
# ---------------------------------------------------------------------------

# Spec clauses 5-17 are the language: notational conventions, data types,
# abstract operations, syntax-directed operations, execution contexts,
# object behaviours, source text, the lexical grammar, expressions,
# statements, functions and classes, scripts and modules, error handling.
CORE_CLAUSE_IDS = [
    "sec-notational-conventions",
    "sec-ecmascript-data-types-and-values",
    "sec-abstract-operations",
    "sec-syntax-directed-operations",
    "sec-executable-code-and-execution-contexts",
    "sec-ordinary-and-exotic-objects-behaviours",
    "sec-ecmascript-language-source-code",
    "sec-ecmascript-language-lexical-grammar",
    "sec-ecmascript-language-expressions",
    "sec-ecmascript-language-statements-and-declarations",
    "sec-ecmascript-language-functions-and-classes",
    "sec-ecmascript-language-scripts-and-modules",
    "sec-error-handling-and-language-extensions",
]

# test262 top-level directories the core slice EXCLUDES, and why.
EXCLUDED_TEST_DIRS = {
    "annexB": "web-legacy, Annex B",
    "intl402": "ECMA-402, a different standard",
    "staging": "not yet promoted into the structured tree",
    "harness": "tests OF the harness, not of the language",
}

# Frontmatter flags that put a test outside the core slice.
OUT_OF_SLICE_FLAGS = {"module", "async", "CanBlockIsTrue", "CanBlockIsFalse"}

FRONTMATTER = re.compile(r"/\*---(.*?)---\*/", re.S)


def load_edition(path):
    d = json.loads(Path(path).read_text(encoding="utf-8"))
    for k in ("language_version", "spec_revision", "spec_sha256"):
        if k not in d:
            raise Refusal(f"{path}: edition pin is missing `{k}`")
    return d


def check_edition(pin, spec):
    """An envelope from another edition is a DIFFERENT PROGRAM.  Refuse."""
    if spec["sha256"] != pin["spec_sha256"]:
        raise Refusal(
            f"edition mismatch: the pin {pin['language_version']} "
            f"({pin['spec_revision']}) names spec sha256 {pin['spec_sha256'][:16]}…, "
            f"but --spec is {spec['sha256'][:16]}… — censusing a different edition "
            f"than the tier claims. Re-pin deliberately or pass the pinned spec.")


class Refusal(Exception):
    """A loud, fuel-independent stop.  Never a finding, always a fault."""


# ---------------------------------------------------------------------------
# The restricted frontmatter reader
# ---------------------------------------------------------------------------

def parse_frontmatter(text, where):
    """Read test262 YAML frontmatter.  Refuses rather than guesses.

    Understood shapes, and no others:
        key: scalar
        key: [a, b, c]
        key: |            (literal block, content indented)
        key: >            (folded block, content indented)
        key:              (nested mapping, `  sub: scalar` lines)
    """
    m = FRONTMATTER.search(text)
    if not m:
        return None
    body = m.group(1)
    lines = body.split("\n")
    # A block mapping's indentation is RELATIVE in YAML, and part of the corpus
    # indents the whole frontmatter by one space.  De-indent by the common
    # prefix rather than refusing a legal document — and count it, so the
    # normalization is a measured fact and not a silent one.
    indents = [len(l) - len(l.lstrip()) for l in lines if l.strip()]
    base = min(indents) if indents else 0
    dedented = base > 0
    if dedented:
        lines = [l[base:] if l.strip() else l for l in lines]
    out = {"_dedented": dedented} if dedented else {}
    i = 0
    while i < len(lines):
        raw = lines[i]
        i += 1
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        if raw[:1] in (" ", "\t"):
            raise Refusal(f"{where}: unattached indented line in frontmatter: {raw!r}")
        km = re.match(r"^([A-Za-z_][A-Za-z0-9_-]*):(.*)$", raw)
        if not km:
            raise Refusal(f"{where}: frontmatter line is not `key: value`: {raw!r}")
        key, rest = km.group(1), km.group(2).strip()
        if rest in ("|", ">", "|-", ">-", "|+", ">+"):
            block = []
            while i < len(lines) and (not lines[i].strip() or lines[i][:1] in (" ", "\t")):
                block.append(lines[i])
                i += 1
            out[key] = "\n".join(block)
        elif rest.startswith("["):
            if not rest.endswith("]"):
                raise Refusal(f"{where}: multi-line flow sequence not understood: {raw!r}")
            items = [x.strip() for x in rest[1:-1].split(",")]
            out[key] = [x for x in items if x]
        elif rest == "":
            sub = {}
            while i < len(lines) and (lines[i][:1] in (" ", "\t")) and lines[i].strip():
                sm = re.match(r"^\s+([A-Za-z_][A-Za-z0-9_-]*):\s*(.*)$", lines[i])
                dm = re.match(r"^\s+-\s*(.*)$", lines[i])
                if sm:
                    sub[sm.group(1)] = sm.group(2).strip()
                elif dm:
                    sub.setdefault("_seq", []).append(dm.group(1).strip())
                else:
                    raise Refusal(f"{where}: nested frontmatter line not understood: {lines[i]!r}")
                i += 1
            if "_seq" in sub and len(sub) == 1:
                out[key] = sub["_seq"]
            elif sub:
                out[key] = sub
            else:
                out[key] = ""
        else:
            out[key] = rest
    return out


# ---------------------------------------------------------------------------
# The spec census
# ---------------------------------------------------------------------------

CLAUSE_OPEN = re.compile(r"<(emu-clause|emu-annex|emu-intro)\b([^>]*)>")
CLAUSE_ANY = re.compile(r"<(/?)(emu-clause|emu-annex|emu-intro)\b[^>]*>")
ID_ATTR = re.compile(r'\bid="([^"]+)"')
TYPE_ATTR = re.compile(r'\btype="([^"]+)"')
H1 = re.compile(r"<h1>(.*?)</h1>", re.S)
ALG_BODY = re.compile(r"<emu-alg\b[^>]*>(.*?)</emu-alg>", re.S)
STEP = re.compile(r"^\s*\d+\. ", re.M)
# The spec's abrupt-completion shorthands: `? Foo(x)` propagates, `! Foo(x)`
# asserts the call cannot abruptly complete.  ES5 wrote ReturnIfAbrupt; the
# current text writes these, exclusively (measured: ReturnIfAbrupt is 0).
SHORTHAND_Q = re.compile(r"(?<![A-Za-z0-9_])\? [A-Z_]")
SHORTHAND_B = re.compile(r"(?<![A-Za-z0-9_])! [A-Z_]")


def count_steps(alg_body):
    return len(STEP.findall(alg_body))
TAGS = re.compile(r"<[^>]+>")


def census_spec(path):
    text = Path(path).read_text(encoding="utf-8")
    clause_ids = sorted(set(ID_ATTR.search(a).group(1)
                            for _, a in ((m.group(2), m.group(2)) for m in CLAUSE_OPEN.finditer(text))
                            if ID_ATTR.search(a)))
    if not clause_ids:
        raise Refusal(f"{path}: zero clauses attributed — an empty census is an instrument fault")

    def count(pat, hay=text):
        return len(re.findall(pat, hay))

    # Steps: the spec's OWN numbering.  emu-alg bodies are markdown ordered
    # lists (`1. Let _x_ be …`), NOT <li> elements — measured, after a first
    # version of this instrument counted <li> and reported zero steps in 2301
    # algorithms.  A zero where a count belongs is an instrument fault.
    steps = sum(count_steps(a) for a in ALG_BODY.findall(text))
    if steps == 0:
        raise Refusal(f"{path}: 2301 algorithms and zero steps — instrument fault")

    types = collections.Counter(
        TYPE_ATTR.search(m.group(2)).group(1)
        for m in CLAUSE_OPEN.finditer(text) if TYPE_ATTR.search(m.group(2))
    )

    # Top-level structure, with per-part counts.
    tops = []
    depth = 0
    for m in CLAUSE_ANY.finditer(text):
        closing, tag = m.group(1), m.group(2)
        if closing:
            depth -= 1
            continue
        if depth == 0:
            attrs = text[m.start():m.end()]
            idm = ID_ATTR.search(attrs)
            hm = H1.search(text, m.end(), m.end() + 800)
            title = TAGS.sub("", hm.group(1)).strip() if hm else ""
            tops.append({"id": idm.group(1) if idm else "", "tag": tag,
                         "title": re.sub(r"\s+", " ", title),
                         "_start": m.start()})
        depth += 1
    top_offsets = [(t["_start"], t["id"]) for t in tops]
    for i, t in enumerate(tops):
        end = tops[i + 1]["_start"] if i + 1 < len(tops) else len(text)
        seg = text[t.pop("_start"):end]
        t["clauses"] = len(re.findall(r"<emu-(?:clause|annex)\b", seg))
        t["algorithms"] = len(re.findall(r"<emu-alg\b", seg))
        t["grammar_blocks"] = len(re.findall(r"<emu-grammar\b", seg))
        t["bytes"] = end - (end - len(seg))
        t["bytes"] = len(seg)
        t["steps"] = sum(count_steps(a) for a in ALG_BODY.findall(seg))

    by_id = {t["id"]: t for t in tops}
    missing = [c for c in CORE_CLAUSE_IDS if c not in by_id]
    if missing:
        raise Refusal(f"{path}: core-slice clause ids absent from the spec: {missing}")
    core = {k: sum(by_id[c][k] for c in CORE_CLAUSE_IDS)
            for k in ("clauses", "algorithms", "steps", "grammar_blocks", "bytes")}
    annexb = by_id.get("sec-additional-ecmascript-features-for-web-browsers", {})

    # The two vocabularies whose ABSENCE and PRESENCE are the taxonomy finding.
    lowered = text.lower()
    vocab = {
        "undefined_behavior": lowered.count("undefined behavior") + lowered.count("undefined behaviour"),
        "implementation_defined": lowered.count("implementation-defined"),
        "implementation_approximated": lowered.count("implementation-approximated"),
        "implementation_dependent": lowered.count("implementation-dependent"),
        "host_defined": lowered.count("host-defined"),
        "host_hooks": lowered.count("host hook"),
        "normal_completion": lowered.count("normal completion"),
        "throw_completion": lowered.count("throw completion"),
        "abrupt_completion": lowered.count("abrupt completion"),
        "return_if_abrupt": text.count("ReturnIfAbrupt"),
        "shorthand_question": sum(len(SHORTHAND_Q.findall(a)) for a in ALG_BODY.findall(text)),
        "shorthand_bang": sum(len(SHORTHAND_B.findall(a)) for a in ALG_BODY.findall(text)),
        "assert_steps": sum(len(re.findall(r"^\s*\d+\. Assert:", a, re.M)) for a in ALG_BODY.findall(text)),
        "left_to_right": lowered.count("left-to-right") + lowered.count("left to right"),
        "unspecified": lowered.count("unspecified"),
        "in_any_order": lowered.count("in any order"),
    }

    # Where the latitude LIVES.  The taxonomy claim is only worth as much as
    # its location: 47 "implementation-approximated" mentions mean one thing
    # if they are spread through the language and another if they sit in one
    # clause.  Measured per top-level clause, and per NAMED operation.
    def owner(pos):
        last = ""
        for at, cid in top_offsets:
            if at <= pos:
                last = cid
            else:
                break
        return last

    latitude = {}
    for term in ("implementation-defined", "implementation-approximated", "host-defined"):
        c = collections.Counter(owner(m.start()) for m in re.finditer(term, text, re.I))
        latitude[term] = dict(sorted(c.items()))

    def named(ty):
        out = []
        for m in re.finditer(r'<emu-(?:clause|annex)\b[^>]*\btype="' + ty + r'"[^>]*>', text):
            hm = H1.search(text, m.end(), m.end() + 800)
            title = TAGS.sub("", hm.group(1)).strip() if hm else ""
            out.append(re.sub(r"\s+", " ", title).split("(")[0].strip() or
                       (ID_ATTR.search(m.group(0)).group(1) if ID_ATTR.search(m.group(0)) else "?"))
        return sorted(out)

    version = ""
    vm = re.search(r"^\s*title:\s*(.+)$", text[:20000], re.M)
    if vm:
        version = TAGS.sub("", vm.group(1)).replace("&reg;", "(R)").replace("&nbsp;", " ").strip()
    status = ""
    sm = re.search(r"^\s*status:\s*(.+)$", text[:20000], re.M)
    if sm:
        status = sm.group(1).strip()

    # TC39's own mechanization, measured rather than recalled: ESMeta
    # extracts an executable interpreter from this file, and the repository
    # gates pull requests on it.  A spec whose CI checks that its automatic
    # extractor can still read it is the premise this whole lane rests on,
    # so it is a row and not a sentence.
    root = Path(path).parent
    ignore = root / "esmeta-ignore.json"
    wf = root / ".github" / "workflows"
    esmeta = {
        "ignore_file_present": ignore.is_file(),
        "ignore_entries": (len(json.loads(ignore.read_text(encoding="utf-8")))
                           if ignore.is_file() else None),
        "workflows": sorted(w.name for w in wf.glob("esmeta*")) if wf.is_dir() else [],
    }

    return {
        "path_name": Path(path).name,
        "esmeta": esmeta,
        "sha256": hashlib.sha256(Path(path).read_bytes()).hexdigest(),
        "bytes": len(Path(path).read_bytes()),
        "lines": text.count("\n"),
        "title": version,
        "status": status,
        "clause_ids": len(clause_ids),
        "clauses": count(r"<emu-clause\b"),
        "annexes": count(r"<emu-annex\b"),
        "algorithms": count(r"<emu-alg\b"),
        "algorithm_steps": steps,
        "grammar_blocks": count(r"<emu-grammar\b"),
        "tables": count(r"<emu-table\b"),
        "notes": count(r"<emu-note\b"),
        "clause_types": dict(sorted(types.items())),
        "top_level": tops,
        "core_slice": core,
        "annexB": {k: annexb.get(k) for k in ("clauses", "algorithms", "steps")},
        "vocabulary": vocab,
        "latitude_by_clause": latitude,
        "host_defined_operations": named("host-defined abstract operation"),
        "implementation_defined_operations": named("implementation-defined abstract operation"),
        "_clause_id_set": clause_ids,
    }


# ---------------------------------------------------------------------------
# The test262 census
# ---------------------------------------------------------------------------

def census_tests(root, spec_clause_ids):
    root = Path(root)
    testdir = root / "test"
    if not testdir.is_dir():
        raise Refusal(f"{root}: no test/ directory — not a test262 checkout")
    files = sorted(testdir.rglob("*.js"))
    if not files:
        raise Refusal(f"{testdir}: zero .js files attributed — an instrument fault")

    by_top = collections.Counter()
    by_second = collections.Counter()
    flags = collections.Counter()
    features = collections.Counter()
    includes = collections.Counter()
    neg_phase = collections.Counter()
    neg_type = collections.Counter()
    keys = collections.Counter()
    fixtures = 0
    no_meta = 0
    dedented = 0
    esids = collections.Counter()
    esid_hits = 0
    esid_rows = 0
    # An esid that does not resolve is not one fact but four, and they retire
    # on completely different schedules — so they are never pooled.
    esid_miss = collections.Counter()          # bucket -> rows
    esid_miss_ids = collections.defaultdict(set)
    # The core slice, and the rung-0 subset inside it.
    slice_total = 0
    slice_no_includes = 0
    slice_parse_negative = 0
    slice_runtime_negative = 0
    slice_positive = 0
    slice_features = collections.Counter()
    slice_by_second = collections.Counter()
    parse_negative_all = 0
    builtins_total = 0
    builtins_no_includes = 0
    builtins_by_second = collections.Counter()
    module_total = 0

    spec_ids = set(spec_clause_ids) if spec_clause_ids else set()

    for p in files:
        rel = p.relative_to(testdir)
        parts = rel.parts
        top = parts[0]
        by_top[top] += 1
        by_second["/".join(parts[:2]) if len(parts) > 1 else top] += 1
        if "_FIXTURE" in p.name:
            fixtures += 1
            continue
        meta = parse_frontmatter(p.read_text(encoding="utf-8", errors="strict"), str(rel))
        if meta is None:
            no_meta += 1
            continue
        if meta.pop("_dedented", False):
            dedented += 1
        for k in meta:
            keys[k] += 1
        f = meta.get("flags") or []
        if isinstance(f, str):
            f = [f] if f else []
        for x in f:
            flags[x] += 1
        feats = meta.get("features") or []
        if isinstance(feats, str):
            feats = [feats] if feats else []
        for x in feats:
            features[x] += 1
        inc = meta.get("includes") or []
        if isinstance(inc, str):
            inc = [inc] if inc else []
        for x in inc:
            includes[x] += 1
        neg = meta.get("negative")
        phase = None
        if isinstance(neg, dict):
            phase = neg.get("phase", "")
            neg_phase[phase] += 1
            neg_type[neg.get("type", "")] += 1
        if phase == "parse":
            parse_negative_all += 1
        esid = meta.get("esid")
        if isinstance(esid, str) and esid:
            esid_rows += 1
            esids[esid] += 1
            if esid in spec_ids:
                esid_hits += 1
            elif esid == "pending":
                esid_miss["placeholder-pending"] += 1
            elif esid.startswith("prod-"):
                # ecmarkup mints `prod-` anchors for grammar PRODUCTIONS at
                # build time; they are real spec anchors of a different kind
                # and are absent from the source, not stale.
                esid_miss["grammar-production-anchor"] += 1
                esid_miss_ids["grammar-production-anchor"].add(esid)
            elif top in ("intl402", "staging"):
                esid_miss["outside-ecma262"] += 1
                esid_miss_ids["outside-ecma262"].add(esid)
            elif esid.startswith("sec-temporal") or esid.startswith("sec-get-temporal"):
                esid_miss["outside-ecma262"] += 1
                esid_miss_ids["outside-ecma262"].add(esid)
            else:
                # A `sec-` id the pinned spec does not define: the clause was
                # renamed by editorial restructuring, or the test is ahead of
                # the edition.  This is the citation-rot number.
                esid_miss["clause-id-absent"] += 1
                esid_miss_ids["clause-id-absent"].add(esid)

        # --- the slices.  `built-ins` is measured SEPARATELY rather than
        # folded in: it is the tier's libc-analogue, so pooling it with the
        # language core would hide the one split the charter has to price.
        if top in EXCLUDED_TEST_DIRS:
            continue
        if len(parts) > 1 and parts[1] in ("module-code", "import", "export"):
            module_total += 1
            continue
        if set(f) & OUT_OF_SLICE_FLAGS:
            continue
        if top == "built-ins":
            builtins_total += 1
            builtins_by_second["/".join(parts[:2]) if len(parts) > 1 else top] += 1
            if not inc:
                builtins_no_includes += 1
            continue
        slice_total += 1
        slice_by_second["/".join(parts[:2]) if len(parts) > 1 else top] += 1
        for x in feats:
            slice_features[x] += 1
        if not inc:
            slice_no_includes += 1
        if phase == "parse":
            slice_parse_negative += 1
        elif phase:
            slice_runtime_negative += 1
        else:
            slice_positive += 1

    harness_dir = root / "harness"
    harness = {}
    if harness_dir.is_dir():
        for h in sorted(harness_dir.glob("*.js")):
            harness[h.name] = h.read_text(encoding="utf-8", errors="replace").count("\n")

    return {
        "files": len(files),
        "fixtures": fixtures,
        "no_frontmatter": no_meta,
        "frontmatter_indented": dedented,
        "tests": len(files) - fixtures,
        "by_area": dict(sorted(by_top.items())),
        "by_second_level": dict(sorted(by_second.items())),
        "metadata_keys": dict(sorted(keys.items())),
        "flags": dict(sorted(flags.items())),
        "features_distinct": len(features),
        "features_top": dict(sorted(features.most_common(30))),
        "includes_distinct": len(includes),
        "includes": dict(sorted(includes.items())),
        "negative_phase": dict(sorted(neg_phase.items())),
        "negative_type": dict(sorted(neg_type.items())),
        "negative_parse_total": parse_negative_all,
        "esid_rows": esid_rows,
        "esid_distinct": len(esids),
        "esid_resolving_to_pinned_spec": esid_hits,
        "esid_unresolved_rows": dict(sorted(esid_miss.items())),
        "esid_unresolved_distinct": {k: len(v) for k, v in sorted(esid_miss_ids.items())},
        "harness_files": harness,
        "harness_total_lines": sum(harness.values()),
        "core_slice": {
            "definition": {
                "excluded_areas": dict(sorted(EXCLUDED_TEST_DIRS.items())),
                "excluded_flags": sorted(OUT_OF_SLICE_FLAGS),
                "excluded_subtrees": ["language/module-code", "language/import", "language/export"],
            "excluded_areas_note": "built-ins is counted separately, not excluded",
            },
            "tests": slice_total,
            "by_second_level": dict(sorted(slice_by_second.items())),
            "no_includes": slice_no_includes,
            "negative_parse": slice_parse_negative,
            "negative_runtime": slice_runtime_negative,
            "positive": slice_positive,
            "features_distinct": len(slice_features),
            "features_top": dict(sorted(slice_features.most_common(20))),
        },
        "built_ins_slice": {
            "tests": builtins_total,
            "no_includes": builtins_no_includes,
            "by_second_level": dict(sorted(builtins_by_second.items())),
        },
        "module_system_tests": module_total,
    }


# ---------------------------------------------------------------------------
# The frontend probe — does a stock ESTree parser cover the slice, and does
# its verdict agree with test262's own?
# ---------------------------------------------------------------------------

def census_frontend(tests_root, acorn_path, limit=0):
    """One node process for the whole batch.  Exactly one row per input path.

    Measures three things the charter cannot assert without running it:
      * the ESTree node-type VOCABULARY over the language-core slice — the
        number a `LeanModels/Es/Ast.lean` would have to carry;
      * whether the parser's accept/reject verdict AGREES with the suite's
        own `negative: {phase: parse}` metadata;
      * where it does not, which DIRECTION it fails in.  An under-reject is
        an EARLY-ERROR obligation the parser does not carry, and it is a
        static-semantics work item, not a parser bug.
    """
    tests_root = Path(tests_root)
    testdir = tests_root / "test"
    probe = Path(__file__).parent / "es" / "acorn_probe.mjs"
    if not probe.is_file():
        raise Refusal(f"{probe}: the frontend probe is missing")
    if not Path(acorn_path).is_file():
        raise Refusal(f"{acorn_path}: no acorn there — fetch it "
                      f"(`npm install acorn` in a scratch dir) and pass --acorn")

    rows = []           # (relpath, expects_parse_error)
    for p in sorted((testdir / "language").rglob("*.js")):
        if "_FIXTURE" in p.name:
            continue
        parts = p.relative_to(testdir).parts
        if len(parts) > 1 and parts[1] in ("module-code", "import", "export"):
            continue
        meta = parse_frontmatter(p.read_text(encoding="utf-8", errors="strict"), str(p))
        if meta is None:
            continue
        meta.pop("_dedented", None)
        f = meta.get("flags") or []
        if isinstance(f, str):
            f = [f] if f else []
        if set(f) & OUT_OF_SLICE_FLAGS:
            continue
        neg = meta.get("negative")
        feats = meta.get("features") or []
        if isinstance(feats, str):
            feats = [feats] if feats else []
        rows.append((p, isinstance(neg, dict) and neg.get("phase") == "parse", feats))
    if not rows:
        raise Refusal(f"{testdir}: zero slice files attributed — an instrument fault")
    if limit:
        rows = rows[:limit]

    stdin = "\n".join(str(p) for p, _, _ in rows) + "\n"
    proc = subprocess.run(["node", str(probe), str(acorn_path)],
                          input=stdin, capture_output=True, text=True)
    # "\n" only — never `splitlines()`, which also splits on U+2028/U+2029.
    # test262's line-terminator tests contain both; see extractors/es/extract.py.
    out = [l for l in proc.stdout.split("\n") if l.strip()]
    if proc.returncode == 3:
        raise Refusal(f"frontend probe refused: {out[0] if out else proc.stderr.strip()}")
    if len(out) != len(rows):
        raise Refusal(f"frontend probe returned {len(out)} rows for {len(rows)} inputs "
                      f"— the batch protocol requires exactly one row per job")

    vocab = collections.Counter()
    agree_pos = agree_neg = over_reject = under_reject = runner_err = 0
    over_reject_examples = []
    source_types = collections.Counter()
    errors = collections.Counter()
    over_by_feature = collections.Counter()
    under_by_feature = collections.Counter()
    under_by_dir = collections.Counter()
    for (p, expects_error, feats), line in zip(rows, out):
        r = json.loads(line)
        if "runner_error" in r:
            runner_err += 1
            continue
        if r.get("ok"):
            source_types[r.get("sourceType", "?")] += 1
            for k, v in r["types"].items():
                vocab[k] += v
            if expects_error:
                under_reject += 1
                for x in (feats or ["(untagged)"]):
                    under_by_feature[x] += 1
                under_by_dir["/".join(p.relative_to(testdir).parts[:3])] += 1
            else:
                agree_pos += 1
        else:
            errors[re.sub(r"\s*\(\d+:\d+\)\s*$", "", r.get("error", ""))] += 1
            if expects_error:
                agree_neg += 1
            else:
                over_reject += 1
                for x in (feats or ["(untagged)"]):
                    over_by_feature[x] += 1
                if len(over_reject_examples) < 12:
                    over_reject_examples.append(
                        {"path": str(p.relative_to(testdir)), "error": r.get("error", "")})

    return {
        "parser": "acorn",
        "attempted": len(rows),
        "parsed": agree_pos + under_reject,
        "rejected": agree_neg + over_reject,
        "runner_errors": runner_err,
        "source_type": dict(sorted(source_types.items())),
        "verdict_vs_metadata": {
            "agree_accept": agree_pos,
            "agree_reject": agree_neg,
            "over_reject": over_reject,
            "under_reject_early_errors": under_reject,
        },
        "over_reject_by_feature": dict(sorted(over_by_feature.items())),
        "under_reject_by_feature": dict(sorted(under_by_feature.items())),
        "under_reject_by_directory": dict(sorted(under_by_dir.items())),
        "over_reject_examples": over_reject_examples,
        "node_types_distinct": len(vocab),
        "node_types": dict(sorted(vocab.items())),
        "reject_reasons_top": dict(sorted(errors.most_common(15))),
    }


# ---------------------------------------------------------------------------
# The engine262 census — the JS-implements-the-spec precedent, measured
# ---------------------------------------------------------------------------

SEC_ANCHOR = re.compile(r"#(sec-[A-Za-z0-9._%-]*[A-Za-z0-9])")


def census_engine(root, spec_clause_ids):
    root = Path(root)
    src = root / "src"
    if not src.is_dir():
        raise Refusal(f"{root}: no src/ — not an engine262 checkout")
    files = sorted(p for p in src.rglob("*.mts"))
    if not files:
        raise Refusal(f"{src}: zero .mts files attributed — an instrument fault")
    lines = 0
    anchors = collections.Counter()
    by_dir = collections.Counter()
    for p in files:
        t = p.read_text(encoding="utf-8", errors="replace")
        lines += t.count("\n")
        by_dir[p.relative_to(src).parts[0] if len(p.relative_to(src).parts) > 1 else "."] += 1
        for a in SEC_ANCHOR.findall(t):
            anchors[a] += 1
    spec_ids = set(spec_clause_ids) if spec_clause_ids else set()
    named = sorted(anchors)
    resolving = [a for a in named if a in spec_ids]
    return {
        "files": len(files),
        "lines": lines,
        "files_by_dir": dict(sorted(by_dir.items())),
        "sec_anchors_distinct": len(named),
        "sec_anchors_resolving_to_pinned_spec": len(resolving),
        "sec_anchor_sites": sum(anchors.values()),
    }


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def rev(path):
    """The corpus revision, REFUSED rather than stamped empty.

    §5.4a — quote the number and the state, or quote neither.  The previous
    version returned `""` on any failure, and `docs/es262-census.json` records
    the result: `"sources": {"ecma262": "", "engine262": "c7939eaf…",
    "test262": "3655e746…"}`.  Two thirds provenanced and one third silently
    blank is the trap the law names — the artifact looks complete, and the
    empty string reads CLEANER than "this measurement has no recoverable
    state".

    A corpus whose revision cannot be recovered is an INPUT FAULT (§5.2), so
    it refuses.  To census a spec that is not in a checkout, put it in one —
    the edition pin in `docs/es-edition.json` carries the sha256, but the
    sha256 of a file is not the revision of the corpus it came from.
    """
    try:
        out = subprocess.run(["git", "-C", str(path), "log", "-1", "--format=%H %cI"],
                             capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError) as exc:
        raise Refusal(f"cannot run git in {path}: {exc} — the corpus revision is part "
                      f"of the result (§5.4a), so it is refused, not stamped empty")
    if out.returncode != 0 or not out.stdout.strip():
        raise Refusal(f"no git revision for {path} "
                      f"(exit {out.returncode}): {(out.stderr or '').strip()[:200]} — "
                      f"census a git CHECKOUT of the corpus; §5.4a forbids stamping this blank")
    return out.stdout.strip()


def self_test():
    """Run all three refusal paths.  A path that is only designed is not one."""
    ok = []
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        # 1. missing path
        try:
            census_spec(d / "nope.html")
            print("SELF-TEST FAIL: a missing spec did not refuse")
            return 1
        except (Refusal, OSError):
            ok.append("missing-path refuses")
        # 2. zero attribution
        (d / "empty.html").write_text("<html><body>no clauses here</body></html>")
        try:
            census_spec(d / "empty.html")
            print("SELF-TEST FAIL: a zero-clause spec did not refuse")
            return 1
        except Refusal:
            ok.append("zero-attribution refuses")
        # 3. unreadable frontmatter
        try:
            parse_frontmatter("/*---\nflags: [a,\n  b]\n---*/\n", "fixture.js")
            print("SELF-TEST FAIL: a multi-line flow sequence did not refuse")
            return 1
        except Refusal:
            ok.append("unparseable frontmatter refuses")
        # and the positive control: the shapes the corpus really uses
        m = parse_frontmatter(
            "/*---\ndescription: |\n  two\n  lines\nesid: sec-foo\n"
            "flags: [onlyStrict, generated]\nfeatures: [a, b]\n"
            "negative:\n  phase: parse\n  type: SyntaxError\n---*/\n", "fixture.js")
        assert m["esid"] == "sec-foo", m
        assert m["flags"] == ["onlyStrict", "generated"], m
        assert m["negative"] == {"phase": "parse", "type": "SyntaxError"}, m
        assert m["description"].splitlines() == ["  two", "  lines"], m
        ok.append("the corpus's own shapes parse")

        # 4. the EDITION pin.  A pin that cannot refuse is decoration.
        (d / "pin.json").write_text(json.dumps({
            "language_version": "ES2026", "spec_revision": "es2026-errata",
            "spec_sha256": "0" * 64}))
        pin = load_edition(d / "pin.json")
        try:
            check_edition(pin, {"sha256": "f" * 64})
            print("SELF-TEST FAIL: an edition mismatch did not refuse")
            return 1
        except Refusal:
            ok.append("edition mismatch refuses")
        check_edition(pin, {"sha256": "0" * 64})          # the matching case passes
        ok.append("the matching edition passes")
        (d / "bad.json").write_text(json.dumps({"language_version": "ES2026"}))
        try:
            load_edition(d / "bad.json")
            print("SELF-TEST FAIL: an incomplete pin did not refuse")
            return 1
        except Refusal:
            ok.append("an incomplete edition pin refuses")

    for line in ok:
        print("  ok:", line)
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--spec", help="path to ecma262 spec.html")
    ap.add_argument("--tests", help="path to a test262 checkout")
    ap.add_argument("--engine", help="path to an engine262 checkout")
    ap.add_argument("--acorn", help="path to a fetched acorn ESM entry point; "
                                    "enables the frontend probe over --tests")
    ap.add_argument("--frontend-limit", type=int, default=0,
                    help="probe only the first N slice files (a smoke, not a census)")
    ap.add_argument("-o", "--out", help="write JSON here")
    ap.add_argument("--compare", help="compare against a previous JSON; nonzero on drift")
    ap.add_argument("--self-test", action="store_true", help="run the refusal paths")
    ap.add_argument("--check-schema", metavar="MD",
                    help="assert docs/es-envelope-schema.md's node table is DERIVED from "
                         "this census: every kind listed, nothing extra, every count exact")
    ap.add_argument("--edition", help="path to docs/es-edition.json; verifies --spec "
                                      "is the pinned edition and stamps language_version")
    ap.add_argument("--write-edition", metavar="OUT",
                    help="write the edition pin for --spec (needs --edition-token/--edition-revision)")
    ap.add_argument("--edition-token", help="the registry's edition token, e.g. ES2026")
    ap.add_argument("--edition-revision", help="the pinned revision of that edition's text, e.g. es2026-errata")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not (args.spec or args.tests or args.engine):
        ap.error("nothing to census: pass --spec and/or --tests and/or --engine")

    result = {"schema": SCHEMA, "sources": {}}
    clause_ids = []
    try:
        if args.spec:
            spec = census_spec(args.spec)
            clause_ids = spec.pop("_clause_id_set")
            result["spec"] = spec
            result["sources"]["ecma262"] = rev(Path(args.spec).parent)
            if args.write_edition:
                if not (args.edition_token and args.edition_revision):
                    ap.error("--write-edition needs --edition-token and --edition-revision")
                if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", args.edition_token):
                    raise Refusal(f"edition token {args.edition_token!r} is not a valid Lean "
                                  f"identifier — family-architecture.md §1.1 law 1")
                pin = {
                    "language": "ecmascript",
                    "language_version": args.edition_token,
                    "spec_revision": args.edition_revision,
                    "spec_sha256": spec["sha256"],
                    "spec_bytes": spec["bytes"],
                    "spec_title": spec["title"],
                    "clauses": spec["clauses"] + spec["annexes"],
                    "algorithms": spec["algorithms"],
                    "algorithm_steps": spec["algorithm_steps"],
                    "core_slice": spec["core_slice"],
                }
                Path(args.write_edition).write_text(
                    json.dumps(pin, indent=2, sort_keys=True) + "\n", encoding="utf-8")
                print(f"wrote {args.write_edition}: {args.edition_token} "
                      f"({args.edition_revision}), sha256 {spec['sha256'][:16]}…")
            if args.edition:
                pin = load_edition(args.edition)
                check_edition(pin, spec)
                result["language_version"] = pin["language_version"]
                result["spec_revision"] = pin["spec_revision"]
        elif args.edition or args.write_edition:
            ap.error("--edition/--write-edition need --spec")
        if args.tests:
            result["test262"] = census_tests(args.tests, clause_ids)
            result["sources"]["test262"] = rev(args.tests)
        if args.engine:
            result["engine262"] = census_engine(args.engine, clause_ids)
            result["sources"]["engine262"] = rev(args.engine)
        if args.acorn:
            if not args.tests:
                ap.error("--acorn needs --tests")
            result["frontend"] = census_frontend(args.tests, args.acorn, args.frontend_limit)
    except Refusal as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2

    if args.check_schema:
        # "What the ingester accepts" and "what the corpus contains" must not
        # be able to drift apart.  The C lane states this as a property; here
        # it is a CHECK, because a table of 66 rows is exactly the size where
        # a hand edit goes unnoticed.
        if "frontend" not in result:
            print("REFUSED: --check-schema needs the frontend census "
                  "(pass --tests and --acorn)", file=sys.stderr)
            return 2
        doc = Path(args.check_schema).read_text(encoding="utf-8")
        listed = dict((m.group(1), int(m.group(2)))
                      for m in re.finditer(r"`([A-Z][A-Za-z]+)` (\d+)", doc))
        actual = result["frontend"]["node_types"]
        missing = sorted(set(actual) - set(listed))
        extra = sorted(set(listed) - set(actual))
        wrong = sorted((k, listed[k], actual[k]) for k in set(listed) & set(actual)
                       if listed[k] != actual[k])
        if missing or extra or wrong:
            print(f"REFUSED: {args.check_schema} has DRIFTED from the census",
                  file=sys.stderr)
            for k in missing:
                print(f"  missing from the doc: {k} ({actual[k]})", file=sys.stderr)
            for k in extra:
                print(f"  in the doc but not the corpus: {k}", file=sys.stderr)
            for k, d_, a_ in wrong:
                print(f"  count differs: {k} doc={d_} census={a_}", file=sys.stderr)
            return 1
        # ...and the EXTRACTOR's own constant, so census, schema document and
        # ingester cannot drift apart in any pair.
        ex = Path(__file__).resolve().parent.parent / "extractors" / "es" / "extract.py"
        if ex.is_file():
            src = ex.read_text(encoding="utf-8")
            m = re.search(r"VOCABULARY = frozenset\(\{(.*?)\}\)", src, re.S)
            if not m:
                print(f"REFUSED: {ex}: no VOCABULARY frozenset to check", file=sys.stderr)
                return 1
            vocab = set(re.findall(r'"([A-Za-z]+)"', m.group(1)))
            if vocab != set(actual):
                print(f"REFUSED: {ex} has DRIFTED from the census", file=sys.stderr)
                for k in sorted(set(actual) - vocab):
                    print(f"  missing from the extractor: {k}", file=sys.stderr)
                for k in sorted(vocab - set(actual)):
                    print(f"  in the extractor but not the corpus: {k}", file=sys.stderr)
                return 1
            print(f"{ex.name}: VOCABULARY matches the census ({len(vocab)} kinds)")
        print(f"{args.check_schema}: {len(actual)} node kinds, all listed, "
              f"all counts exact")
        if not (args.out or args.compare):
            return 0

    blob = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.compare:
        old = Path(args.compare).read_text(encoding="utf-8")
        if old == blob:
            print(f"{args.compare}: unchanged")
            return 0
        print(f"{args.compare}: DRIFT — re-run with -o to update", file=sys.stderr)
        a, b = json.loads(old), result
        for k in sorted(set(a) | set(b)):
            if a.get(k) != b.get(k):
                print(f"  section differs: {k}", file=sys.stderr)
        return 1
    if args.out:
        Path(args.out).write_text(blob, encoding="utf-8")
        print(f"wrote {args.out}")
    else:
        sys.stdout.write(blob)
    return 0


if __name__ == "__main__":
    sys.exit(main())
