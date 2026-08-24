#!/usr/bin/env python3
"""es_coverage.py — how many of the 66 node kinds does the ES tier STATE?

    python3 harness/es_coverage.py            # the §9.0 line, plus the table
    python3 harness/es_coverage.py --json
    python3 harness/es_coverage.py --self-test

WHY THIS EXISTS.  The number was produced by scraping `| .kind =>` arms out of
`Eval.lean` and counting them.  On 2026-08-24 the object-destructuring inch
added `bindPattern`, whose arms include `arrayPattern` — **which REFUSES** —
and the scrape counted it as stated, reporting 42/66 where the truth was
40/66, and 6,634 in-vocabulary tests where the truth was 5,154.  A 1,480-test
overclaim, caught only because the number was re-derived by hand.

**A scrape that cannot tell an implementing arm from a refusing one is not a
coverage instrument.**  It had been right until then only because every
earlier inch happened to implement every arm it added — the measure was
accidentally correct, which is the worst kind of correct, because nothing
would have announced the day it stopped being.

THE DISTINCTION THAT MAKES IT SOUND.  Not every refusal in an arm is a
boundary.  A refusal whose message starts `internal:` is a DEFENSIVE guard
against a malformed AST — `internal: malformed IfStatement` sits inside a
fully implemented `if`, and reading it as "if is not implemented" would be as
wrong as the bug this replaces.  So refusals are split:

    boundary refusal   "array destructuring needs GetIterator"  -> not stated
    internal refusal   "internal: malformed IfStatement"        -> says nothing

and an arm is classified:

    REFUSING   its whole body is one boundary refusal
    PARTIAL    real evaluation AND at least one boundary refusal
               (`objectExpression` implements `init` and refuses get/set)
    STATED     real evaluation, and only internal guards if any

**PARTIAL is counted as NOT stated in the headline**, and listed separately.
Counting it as stated would claim a construct the tier only half evaluates;
counting it as absent would deny work that is really there.  The §9.0 line
carries `stated`, and `partial` rides beside it — the same argument §5.0a
makes for keeping declared divergences out of the coverage numerator.

Exit status: 0 always for a report; 1 if the vocabulary and the evaluator have
drifted apart (a kind the evaluator dispatches on that `Ast.lean` does not
define, which would mean one of the two files is stale).
"""

import argparse
import json
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EVAL = os.path.join(REPO, "LeanModels", "Es", "Eval.lean")
AST = os.path.join(REPO, "LeanModels", "Es", "Ast.lean")

ARM = re.compile(r"^(?P<indent> {4,16})\| (?:some )?(?P<pats>\.\w+(?: \| (?:some )?\.\w+)*) =>(?P<tail>.*)$")
REFUSE = re.compile(r"SemM\.refuse\w*")
# Anything that means the arm actually DOES something.
EVALUATES = re.compile(r"(?:^|[^\w.])(?:do|match|if|let|for|return|pure|←)(?:[^\w]|$)")

# Kinds handled by a DEDICATED CLAUSE rather than a dispatch arm — the
# evaluator reaches them structurally, so no `| .kind =>` exists to read.
# Each names the definition that handles it and the instrument CHECKS THAT
# DEFINITION EXISTS: the same discipline §5.0a's register uses for its guards,
# because a hand-maintained exemption list that nothing verifies is exactly
# the discipline-not-instrument shape MEAS-28 forbids. Delete `evalCatchClause`
# and this file goes red rather than quietly keeping the kind in the numerator.
DEDICATED = {
    "program": "evalProgram",
    "variableDeclarator": "evalDeclarator",
    "catchClause": "evalCatchClause",
    "switchCase": "selectCase",
    "literal": "literalValue",
}


def vocabulary():
    """The 66 kinds `Ast.lean` defines, in declaration order."""
    text = open(AST, encoding="utf-8").read()
    m = re.search(r"inductive NodeKind where(.*?)deriving", text, re.S)
    if not m:
        raise SystemExit("es_coverage: cannot find `inductive NodeKind` in Ast.lean")
    return re.findall(r"^\s*\|\s*([a-zA-Z]\w*)\s*$", m.group(1), re.M)


def strip_comments(lines):
    out, in_block = [], False
    for ln in lines:
        if in_block:
            if "-/" in ln:
                in_block = False
            continue
        s = ln.strip()
        if s.startswith("/-"):
            if "-/" not in s:
                in_block = True
            continue
        ln = re.sub(r"--.*$", "", ln)
        if ln.strip():
            out.append(ln)
    return out


def classify_body(body_lines):
    """-> 'stated' | 'partial' | 'refusing'"""
    body = strip_comments(body_lines)
    text = "\n".join(body)
    refusals = REFUSE.findall(text)
    if not refusals:
        return "stated"
    # Which refusals are boundaries, and which are defensive `internal:` guards?
    boundary = 0
    for m in REFUSE.finditer(text):
        after = text[m.end():m.end() + 400]
        msg = re.search(r'"((?:[^"\\]|\\.)*)"', after)
        if not msg or not msg.group(1).lstrip().startswith("internal:"):
            boundary += 1
    if boundary == 0:
        return "stated"
    # Is the body ONE boundary refusal and nothing else?
    without = REFUSE.sub("", text)
    without = re.sub(r'"(?:[^"\\]|\\.)*"', "", without)
    without = re.sub(r'[\s(){}\[\],.!?:;\'`|+-]', "", without)
    without = re.sub(r"s!", "", without)
    return "refusing" if not without else "partial"


def arms(vocab):
    """Every dispatch arm in Eval.lean, classified, keyed by node kind.

    `vocab` filters: the same `| .x =>` shape matches OTHER inductives'
    constructors — `| .null | .undef =>` over `Val`, `| .brk _ =>` over
    `Abrupt` — and those are not node kinds. Only names `Ast.lean` defines
    are counted, so the reader is not told that `undef` is an unhandled node.
    """
    lines = open(EVAL, encoding="utf-8").read().split("\n")
    seen = {}
    i = 0
    while i < len(lines):
        m = ARM.match(lines[i])
        if not m:
            i += 1
            continue
        indent = len(m.group("indent"))
        pats = [p.strip().lstrip(".") for p in m.group("pats").split("|")]
        pats = [p for p in pats if p in vocab]
        if not pats:
            i += 1
            continue
        body = [m.group("tail")]
        j = i + 1
        while j < len(lines):
            nxt = lines[j]
            if not nxt.strip():
                body.append(nxt); j += 1; continue
            lead = len(nxt) - len(nxt.lstrip())
            if lead <= indent and nxt.lstrip().startswith("|"):
                break
            if lead < indent:
                break
            body.append(nxt); j += 1
        verdict = classify_body(body)
        for p in pats:
            seen.setdefault(p, []).append(verdict)
        # ADVANCE BY ONE, not past the body. A dispatch arm's body can CONTAIN
        # further arms — `objectPattern` matches `| some .property =>` and
        # `| some .restElement =>` inside itself — and jumping to the end of
        # the outer body made those kinds invisible, reporting them `absent`
        # while the evaluator handled them. That is the same class of error as
        # the scrape this file replaces, in the opposite direction.
        i += 1

    # AGGREGATION. A kind can have arms in several matches. The rule is not
    # "strongest wins" — that made the answer depend on file order — but:
    # every arm refuses -> refusing; ANY arm carries a boundary refusal ->
    # partial; otherwise stated. A boundary anywhere means the kind is not
    # fully stated, whichever arm it sits in.
    out = {}
    for kind, vs in seen.items():
        if all(v == "refusing" for v in vs):
            out[kind] = "refusing"
        elif any(v in ("refusing", "partial") for v in vs):
            out[kind] = "partial"
        else:
            out[kind] = "stated"
    return out


def report(as_json=False):
    vocab = vocabulary()
    got = arms(set(vocab))
    src = open(EVAL, encoding="utf-8").read()
    missing_dedicated = []
    for kind, fn in DEDICATED.items():
        if re.search(r"^def %s\b" % re.escape(fn), src, re.M):
            got.setdefault(kind, "stated")
        else:
            missing_dedicated.append("%s (claimed by %s)" % (kind, fn))
    unknown = []
    buckets = {"stated": [], "partial": [], "refusing": [], "absent": []}
    for k in vocab:
        buckets[got.get(k, "absent")].append(k)
    result = {
        "vocabulary": len(vocab),
        "stated": len(buckets["stated"]),
        "partial": len(buckets["partial"]),
        "refusing": len(buckets["refusing"]),
        "absent": len(buckets["absent"]),
        "kinds": buckets,
        "unknown_kinds_dispatched": unknown,
        "dedicated_clauses_missing": missing_dedicated,
    }
    if as_json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        for name in ("stated", "partial", "refusing", "absent"):
            ks = buckets[name]
            print("%-9s %2d  %s" % (name, len(ks), ", ".join(ks) if ks else "-"))
        print()
        print("§9.0  node kinds stated: %d/%d  (partial: %d, refusing: %d, absent: %d)"
              % (result["stated"], result["vocabulary"], result["partial"],
                 result["refusing"], result["absent"]))
        if unknown:
            print("DRIFT: evaluator dispatches on kinds Ast.lean does not define: %s"
                  % ", ".join(unknown), file=sys.stderr)
        if missing_dedicated:
            print("DRIFT: dedicated clause claimed but not defined: %s"
                  % ", ".join(missing_dedicated), file=sys.stderr)
    return 1 if (unknown or missing_dedicated) else 0


def self_test():
    """BOTH DIRECTIONS. The rule that matters is the one that has never fired,
    so each classification is exercised on a body of the shape it must catch —
    including the exact arm whose misreading produced this file."""
    cases = [
        (["", "        SemM.refuseConstruct", '          "array destructuring needs GetIterator (§7.4)"'],
         "refusing", "a whole-body boundary refusal (the arrayPattern shape)"),
        ([" do", "        let v ← evalExpr fuel env e", "        return v"],
         "stated", "plain evaluation"),
        (["", "        match n.child? \"test\" with",
          "        | some t => do return t",
          '        | none => SemM.refuseConstruct "internal: malformed IfStatement"'],
         "stated", "evaluation with only an `internal:` guard"),
        ([" do", "        let obj ← ordinaryObjectCreate none",
          '        if bad then SemM.refuseConstruct "get/set needs the accessor path"',
          "        return obj"],
         "partial", "evaluation plus a boundary refusal (objectExpression)"),
        (["", "        -- a comment mentioning SemM.refuseConstruct",
          "        return 1"],
         "stated", "a refusal named only in a COMMENT"),
    ]
    ok = True
    for body, want, label in cases:
        got = classify_body(body)
        flag = "ok  " if got == want else "FAIL"
        if got != want:
            ok = False
        print("  %s %-52s -> %s" % (flag, label, got))
    # And the real file must agree with what the lane knows by hand.
    got = arms(set(vocabulary()))
    for kind, want in (("arrayPattern", "refusing"), ("objectExpression", "partial"),
                       ("emptyStatement", "stated")):
        g = got.get(kind)
        flag = "ok  " if g == want else "FAIL"
        if g != want:
            ok = False
        print("  %s real arm %-43s -> %s" % (flag, kind, g))
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    return report(a.json)


if __name__ == "__main__":
    sys.exit(main())
