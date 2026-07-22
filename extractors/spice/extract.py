#!/usr/bin/env python3
"""SPICE netlist -> standardized AST envelope extractor for the lean_models
spice lane (M0 tier, see docs/spice-design-m0.md).

Usage (run from the repo root):

    python3 extractors/spice/extract.py <file.cir> [more.cir ...]

For each source file ``foo.cir`` this writes ``foo.json`` next to the
source (final extension replaced, matching the Python lane's tri.py ->
tri.json convention): the envelope described in
docs/spice-envelope-schema.md (schema "spice-0.1").

Guarantees:
  * Never fails on valid SPICE -- anything outside the M0 card vocabulary
    becomes an ``Unsupported`` card (tag + source text, <= 200 chars).
  * Deterministic: same input bytes => same output bytes. json indent=2,
    ASCII, one trailing newline; fixed key order: "kind" first, then
    "span", then the card's fields in the order documented in
    docs/spice-envelope-schema.md.
  * All numeric values are EXACT rationals ({"num": int, "den": int},
    lowest terms, den > 0): decimals and SPICE scale suffixes are parsed
    without ever touching floating point (1k = 1000, 1m = 1/1000,
    2.2meg = 2200000, 470u = 47/100000, 1.5 = 3/2).
  * Hard errors (non-zero exit, no output): unreadable file / not UTF-8.

Pure python3 stdlib (no third-party frontend: SPICE decks are line-based
cards and the M0 grammar is regular).
"""

import argparse
import hashlib
import json
import os
import re
import sys
from fractions import Fraction

SCHEMA_VERSION = "spice-0.1"
FRONTEND = {"name": "spice-extract", "version": "0.1"}

UNSUPPORTED_TEXT_LIMIT = 200


class ExtractError(Exception):
    """Fatal extractor error (message to stderr, exit code 1)."""


# ---------------------------------------------------------------------------
# Exact value parsing (SPICE numbers with scale suffixes -> Fraction)
# ---------------------------------------------------------------------------

# mantissa (decimal), optional exponent, optional trailing letters
# (scale suffix and/or units -- "1kohm", "5V", "2.2meg").
_VALUE_RE = re.compile(
    r"^([+-]?)(\d+\.\d*|\.\d+|\d+)(?:[eE]([+-]?\d+))?([a-zA-Z]*)$"
)

# SPICE scale suffixes (case-INSENSITIVE; note MEG is mega but M is milli).
# Multi-letter suffixes must be matched before their one-letter prefixes.
_SUFFIXES = [
    ("meg", Fraction(10) ** 6),
    ("mil", Fraction(254, 10) * Fraction(1, 10**6)),  # 25.4e-6, exact
    ("t", Fraction(10) ** 12),
    ("g", Fraction(10) ** 9),
    ("k", Fraction(10) ** 3),
    ("m", Fraction(1, 10**3)),
    ("u", Fraction(1, 10**6)),
    ("n", Fraction(1, 10**9)),
    ("p", Fraction(1, 10**12)),
    ("f", Fraction(1, 10**15)),
]


def parse_value(tok):
    """Parse a SPICE numeric token to an exact Fraction, or None if the
    token is not a number.  Decimal mantissa and exponent are exact
    (never via float); a scale suffix multiplies; any remaining letters
    after the suffix are units and are ignored ("1kohm", "5V")."""
    m = _VALUE_RE.match(tok)
    if m is None:
        return None
    sign, mant, exp, trailer = m.groups()
    if mant.startswith("."):
        mant = "0" + mant
    if mant.endswith("."):
        mant = mant + "0"
    val = Fraction(mant)  # exact decimal ("2.2" -> 11/5)
    if exp is not None:
        val *= Fraction(10) ** int(exp)
    t = trailer.lower()
    for suf, scale in _SUFFIXES:
        if t.startswith(suf):
            val *= scale
            break
    if sign == "-":
        val = -val
    return val


def value_json(frac):
    """{"num": int, "den": int} -- lowest terms, den > 0 (Fraction
    normalizes both)."""
    return {"num": frac.numerator, "den": frac.denominator}


# ---------------------------------------------------------------------------
# Logical-line assembly (title line, comments, continuations, .end)
# ---------------------------------------------------------------------------

def _strip_inline_comment(line):
    """Cut ';' end-of-line comments anywhere and '$' comments preceded by
    whitespace (or at line start), per ngspice."""
    cut = len(line)
    i = line.find(";")
    if i != -1:
        cut = min(cut, i)
    m = re.search(r"(^|\s)\$", line)
    if m is not None:
        cut = min(cut, m.start() if m.group(1) == "" else m.start() + 1)
    return line[:cut]


def logical_cards(text):
    """Split source text into (title, cards); each card is a dict
    {"text", "line", "end_line", "tokens"} with 1-based inclusive line
    span covering continuations.  The FIRST line of a SPICE deck is
    always the title (never a card).  '*' lines are comments, '+' lines
    continue the previous card, '.end' stops parsing."""
    lines = text.split("\n")
    title = lines[0].rstrip("\r").strip() if lines else ""
    cards = []
    open_card = None  # card still accepting '+' continuations

    def close():
        nonlocal open_card
        if open_card is not None:
            open_card["tokens"] = open_card["text"].split()
            cards.append(open_card)
            open_card = None

    for lineno, raw in enumerate(lines[1:], start=2):
        line = _strip_inline_comment(raw.rstrip("\r"))
        stripped = line.strip()
        if stripped == "" or stripped.startswith("*"):
            continue
        if stripped.startswith("+"):
            cont = stripped[1:].strip()
            if open_card is None:
                cards.append({
                    "text": stripped, "line": lineno, "end_line": lineno,
                    "tokens": None, "stray_continuation": True,
                })
            else:
                open_card["text"] += " " + cont
                open_card["end_line"] = lineno
            continue
        close()
        first = stripped.split(None, 1)[0].lower()
        if first == ".end":
            return title, cards
        open_card = {"text": stripped, "line": lineno, "end_line": lineno,
                     "tokens": None}
    close()
    return title, cards


# ---------------------------------------------------------------------------
# Card -> JSON node
# ---------------------------------------------------------------------------

def span_of(card, end_card=None):
    end = (end_card or card)["end_line"]
    return {"line": card["line"], "end_line": end}


def unsupported(card, tag, end_card=None, text=None):
    if text is None:
        text = card["text"]
    return {
        "kind": "Unsupported",
        "span": span_of(card, end_card),
        "spice_kind": tag,
        "text": text[:UNSUPPORTED_TEXT_LIMIT],
    }


# Two-terminal element cards: first letter -> (kind, whether a bare 'dc'
# keyword may precede the value).
_ELEMENTS = {"r": "R", "c": "C", "l": "L", "v": "V", "i": "I"}
_SOURCES = ("V", "I")


def element_node(card):
    toks = [t.lower() for t in card["tokens"]]
    kind = _ELEMENTS[toks[0][0]]
    body = toks[1:]
    if kind in _SOURCES and len(body) == 4 and body[2] == "dc":
        body = body[:2] + body[3:]
    if len(body) != 3:
        return unsupported(card, kind + ":form")
    val = parse_value(body[2])
    if val is None:
        return unsupported(card, kind + ":value")
    return {
        "kind": kind,
        "span": span_of(card),
        "name": toks[0],
        "nodes": [body[0], body[1]],
        "value": value_json(val),
    }


def instance_node(card):
    toks = [t.lower() for t in card["tokens"]]
    if len(toks) < 3 or any("=" in t for t in toks):
        return unsupported(card, "X:form")
    return {
        "kind": "X",
        "span": span_of(card),
        "name": toks[0],
        "subckt": toks[-1],
        "connections": toks[1:-1],
    }


def parse_cards(cards):
    """Build (subckts, top_cards).  Top-level .subckt definitions go to
    `subckts`; nested definitions stay as Subckt nodes inside the parent
    body (M0 flatten rejects them -- see the design doc)."""
    subckts = []
    top = []
    # each frame: {"node": Subckt-node-in-progress, "card": header card,
    #              "bad": tag or None (whole definition demoted)}
    stack = []

    def emit(node):
        if stack:
            stack[-1]["node"]["body"].append(node)
        else:
            top.append(node)

    def emit_def(frame, end_card):
        node = frame["node"]
        node["span"] = span_of(frame["card"], end_card)
        if frame["bad"] is not None:
            node = unsupported(frame["card"], frame["bad"], end_card)
        target = subckts if not stack else stack[-1]["node"]["body"]
        target.append(node)

    for card in cards:
        if card.get("stray_continuation"):
            emit(unsupported(card, "Continuation:stray"))
            continue
        toks = card["tokens"]
        first = toks[0].lower()
        c0 = first[0]
        if c0 == ".":
            if first == ".subckt":
                low = [t.lower() for t in toks]
                bad = None
                if len(low) < 2:
                    bad = "Subckt:form"
                elif any("=" in t or t == "params:" for t in low[1:]):
                    bad = "Subckt:params"
                name = low[1] if len(low) >= 2 else ""
                stack.append({
                    "node": {"kind": "Subckt", "span": None, "name": name,
                             "ports": low[2:], "body": []},
                    "card": card,
                    "bad": bad,
                })
            elif first == ".ends":
                if not stack:
                    emit(unsupported(card, "Ends:stray"))
                    continue
                frame = stack.pop()
                low = [t.lower() for t in toks]
                if len(low) > 1 and low[1] != frame["node"]["name"]:
                    frame["bad"] = frame["bad"] or "Subckt:ends-mismatch"
                emit_def(frame, card)
            elif first == ".op":
                if len(toks) == 1:
                    emit({"kind": "Op", "span": span_of(card)})
                else:
                    emit(unsupported(card, "Op:form"))
            else:
                emit(unsupported(card, first))
        elif c0 in _ELEMENTS:
            emit(element_node(card))
        elif c0 == "x":
            emit(instance_node(card))
        else:
            emit(unsupported(card, c0.upper()))

    while stack:  # unterminated .subckt at EOF / .end
        frame = stack.pop()
        frame["bad"] = frame["bad"] or "Subckt:unterminated"
        last = frame["node"]["body"][-1] if frame["node"]["body"] else None
        end_line = last["span"]["end_line"] if last else frame["card"]["end_line"]
        emit_def(frame, {"end_line": end_line})
    return subckts, top


# ---------------------------------------------------------------------------
# Envelope
# ---------------------------------------------------------------------------

def extract_source(text, source_file, source_bytes):
    title, cards = logical_cards(text)
    subckts, top = parse_cards(cards)
    return {
        "schema_version": SCHEMA_VERSION,
        "language": "spice",
        "frontend": dict(FRONTEND),
        "source_file": source_file.replace(os.sep, "/"),
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "netlist": {
            "kind": "Netlist",
            "title": title,
            "subckts": subckts,
            "cards": top,
        },
        "lean_blocks": [],
    }


def extract_file(path):
    try:
        with open(path, "rb") as f:
            source_bytes = f.read()
    except OSError as e:
        raise ExtractError("cannot read {}: {}".format(path, e))
    try:
        text = source_bytes.decode("utf-8")
    except UnicodeDecodeError as e:
        raise ExtractError("{} is not UTF-8: {}".format(path, e))
    return extract_source(text, path, source_bytes)


def output_path(src):
    return os.path.splitext(src)[0] + ".json"


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="SPICE -> AST envelope (schema {})".format(SCHEMA_VERSION))
    ap.add_argument("sources", nargs="+", metavar="file.cir")
    args = ap.parse_args(argv)
    status = 0
    for src in args.sources:
        try:
            env = extract_file(src)
        except ExtractError as e:
            print("extract.py: error: {}".format(e), file=sys.stderr)
            status = 1
            continue
        out = output_path(src)
        with open(out, "w", encoding="ascii") as f:
            json.dump(env, f, indent=2)
            f.write("\n")
        print("{} -> {}".format(src, out))
    return status


if __name__ == "__main__":
    sys.exit(main())
