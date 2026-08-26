#!/usr/bin/env python3
"""Analog-tier assurance census: the standing §9.0 number and its denominator.

WHAT THIS MEASURES, and why the obvious number would mislead.

`LeanModels/Circuit/Assurance.lean` bundles three obligations -- `safe`,
`realizable`, `withinDomain` -- over one circuit, behavior and allowed-world
predicate.  All three are universally quantified over `allowed world`.  So an
`allowed` predicate that NO world satisfies discharges all three at once, and
`#assurance_report` prints exactly the lines it prints for a real result.
`RealizableUnder` was introduced to stop a safety theorem resting on an empty
BEHAVIOR set; it cannot stop one resting on an empty WORLD set, because it is
itself guarded by `allowed world`.

Non-vacuity is a chain of two links.  This instrument counts the outer one.

A case is GROUNDED here when the tree carries a `GroundedUnder <allowed>`
proof for that case's own allowed-world predicate -- a witness that the
premise set is inhabited.  Only a grounded case is one that could have
DISAGREED, which is the denominator rule of family-architecture.md §9.0(a).

DIRECTION OF THE ERROR, and it is the opposite of §9.0's syntactic guard.
There the syntactic measure was an UPPER bound on coverage; this one is a
LOWER bound on non-vacuity.  A case can be grounded semantically without
carrying the canonical spelling -- `dram_bank_256x32` is, via
`dram_bank_256x32_nominal_profile : DramBankCoreNominalProfile
dramBank256x32Profile`, which inhabits `DramBankCoreReadAllowed` for every
world.  So NO-GROUNDING-WITNESS means "this instrument cannot see a witness",
NEVER "this case is vacuous".  Retiring a flag is done by writing the
canonical witness, which is also what makes the fact mechanically checkable.

Two further degeneracies are reported but NOT counted as failures, because
they are design choices the lane may have made deliberately:

  TRIVIAL-DOMAIN  the validity domain is `fun _ _ _ => True`, so the
                  `withinDomain` obligation carries no information;
  SPEC-EQ-DOMAIN  the specification and the domain are the same expression,
                  so `safe` and `withinDomain` are one proposition and the
                  "safety" claim is a well-posedness claim restated.

Method is SYNTACTIC (regex over the declaration headers), which is an upper
bound on what is actually proved -- §9.0's syntactic-upper-bound guard.  A
syntactic win is never banked as a semantic one: this instrument reports
counts of DECLARATIONS, and the triad is what says they compile.

Usage:
    python3 harness/spice/assurance_census.py [--json] [--min-grounded N]

Exit codes: 0 ok, 1 floor violated (with --min-grounded), 3 instrument error.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

REPO = pathlib.Path(__file__).resolve().parents[2]
SPICE_EXAMPLES = REPO / "Examples" / "spice"


def retarget(root: pathlib.Path) -> None:
    """Point the instrument at another checkout, so a baseline can be taken."""
    global REPO, SPICE_EXAMPLES
    REPO = root.resolve()
    SPICE_EXAMPLES = REPO / "Examples" / "spice"

# `theorem <name> :\n? ... AssuranceCase` -- capture the declaration name and
# the statement body up to the `:=` that opens the proof.
ASSURANCE_DECL = re.compile(
    r"^theorem\s+([A-Za-z_][A-Za-z0-9_.']*)\s*:\s*\n?"
    r"(?P<body>.*?)(?=\s*:=\s)",
    re.MULTILINE | re.DOTALL,
)
GROUNDED_DECL = re.compile(
    r"^theorem\s+([A-Za-z_][A-Za-z0-9_.']*)\s*:\s*\n?\s*GroundedUnder\s+"
    r"(?P<allowed>.*?)(?=\s*:=\s)",
    re.MULTILINE | re.DOTALL,
)
EXHIBITS_DECL = re.compile(
    r"^theorem\s+([A-Za-z_][A-Za-z0-9_.']*)\s*:\s*\n?\s*ExhibitsUnder\b",
    re.MULTILINE,
)
# THE NON-VACUITY IDIOMS, enumerated because counting only one of them is how
# the "9 / 21" figure happened.  A guarantee is non-vacuous when the tree shows
# its premise set is inhabited -- and this corpus does that FIVE different ways.
# Recognising only `_realizable` would mark `chain` and the gate decks empty.
NONVACUITY_IDIOMS = (
    # 1. the house twin: a `..._realizable` companion to a universal theorem
    ("realizable-twin", re.compile(r"^theorem\s+\S*_realizable", re.M)),
    # 2. an exhibited observation for every input vector (and_gate, half_adder)
    ("observation-exists", re.compile(r"^theorem\s+\S*_observation_exists", re.M)),
    # 3. this lane's own two-link chain (analog-1, analog-8)
    ("grounded-witness", re.compile(r"GroundedUnder|^theorem\s+\S*_grounded", re.M)),
    # 4. the existential form an empty premise set would refute
    ("exhibits", re.compile(r"ExhibitsUnder|^theorem\s+\S*_exhibits", re.M)),
    # 5. an IFF whose reverse direction constructs the witness (chain), or a
    #    computed operating point the DC solver actually found
    ("iff-or-computed-op", re.compile(r"↔|#circuit_check\s+\S+\s+dc\s+shows", re.M)),
)


def nonvacuity_idioms(text: str) -> list[str]:
    """Which non-vacuity idioms this circuit uses. Empty list = nothing shows
    the guarantee's premise set is inhabited."""
    return [name for name, pattern in NONVACUITY_IDIOMS if pattern.search(text)]


TRIVIAL_PROP = re.compile(r"^\(?\s*fun(\s+[A-Za-z_][A-Za-z0-9_']*)+\s*=>\s*True\s*\)?$")


def normalise(text: str) -> str:
    """Collapse whitespace so multi-line Lean terms compare as one token."""
    return re.sub(r"\s+", " ", text).strip()


def split_arguments(body: str) -> list[str]:
    """Split an `AssuranceCase a b c ...` application into its arguments.

    Bracket-aware so that `(fun _ _ _ => True)` stays one argument.  Returns
    the arguments AFTER the `AssuranceCase` head token.
    """
    head = body.index("AssuranceCase") + len("AssuranceCase")
    rest = body[head:]
    arguments: list[str] = []
    depth = 0
    current: list[str] = []
    for character in rest:
        if character in "([{":
            depth += 1
            current.append(character)
        elif character in ")]}":
            depth -= 1
            current.append(character)
        elif depth == 0 and character.isspace():
            if current:
                arguments.append("".join(current))
                current = []
        else:
            current.append(character)
    if current:
        arguments.append("".join(current))
    return [normalise(argument) for argument in arguments if argument.strip()]


def allowed_key(text: str) -> str:
    """Canonical key for an allowed-world predicate.

    Two spellings denote the same predicate and must match: a namespace-
    qualified name (`Examples.spice.ac_lowpass.proof.CutoffAllowed`) and its
    unqualified form under an `open` (`CutoffAllowed`); and a lambda with or
    without a binder type ascription (`fun _world : Unit => True` versus
    `fun _world => True`).  Canonicalising is what lets the instrument see
    that a `GroundedUnder` proof discharges a given case.
    """
    text = strip_outer_parens(normalise(text))
    # Drop binder type ascriptions inside a `fun ... => ...` head.
    if text.startswith("fun "):
        head, separator, tail = text.partition("=>")
        if separator:
            head = re.sub(r":\s*[^,\s]+", "", head)
            text = f"{normalise(head)} => {normalise(tail)}"
    # Reduce every dotted name to its final component.
    return " ".join(token.split(".")[-1] for token in text.split())


def strip_outer_parens(text: str) -> str:
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        for index, character in enumerate(text):
            if character == "(":
                depth += 1
            elif character == ")":
                depth -= 1
                if depth == 0 and index != len(text) - 1:
                    return text
        text = text[1:-1].strip()
    return text


def census_directory(directory: pathlib.Path) -> dict:
    cases: list[dict] = []
    grounded_allowed: set[str] = set()
    exhibits: list[str] = []

    for source in sorted(directory.glob("*.lean")):
        text = source.read_text(encoding="utf-8")

        for match in GROUNDED_DECL.finditer(text):
            grounded_allowed.add(allowed_key(match.group("allowed")))
        for match in EXHIBITS_DECL.finditer(text):
            exhibits.append(match.group(1))

        for match in ASSURANCE_DECL.finditer(text):
            body = match.group("body")
            if "AssuranceCase" not in body:
                continue
            arguments = split_arguments(body)
            # circuit, behavior, allowed, source, specification, domain
            if len(arguments) < 6:
                cases.append(
                    {
                        "theorem": match.group(1),
                        "file": str(source.relative_to(REPO)),
                        "malformed": True,
                        "arguments": arguments,
                    }
                )
                continue
            circuit, behavior, allowed, _source, specification, domain = arguments[:6]
            cases.append(
                {
                    "theorem": match.group(1),
                    "file": str(source.relative_to(REPO)),
                    "malformed": False,
                    "circuit": circuit,
                    "behavior": behavior,
                    "allowed": strip_outer_parens(allowed),
                    "specification": strip_outer_parens(specification),
                    "domain": strip_outer_parens(domain),
                }
            )

    for case in cases:
        if case["malformed"]:
            case["grounded"] = False
            case["flags"] = ["MALFORMED"]
            continue
        flags: list[str] = []
        case["grounded"] = allowed_key(case["allowed"]) in grounded_allowed
        if not case["grounded"]:
            flags.append("NO-GROUNDING-WITNESS")
        if TRIVIAL_PROP.match(case["domain"]):
            flags.append("TRIVIAL-DOMAIN")
        if TRIVIAL_PROP.match(case["specification"]):
            flags.append("TRIVIAL-SPEC")
        if case["specification"] == case["domain"]:
            flags.append("SPEC-EQ-DOMAIN")
        case["flags"] = flags

    corpus = "\n".join(
        source.read_text(encoding="utf-8") for source in sorted(directory.glob("*.lean")))
    return {
        "idioms": nonvacuity_idioms(corpus),
        "has_lean": bool(list(directory.glob("*.lean"))),
        "circuit": directory.name,
        "cases": cases,
        "exhibits": exhibits,
        "has_netlist": bool(list(directory.glob("*.cir"))),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument(
        "--repo",
        type=pathlib.Path,
        default=None,
        help="measure another checkout (for taking a pre-change baseline)",
    )
    parser.add_argument(
        "--min-grounded",
        type=int,
        default=None,
        help="fail if fewer than N assurance cases are grounded (ratchet floor)",
    )
    options = parser.parse_args()
    if options.repo is not None:
        retarget(options.repo)

    if not SPICE_EXAMPLES.is_dir():
        print(f"assurance_census: no such directory: {SPICE_EXAMPLES}", file=sys.stderr)
        return 3

    directories = sorted(entry for entry in SPICE_EXAMPLES.iterdir() if entry.is_dir())
    rows = [census_directory(directory) for directory in directories]

    total_circuits = len(rows)
    with_case = [row for row in rows if row["cases"]]
    all_cases = [case for row in rows for case in row["cases"]]
    grounded_cases = [case for case in all_cases if case["grounded"]]
    grounded_circuits = [
        row for row in with_case if all(case["grounded"] for case in row["cases"])
    ]

    if options.json:
        print(
            json.dumps(
                {
                    "circuits_total": total_circuits,
                    "circuits_with_assurance_case": len(with_case),
                    "circuits_fully_grounded": len(grounded_circuits),
                    "assurance_cases_total": len(all_cases),
                    "assurance_cases_grounded": len(grounded_cases),
                    "rows": rows,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    print("Analog tier -- assurance census (syntactic; the triad says they compile)")
    print()
    width = max(len(row["circuit"]) for row in rows)
    print(f"{'circuit'.ljust(width)}  cases  grounded  flags")
    print(f"{'-' * width}  -----  --------  -----")
    for row in rows:
        if not row["cases"]:
            print(f"{row['circuit'].ljust(width)}      0         -  no AssuranceCase")
            continue
        grounded = sum(1 for case in row["cases"] if case["grounded"])
        flags = sorted({flag for case in row["cases"] for flag in case["flags"]})
        print(
            f"{row['circuit'].ljust(width)}  {len(row['cases']):5d}  "
            f"{grounded:8d}  {', '.join(flags) if flags else 'ok'}"
        )

    print()
    with_lean = [row for row in rows if row["has_lean"]]
    nonvacuous = [row for row in with_lean if row["idioms"]]

    print("THE PRIMARY NUMBER — non-vacuous behavior guarantees")
    print(
        f"  circuits with a non-vacuity witness  : "
        f"{len(nonvacuous)}/{len(with_lean)}   (of circuits carrying Lean)"
    )
    print(
        f"  circuits carrying Lean at all        : "
        f"{len(with_lean)}/{total_circuits}"
    )
    for row in with_lean:
        if not row["idioms"]:
            print(f"    !! {row['circuit']}: NO non-vacuity idiom found")
    print()
    print("  idiom used, per circuit (five are recognised; counting one gives 9/21):")
    for row in with_lean:
        print(f"    {row['circuit'].ljust(width)}  {', '.join(row['idioms'])}")
    print()
    print("THE BUNDLING NUMBER (secondary; §9.0 denominator counts what could have DISAGREED)")
    print(
        f"  grounded assurance cases            : "
        f"{len(grounded_cases)}/{len(all_cases)}"
    )
    print(
        f"  circuits with every case grounded   : "
        f"{len(grounded_circuits)}/{total_circuits}"
    )
    print(
        f"  circuits with any assurance case    : "
        f"{len(with_case)}/{len(with_lean)}   (of circuits carrying Lean —"
        f" the SAME denominator as the primary number, deliberately:"
        f" quoting these two against different denominators is how a"
        f" bundling figure got read as a coverage figure)"
    )
    print()
    print()
    print(
        "  A case with NO-GROUNDING-WITNESS is one this instrument cannot see a"
    )
    print(
        "  witness for. That is a LOWER bound on non-vacuity, not a vacuity"
    )
    print(
        "  verdict: some cases are grounded semantically by other lemmas."
    )

    if options.min_grounded is not None and len(grounded_cases) < options.min_grounded:
        print(
            f"\nassurance_census: FAIL -- {len(grounded_cases)} grounded cases, "
            f"floor is {options.min_grounded}",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
