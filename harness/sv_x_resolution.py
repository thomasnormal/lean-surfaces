#!/usr/bin/env python3
"""Executable X-E per-read resolver.

This instrument is deliberately separate from E.  It enumerates the 0/1
values available at one read site, applies the operation's IEEE rule, and
discards the choice before the next read.  ``--strict`` turns an
unknown-sensitive decision or control value into a named refusal, which is
the interim proof boundary while the relation is not threaded through E.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


class XResolutionRefusal(Exception):
    """The strict interim profile refuses an unknown-sensitive operation."""


def resolve_read(value: str) -> tuple[str, ...]:
    """Return independent concrete reads for one four-state bit vector."""
    if any(bit.lower() not in "01xz" for bit in value):
        raise ValueError("four-state value must contain only 0/1/x/z")
    choices = [(bit,) if bit.lower() in "01" else ("0", "1")
               for bit in value]
    return tuple("".join(bits) for bits in itertools.product(*choices))


def two_state(value: str) -> str:
    """IEEE 1800-2023 §6.11 conversion, deterministic at the boundary."""
    if any(bit.lower() not in "01xz" for bit in value):
        raise ValueError("four-state value must contain only 0/1/x/z")
    return "".join("0" if bit.lower() in "xz" else bit for bit in value)


def decision(value: str, strict: bool = False) -> tuple[str, ...]:
    """Resolve an if/case decision to its possible boolean bit values."""
    reads = resolve_read(value)
    if strict and len(set(reads)) > 1:
        raise XResolutionRefusal("unknown decision value")
    return tuple(sorted(set(reads)))


def if_values(condition: str, then: str, otherwise: str,
              strict: bool = False) -> tuple[str, ...]:
    """Apply the IEEE truth rule independently at this if site."""
    outputs = []
    for value in decision(condition, strict):
        outputs.append(then if value != "0" else otherwise)
    return tuple(sorted(set(outputs)))


def case_values(subject: str, items: list[tuple[str, str]], default: str,
                strict: bool = False) -> tuple[str, ...]:
    """Resolve a plain case in source order for one selector read."""
    outputs = []
    for value in decision(subject, strict):
        selected = default
        for pattern, result in items:
            if value == pattern:
                selected = result
                break
        outputs.append(selected)
    return tuple(sorted(set(outputs)))


def index_reads(index: str, cells: dict[int, str], strict: bool = False) -> tuple[str, ...]:
    """Read one memory cell for every resolved index; invalid reads are x."""
    reads = resolve_read(index)
    if strict and len(set(reads)) > 1:
        raise XResolutionRefusal("unknown memory index")
    width = len(next(iter(cells.values()))) if cells else 1
    unknown = "x" * width
    outputs = []
    for concrete in reads:
        key = int(concrete, 2)
        outputs.append(cells.get(key, unknown))
    return tuple(sorted(set(outputs)))


def index_writes(index: str, cells: dict[int, str], value: str,
                 strict: bool = False) -> tuple[dict[int, str], ...]:
    """Enumerate memory states after one blocking write at this site."""
    reads = resolve_read(index)
    if strict and len(set(reads)) > 1:
        raise XResolutionRefusal("unknown memory write index")
    states = []
    for concrete in reads:
        state = dict(cells)
        key = int(concrete, 2)
        if key in state:
            state[key] = value
        states.append(state)
    return tuple(states)


def control_edges(value: str, strict: bool = False) -> tuple[str, ...]:
    """Possible control values for an x clock/set/reset read."""
    reads = resolve_read(value)
    if strict and len(set(reads)) > 1:
        raise XResolutionRefusal("unknown clock/set/reset control")
    return tuple(sorted(set(reads)))


def run_row(row: dict) -> dict:
    op = row["op"]
    strict = bool(row.get("strict", False))
    try:
        if op == "read":
            result = list(resolve_read(row["value"]))
        elif op == "two_state":
            result = two_state(row["value"])
        elif op == "decision":
            result = list(decision(row["value"], strict))
        elif op == "if":
            result = list(if_values(row["condition"], row["then"],
                                    row["else"], strict))
        elif op == "case":
            result = list(case_values(row["subject"],
                                      [(x[0], x[1]) for x in row["items"]],
                                      row["default"], strict))
        elif op == "index_read":
            cells = {int(k): v for k, v in row["cells"].items()}
            result = list(index_reads(row["index"], cells, strict))
        elif op == "index_write":
            cells = {int(k): v for k, v in row["cells"].items()}
            result = [{str(k): v for k, v in sorted(state.items())} for state in
                      index_writes(row["index"], cells, row["value"], strict)]
        elif op == "control":
            result = list(control_edges(row["value"], strict))
        else:
            raise ValueError("unknown resolver operation %r" % op)
        return {"name": row["name"], "status": "ok", "result": result}
    except XResolutionRefusal as exc:
        return {"name": row["name"], "status": "refusal", "message": str(exc)}


def check_battery(path: Path) -> int:
    rows = json.loads(path.read_text())
    failures = []
    for row in rows:
        got = run_row(row)
        expected_status = row.get("expected_status", "ok")
        if got["status"] != expected_status:
            failures.append((row["name"], got, row))
            continue
        if expected_status == "ok" and got["result"] != row["expected"]:
            failures.append((row["name"], got, row))
        if expected_status == "refusal" and got.get("message") != row["message"]:
            failures.append((row["name"], got, row))
    if failures:
        for name, got, row in failures:
            print("FAIL", name, "got", got, "expected", row)
        return 1
    print("sv-x-resolution: %d rows PASS" % len(rows))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--battery", type=Path,
                        default=Path(__file__).with_name("sv_x_resolution.json"))
    args = parser.parse_args()
    return check_battery(args.battery)


if __name__ == "__main__":
    raise SystemExit(main())
