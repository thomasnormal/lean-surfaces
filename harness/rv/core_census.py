#!/usr/bin/env python3
"""Census the E-facing constructs in a SystemVerilog core envelope.

The envelope is the source of truth for this instrument.  The census does not
parse Verilog again and does not turn an ``Unsupported`` node into an
admission.  It reports one row for each declaration, process, continuous
assignment, module member, and instance, together with the E rule (or the
exact loud refusal) that applies to the row.

Usage::

    python3 harness/rv/core_census.py CORE.sv.json
    python3 harness/rv/core_census.py CORE.sv.json --json /tmp/core-census.json
    python3 harness/rv/core_census.py --self-test

The JSON output is deliberately portable: it contains no absolute source
path, so a generated census can be moved between checkouts.  ``NOT REACHED``
means that the row is in an inactive generate branch or in an unreferenced
module-library entry.  It is kept separate from ``REFUSED``: a refusal is a
construct E has reached and rejected, while a not-reached row is still behind
the current hierarchy/elaboration frontier.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from typing import Any, Iterable, Optional


SCHEMA = "sv-core-census/1"
STATUSES = ("ADMITTED", "REFUSED", "NOT REACHED")

# This is the exact message in LeanModels.Sv.Param.untypedWidthMsg.  Keeping
# it here makes a census row useful without requiring a Lean process merely to
# print the first cross-check wall.
UNTYPED_WIDTH_MSG = (
    "Constant:untyped-width — an untyped parameter or localparam takes its "
    "expression's own type (IEEE 1800-2023 §6.20.2; slang, Yosys 0.53), "
    "while Icarus 12.0 gives it the lossless width of an expression built "
    "with + - * or ** ($bits of `SB + 1'b1` with an 8-bit SB is 9, of `N + "
    "1` with an int N 33): the two are different constants wherever the "
    "width is observable (a concatenation part, a negative value extended "
    "into a wider unsigned context, a context it widens) — refused for "
    "every such untyped constant, at every point"
)


def _line(node: Any) -> int:
    """Return the source line carried by an envelope node, or zero."""

    if not isinstance(node, dict):
        return 0
    span = node.get("span")
    if isinstance(span, dict):
        value = span.get("line")
        if isinstance(value, int):
            return value
    return 0


def _kind(node: Any) -> str:
    return node.get("kind", "<missing>") if isinstance(node, dict) else "<missing>"


def _name(node: Any) -> str:
    if not isinstance(node, dict):
        return ""
    for key in ("name", "sv_kind"):
        value = node.get(key)
        if isinstance(value, str):
            return value
    return ""


def _source_sha(data: dict[str, Any]) -> str:
    """The envelope's recorded source hash, if it has exactly one source."""

    sources = data.get("source_files")
    if isinstance(sources, list) and len(sources) == 1:
        item = sources[0]
        if isinstance(item, dict) and isinstance(item.get("sha256"), str):
            return item["sha256"]
    return ""


def _first_unsupported(node: Any, context: str = "expression") -> Optional[tuple[str, str]]:
    """Find the first retained unsupported leaf in source order.

    The context is used to reproduce the semantic interpreter's refusal
    spelling (``unsupported expression``, ``unsupported statement``, or
    ``unsupported process``).  We intentionally inspect only AST payloads;
    span dictionaries and metadata are not semantic children.
    """

    if isinstance(node, dict):
        if node.get("kind") == "Unsupported":
            sv_kind = node.get("sv_kind")
            if not isinstance(sv_kind, str):
                sv_kind = "Unsupported"
            return context, sv_kind
        kind = node.get("kind", "")
        next_context = context
        if kind in {"Block", "If", "For", "While", "Case", "CaseItem", "BlockingAssign", "NonblockingAssign", "AlwaysPosedge", "AlwaysComb", "AlwaysEvent", "Initial"}:
            next_context = "statement"
        elif kind in {"Assign", "Binary", "Unary", "Ternary", "Resize", "Literal", "Ident", "ParamRef", "Int", "ArraySel", "PartSelect", "BitSelect", "Concat"}:
            next_context = "expression"
        for key, value in node.items():
            if key in {"span", "text", "sourceRange"}:
                continue
            found = _first_unsupported(value, next_context)
            if found is not None:
                return found
    elif isinstance(node, list):
        for value in node:
            found = _first_unsupported(value, context)
            if found is not None:
                return found
    return None


def _refusal(sv_kind: str, context: str = "process") -> str:
    return f"unsupported {context} '{sv_kind}'"


def _expr_widens(node: Any) -> bool:
    """Mirror the conservative ``PExpr.icarusWidens`` shape test."""

    if not isinstance(node, dict):
        return False
    kind = node.get("kind")
    if kind == "Binary":
        op = node.get("op")
        if op in {"+", "-", "*", "**", "<<", "<<<"}:
            return True
        return _expr_widens(node.get("left")) or _expr_widens(node.get("right"))
    if kind == "Unary":
        return _expr_widens(node.get("operand"))
    if kind in {"Resize", "SignedResize", "Cast", "Squash"}:
        return _expr_widens(node.get("operand"))
    if kind == "Ternary":
        return _expr_widens(node.get("then")) or _expr_widens(node.get("else"))
    return False


def _literal_initializer(node: Any) -> bool:
    """Whether a declaration initializer is directly in the M0 literal tier."""

    if not isinstance(node, dict):
        return False
    # ``instExpr`` can materialize a few wrappers, but these are the only
    # initializer forms in the four core envelopes that are unambiguously
    # literal at the declaration point.  Any other shape is reported loudly;
    # the census must not guess a run-time initializer's value.
    return node.get("kind") in {"Int", "Literal", "Fill"}


def _const_value(node: Any, env: dict[str, int]) -> Optional[int]:
    """Small evaluator for generate reachability metadata only."""

    if not isinstance(node, dict):
        return None
    kind = node.get("kind")
    if kind == "Int" and isinstance(node.get("value"), int):
        return node["value"]
    if kind == "Literal":
        bits = node.get("bits")
        if isinstance(bits, str) and bits and set(bits) <= {"0", "1"}:
            return int(bits, 2)
    if kind in {"ParamRef", "GenvarRef"}:
        name = node.get("name")
        return env.get(name) if isinstance(name, str) else None
    if kind == "Unary":
        value = _const_value(node.get("operand"), env)
        if value is None:
            return None
        if node.get("op") == "-":
            return -value
        if node.get("op") == "+":
            return value
    if kind == "Binary":
        left = _const_value(node.get("left"), env)
        right = _const_value(node.get("right"), env)
        if left is None or right is None:
            return None
        op = node.get("op")
        try:
            if op == "+":
                return left + right
            if op == "-":
                return left - right
            if op == "*":
                return left * right
            if op == "/" and right:
                return left // right
            if op == "<<":
                return left << right
            if op == ">>":
                return left >> right
            if op in {"==", "==="}:
                return int(left == right)
            if op in {"!=", "!=="}:
                return int(left != right)
        except (ArithmeticError, ValueError):
            return None
    return None


def _instance_nodes(node: Any, env: Optional[dict[str, int]] = None) -> Iterable[dict[str, Any]]:
    """Yield active instance nodes, without treating metadata as children."""

    env = env or {}
    if isinstance(node, dict):
        kind = node.get("kind")
        if kind == "Instance":
            yield node
            return
        if kind == "GenerateIf":
            value = _const_value(node.get("cond"), env)
            branches = []
            if value is None or value != 0:
                branches.append(node.get("then", []))
            if value is None or value == 0:
                branches.append(node.get("else", []))
            for branch in branches:
                yield from _instance_nodes(branch, env)
            return
        if kind == "GenerateFor":
            count = node.get("resolved_count")
            if count is None or count > 0:
                yield from _instance_nodes(node.get("body", []), env)
            return
        for key, value in node.items():
            if key in {"span", "text", "sourceRange"}:
                continue
            yield from _instance_nodes(value, env)
    elif isinstance(node, list):
        for value in node:
            yield from _instance_nodes(value, env)


class Census:
    def __init__(self, data: dict[str, Any], input_path: pathlib.Path):
        self.data = data
        self.input_path = input_path
        self.top = data.get("top", "")
        modules = data.get("design", {}).get("modules", [])
        if not isinstance(modules, list) or not modules:
            raise ValueError("envelope design.modules must be a nonempty array")
        self.modules = [m for m in modules if isinstance(m, dict)]
        self.module_names = {m.get("name") for m in self.modules if isinstance(m.get("name"), str)}
        self.reachable = self._reachable_modules()
        self.rows: list[dict[str, Any]] = []
        self._emit_all()

    def _module_env(self, module: dict[str, Any]) -> dict[str, int]:
        env: dict[str, int] = {}
        for key in ("params", "local_params", "localParams"):
            for item in module.get(key, []) or []:
                if isinstance(item, dict) and isinstance(item.get("name"), str) and isinstance(item.get("resolved"), int):
                    env[item["name"]] = item["resolved"]
        return env

    def _reachable_modules(self) -> set[str]:
        if not isinstance(self.top, str):
            return set()
        by_name = {m.get("name"): m for m in self.modules if isinstance(m.get("name"), str)}
        reached = {self.top}
        todo = [self.top]
        while todo:
            name = todo.pop()
            module = by_name.get(name)
            if not module:
                continue
            env = self._module_env(module)
            for inst in _instance_nodes(module.get("generates", []), env):
                target = inst.get("module")
                if isinstance(target, str) and target in by_name and target not in reached:
                    reached.add(target)
                    todo.append(target)
            for inst in _instance_nodes(module.get("others", []), env):
                target = inst.get("module")
                if isinstance(target, str) and target in by_name and target not in reached:
                    reached.add(target)
                    todo.append(target)
            for proc in module.get("processes", []) or []:
                for inst in _instance_nodes(proc, env):
                    target = inst.get("module")
                    if isinstance(target, str) and target in by_name and target not in reached:
                        reached.add(target)
                        todo.append(target)
        return reached

    def _row(
        self,
        module: dict[str, Any],
        category: str,
        node: dict[str, Any],
        status: str,
        requirement: str,
        path: str,
        *,
        nested_line: Optional[int] = None,
    ) -> None:
        if status not in STATUSES:
            raise AssertionError(status)
        row = {
            "module": module.get("name", ""),
            "category": category,
            "kind": _kind(node),
            "name": _name(node),
            "line": _line(node),
            "status": status,
            "requirement": requirement,
            "path": path,
        }
        if nested_line is not None:
            row["refusal_line"] = nested_line
        self.rows.append(row)

    def _status_for_module(self, module: dict[str, Any]) -> Optional[str]:
        if module.get("name") not in self.reachable:
            return "NOT REACHED"
        return None

    def _emit_decl(self, module: dict[str, Any], node: dict[str, Any], path: str, reachable: Optional[str]) -> None:
        if reachable:
            self._row(module, "declaration", node, reachable, "module is not reached from the selected top", path)
            return
        name = _name(node)
        if node.get("kind") == "UnpackedDecl" or node.get("unpacked"):
            req = f"decl '{name}': unpacked array storage outside E (UnpackedDecl:memory)"
            self._row(module, "declaration", node, "REFUSED", req, path)
            return
        init = node.get("init")
        if init is not None and not _literal_initializer(init):
            req = f"decl '{name}': non-literal initializer outside the M0 tier"
            self._row(module, "declaration", node, "REFUSED", req, path)
            return
        self._row(module, "declaration", node, "ADMITTED", "Decl: packed scalar/vector storage (instDecl)", path)

    def _emit_param(self, module: dict[str, Any], node: dict[str, Any], path: str, reachable: Optional[str]) -> None:
        if reachable:
            self._row(module, "declaration", node, reachable, "module is not reached from the selected top", path)
            return
        expr = node.get("default", node.get("expr"))
        if node.get("type") is None and _expr_widens(expr):
            prefix = "localparam" if node.get("kind") == "LocalParam" else "parameter"
            req = f"{prefix} '{_name(node)}': {UNTYPED_WIDTH_MSG}"
            self._row(module, "declaration", node, "REFUSED", req, path)
            return
        self._row(module, "declaration", node, "ADMITTED", "Param: defaults/localparams elaboration", path)

    def _emit_port(self, module: dict[str, Any], node: dict[str, Any], path: str, reachable: Optional[str]) -> None:
        if reachable:
            category = "module_member" if _kind(node) == "Unsupported" else "declaration"
            self._row(module, category, node, reachable, "module is not reached from the selected top", path)
            return
        if _kind(node) == "Unsupported":
            self._row(module, "module_member", node, "REFUSED", _refusal(node.get("sv_kind", "Unsupported")), path)
            return
        nested = _first_unsupported(node)
        if nested:
            context, kind = nested
            self._row(module, "declaration", node, "REFUSED", _refusal(kind, context), path, nested_line=_line(node))
            return
        self._row(module, "declaration", node, "ADMITTED", "Port: four-state packed port declaration", path)

    def _emit_process(self, module: dict[str, Any], node: dict[str, Any], path: str, reachable: Optional[str], active: bool = True) -> None:
        category = "continuous_assign" if _kind(node) == "Assign" else "process"
        if reachable or not active:
            reason = "module is not reached from the selected top" if reachable else "generate branch is not reached at defaults"
            self._row(module, category, node, "NOT REACHED", reason, path)
            return
        kind = _kind(node)
        if kind == "Assign":
            rule = "Core0: Assign continuous assignment (Process2.assign)"
        elif kind == "AlwaysPosedge":
            rule = "Core1: AlwaysPosedge edge process with NBA queue"
        elif kind == "AlwaysPlain":
            rule = "Core1: Always source-kind-preserving plain process"
        elif kind == "AlwaysComb":
            rule = "Core0: AlwaysComb combinational process"
        elif kind == "AlwaysEvent":
            category = "process"
            rule = "Core0: implicit event process with raw-read sensitivity"
        elif kind == "Initial":
            category = "process"
            self._row(module, category, node, "REFUSED", _refusal("T2:Initial"), path)
            return
        elif kind == "Unsupported":
            category = "process"
            self._row(module, category, node, "REFUSED", _refusal(node.get("sv_kind", "Unsupported")), path)
            return
        else:
            category = "process"
            self._row(module, category, node, "REFUSED", _refusal(kind), path)
            return
        nested = _first_unsupported(node)
        if nested:
            context, bad_kind = nested
            self._row(module, category, node, "REFUSED", _refusal(bad_kind, context), path, nested_line=_line(node))
        else:
            self._row(module, category, node, "ADMITTED", rule, path)

    def _emit_instance(self, module: dict[str, Any], node: dict[str, Any], path: str, reachable: Optional[str], active: bool = True) -> None:
        if reachable or not active:
            reason = "module is not reached from the selected top" if reachable else "generate branch is not reached at defaults"
            self._row(module, "instance", node, "NOT REACHED", reason, path)
            return
        target = node.get("module", "?")
        if target in self.module_names:
            self._row(module, "instance", node, "ADMITTED", "Hier2: hierarchical instance flattening", path)
        else:
            req = f"module instance '{node.get('name', '?')}' of '{target}': definition is absent from the envelope"
            self._row(module, "instance", node, "REFUSED", req, path)

    def _emit_member(self, module: dict[str, Any], node: dict[str, Any], path: str, reachable: Optional[str], active: bool = True) -> None:
        if _kind(node) == "Instance":
            self._emit_instance(module, node, path, reachable, active)
            return
        if reachable or not active:
            reason = "module is not reached from the selected top" if reachable else "generate branch is not reached at defaults"
            self._row(module, "module_member", node, "NOT REACHED", reason, path)
            return
        if _kind(node) == "Unsupported":
            self._row(module, "module_member", node, "REFUSED", _refusal(node.get("sv_kind", "Unsupported")), path)
        else:
            self._row(module, "module_member", node, "ADMITTED", f"{_kind(node)}: structural module member", path)

    def _emit_nested(self, module: dict[str, Any], node: Any, path: str, reachable: Optional[str], active: bool) -> None:
        """Emit nested local declarations/instances and recurse through generates."""

        if isinstance(node, dict):
            kind = node.get("kind")
            if kind == "Instance":
                self._emit_instance(module, node, path, reachable, active)
                return
            if kind in {"LocalDecl", "Var", "Net", "UnpackedDecl"} and path:
                self._emit_decl(module, node, path, reachable)
                return
            if kind == "GenerateIf":
                self._emit_member(module, node, path, reachable, active)
                env = self._module_env(module)
                value = _const_value(node.get("cond"), env)
                self._emit_gen_list(module, node.get("then", []), path + "/then", reachable, active and (value is None or value != 0))
                self._emit_gen_list(module, node.get("else", []), path + "/else", reachable, active and (value is None or value == 0))
                return
            if kind == "GenerateFor":
                self._emit_member(module, node, path, reachable, active)
                count = node.get("resolved_count")
                self._emit_gen_list(module, node.get("body", []), path + "/body", reachable, active and (count is None or count > 0))
                return
            for key, value in node.items():
                if key in {"span", "text", "sourceRange"}:
                    continue
                self._emit_nested(module, value, path + "/" + key, reachable, active)
        elif isinstance(node, list):
            for index, value in enumerate(node):
                self._emit_nested(module, value, f"{path}[{index}]", reachable, active)

    def _emit_gen_list(self, module: dict[str, Any], items: Any, path: str, reachable: Optional[str], active: bool) -> None:
        if not isinstance(items, list):
            return
        for index, item in enumerate(items):
            if isinstance(item, dict) and item.get("kind") in {"Assign", "AlwaysPosedge", "AlwaysPlain", "AlwaysComb", "AlwaysEvent", "Initial", "Unsupported"}:
                if item.get("kind") == "AlwaysEvent":
                    # parseGenItem has no AlwaysEvent arm yet.  Keep the row
                    # (the source process is still part of the census), but
                    # report the exact parser boundary rather than pretending
                    # that the generate body entered E.
                    self._row(
                        module,
                        "process",
                        item,
                        "NOT REACHED" if (reachable or not active) else "REFUSED",
                        (
                            "module is not reached from the selected top"
                            if reachable
                            else "generate branch is not reached at defaults"
                            if not active
                            else 'GenerateIf: AlwaysEvent: unknown generate member kind "AlwaysEvent"'
                        ),
                        f"{path}[{index}]",
                    )
                else:
                    self._emit_process(module, item, f"{path}[{index}]", reachable, active)
            else:
                self._emit_nested(module, item, f"{path}[{index}]", reachable, active)

    def _emit_all(self) -> None:
        for module_index, module in enumerate(self.modules):
            reachable = self._status_for_module(module)
            prefix = f"modules[{module_index}]"
            for index, node in enumerate(module.get("params", []) or []):
                if isinstance(node, dict):
                    self._emit_param(module, node, f"{prefix}/params[{index}]", reachable)
            for index, node in enumerate(module.get("ports", []) or []):
                if isinstance(node, dict):
                    self._emit_port(module, node, f"{prefix}/ports[{index}]", reachable)
            for index, node in enumerate(module.get("decls", []) or []):
                if isinstance(node, dict):
                    self._emit_decl(module, node, f"{prefix}/decls[{index}]", reachable)
            for index, node in enumerate(module.get("processes", []) or []):
                if isinstance(node, dict):
                    self._emit_process(module, node, f"{prefix}/processes[{index}]", reachable)
                    self._emit_nested(module, node, f"{prefix}/processes[{index}]", reachable, True)
            self._emit_gen_list(module, module.get("generates", []), f"{prefix}/generates", reachable, True)
            for index, node in enumerate(module.get("others", []) or []):
                if isinstance(node, dict):
                    self._emit_member(module, node, f"{prefix}/others[{index}]", reachable, True)

    def result(self) -> dict[str, Any]:
        counts = {status: sum(row["status"] == status for row in self.rows) for status in STATUSES}
        try:
            envelope_sha = hashlib.sha256(self.input_path.read_bytes()).hexdigest()
        except OSError:
            envelope_sha = ""
        sources = self.data.get("source_files", [])
        source_files = [
            {"path": item.get("path", ""), "sha256": item.get("sha256", "")}
            for item in sources
            if isinstance(item, dict)
        ] if isinstance(sources, list) else []
        return {
            "schema": SCHEMA,
            "top": self.top,
            "envelope_sha256": envelope_sha,
            "source_sha256": _source_sha(self.data),
            "source_files": source_files,
            "modules": [m.get("name", "") for m in self.modules],
            "reachable_modules": sorted(self.reachable),
            "counts": counts,
            "refused": counts["REFUSED"],
            "not_reached": counts["NOT REACHED"],
            "remaining": counts["REFUSED"] + counts["NOT REACHED"],
            "rows": self.rows,
        }


def _read(path: pathlib.Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read envelope {path}: {exc}") from exc
    if not isinstance(data, dict):
        raise ValueError("envelope root must be an object")
    if data.get("schema_version") != "sv-0.2":
        raise ValueError(f"unsupported schema_version {data.get('schema_version')!r} (want 'sv-0.2')")
    if data.get("language") != "systemverilog" or data.get("mode") != "symbolic":
        raise ValueError("envelope must be a symbolic systemverilog sv-0.2 document")
    return data


def census(path: pathlib.Path) -> dict[str, Any]:
    return Census(_read(path), path).result()


def _fixture() -> dict[str, Any]:
    return {
        "schema_version": "sv-0.2",
        "language": "systemverilog",
        "mode": "symbolic",
        "top": "fixture",
        "source_files": [],
        "packages": [],
        "design": {
            "modules": [
                {
                    "kind": "Module",
                    "name": "fixture",
                    "params": [{"kind": "ParameterDecl", "name": "N", "resolved": 0, "default": {"kind": "Int", "value": 0}, "type": None, "span": {"line": 1}}],
                    "ports": [],
                    "decls": [
                        {"kind": "Var", "name": "a", "init": None, "span": {"line": 2}},
                        {"kind": "UnpackedDecl", "name": "mem", "unpacked": [{"kind": "Int", "value": 1}], "span": {"line": 3}},
                    ],
                    "processes": [
                        {"kind": "Assign", "span": {"line": 4}, "target": {"kind": "Ident", "name": "a"}, "value": {"kind": "Int", "value": 0}},
                        {"kind": "AlwaysPosedge", "span": {"line": 5}, "body": {"kind": "Block", "stmts": []}},
                    ],
                    "generates": [{"kind": "GenerateIf", "span": {"line": 6}, "cond": {"kind": "Int", "value": 0}, "then": [{"kind": "Assign", "span": {"line": 7}}], "else": []}],
                    "others": [{"kind": "Unsupported", "sv_kind": "NetSymbol:net-z", "text": "z", "span": {"line": 8}}],
                }
            ]
        },
    }


def self_test() -> None:
    result = Census(_fixture(), pathlib.Path("fixture.sv.json")).result()
    statuses = [(row["line"], row["category"], row["status"]) for row in result["rows"]]
    expected = [
        (1, "declaration", "ADMITTED"),
        (2, "declaration", "ADMITTED"),
        (3, "declaration", "REFUSED"),
        (4, "continuous_assign", "ADMITTED"),
        (5, "process", "ADMITTED"),
        (6, "module_member", "ADMITTED"),
        (7, "continuous_assign", "NOT REACHED"),
        (8, "module_member", "REFUSED"),
    ]
    if statuses != expected:
        raise AssertionError(f"self-test rows differ:\nexpected={expected!r}\nactual={statuses!r}")
    if result["counts"] != {"ADMITTED": 5, "REFUSED": 2, "NOT REACHED": 1}:
        raise AssertionError(result["counts"])
    print("core_census --self-test ok")


def _print(result: dict[str, Any]) -> None:
    print(f"top={result['top']} modules={','.join(result['modules'])}")
    print(f"reachable_modules={','.join(result['reachable_modules']) or '<none>'}")
    for row in result["rows"]:
        name = f" {row['name']}" if row["name"] else ""
        print(
            f"{row['status']:11} {row['module']}:{row['line']:>5} "
            f"{row['category']:<18} {row['kind']}{name} :: {row['requirement']}"
        )
    counts = result["counts"]
    print(
        "counts: "
        + ", ".join(f"{status}={counts[status]}" for status in STATUSES)
        + f"; remaining={result['remaining']}"
    )


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("envelope", nargs="?", type=pathlib.Path)
    parser.add_argument("--json", dest="json_path", type=pathlib.Path, help="write the deterministic census JSON")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        self_test()
        return 0
    if args.envelope is None:
        parser.error("an envelope is required unless --self-test is used")
    try:
        result = census(args.envelope)
    except ValueError as exc:
        parser.error(str(exc))
    if args.json_path is not None:
        args.json_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    _print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
