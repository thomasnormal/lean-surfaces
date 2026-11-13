#!/usr/bin/env python3
"""Price parser-native record-layout joins on a frozen external manifest.

The manifest source bytes are fed to the approved C extractor with Clang's
record-layout probe enabled.  The report only counts joined envelope nodes; it
does not interpret source text or claim aggregate semantics.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def record_nodes(envelope, name=None):
    return [node for node in walk(envelope)
            if node.get("kind") == "RecordDecl" and
            (name is None or node.get("name") == name)]


def classify(node):
    if "record_layout" not in node:
        return "missing-layout"
    layout = node["record_layout"]
    if layout.get("tag_kind") not in ("struct", "union"):
        return "invalid-tag-kind"
    if not isinstance(layout.get("size_bytes"), int) or not isinstance(layout.get("alignment_bytes"), int):
        return "invalid-size-alignment"
    fields = layout.get("fields")
    if not isinstance(fields, list):
        return "invalid-fields"
    return "joined"


def layout_summary(node):
    layout = node.get("record_layout")
    if not layout:
        return None
    fields = layout.get("fields", [])
    return {
        "size_bytes": layout.get("size_bytes"),
        "alignment_bytes": layout.get("alignment_bytes"),
        "bitfield_count": sum(bool(field.get("bitfield")) for field in fields),
        "bitfields": [
            {"name": field.get("name"),
             "offset_bits": field.get("offset_bits"),
             "width_bits": field.get("width_bits")}
            for field in fields if field.get("bitfield")
        ],
    }


def run(args):
    manifest = json.loads(Path(args.manifest).read_text())
    cache = Path(args.cache_root or manifest["cache"])
    source_name_prefix = manifest["pin"]["subdir"]
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = []
    selected = set(args.name) if args.name else None
    for item in manifest.get("tests", []):
        if selected is not None and item["name"] not in selected:
            continue
        source = cache / "src" / item["name"]
        if item.get("status") != "parsed" or not source.is_file():
            continue
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        if digest != item.get("sha256"):
            raise RuntimeError("source hash mismatch for %s" % item["name"])
        output = out_dir / (Path(item["name"]).stem + ".json")
        command = [sys.executable, "extractors/c/extract.py", str(source),
                   "--source-name", source_name_prefix + "/" + item["name"],
                   "-o", str(output)]
        env = os.environ.copy()
        env["LEAN_C_CLANG"] = args.clang
        env["LEAN_C_RECORD_LAYOUT_PLUGIN"] = args.plugin
        result = subprocess.run(command, capture_output=True, text=True, env=env)
        if result.returncode:
            raise RuntimeError("extract failed for %s: %s" %
                               (item["name"], result.stderr[-2000:]))
        envelope = json.loads(output.read_text())
        nodes = record_nodes(envelope, args.record_name)
        classes = [classify(node) for node in nodes]
        rows.append({"name": item["name"], "records": len(nodes),
                     "classes": classes,
                     "layouts": [summary for node in nodes
                                 if (summary := layout_summary(node)) is not None],
                     "joined": bool(nodes) and all(c == "joined" for c in classes)})
    report = {"schema": "c-record-layout-join-price-0.2",
              "record_name": args.record_name, "rows": rows,
              "files": len(rows),
              "files_with_record": sum(row["records"] > 0 for row in rows),
              "files_fully_joined": sum(row["joined"] for row in rows),
              "files_with_bitfields": sum(
                  any(layout["bitfield_count"] for layout in row["layouts"])
                  for row in rows)}
    if args.json:
        Path(args.json).write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    print(json.dumps(report, indent=1, sort_keys=True))
    return report


def self_test():
    envelope = {"translation_unit": {"decls": [
        {"kind": "RecordDecl", "name": "S",
         "record_layout": {"tag_kind": "struct", "size_bytes": 4,
                            "alignment_bytes": 4, "fields": []}}
    ]}}
    nodes = record_nodes(envelope, "S")
    if len(nodes) != 1 or classify(nodes[0]) != "joined":
        raise RuntimeError("record-layout join self-test failed")
    if record_nodes({"translation_unit": {"decls": []}}, "S"):
        raise RuntimeError("record-layout missing-record self-test failed")
    if len(record_nodes({"translation_unit": {"decls": [
            {"kind": "RecordDecl", "name": "A"},
            {"kind": "RecordDecl", "name": "B"}]}}, None)) != 2:
        raise RuntimeError("record-layout all-record self-test failed")
    if "bit-fields" not in render({"files": 0, "files_fully_joined": 0,
                                    "files_with_bitfields": 0, "rows": []}):
        raise RuntimeError("record-layout price rendering self-test failed")
    print("c_record_layout_join_price: self-test ok")


def render(report):
    lines = ["# C parser-native bit-field layout price", "",
             "Measured from the pinned Clang record-layout probe on a frozen external manifest.", "",
             "- files: %d" % report["files"],
             "- fully joined records: %d" % report["files_fully_joined"],
             "- files with bit-fields: %d" % report["files_with_bitfields"], "",
             "| file | size | alignment | bit-fields | offsets / widths |",
             "| --- | ---: | ---: | ---: | --- |"]
    for row in report["rows"]:
        layouts = row.get("layouts", [])
        if not layouts:
            lines.append("| `%s` | — | — | — | no joined layout |" % row["name"])
            continue
        layout = layouts[0]
        bits = ", ".join(
            "%s@%s/%s" % (field["name"] or "<anonymous>",
                           field["offset_bits"], field["width_bits"])
            for field in layout["bitfields"])
        lines.append("| `%s` | %s | %s | %s | %s |" % (
            row["name"], layout["size_bytes"], layout["alignment_bytes"],
            layout["bitfield_count"], bits or "none"))
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest")
    parser.add_argument("--plugin")
    parser.add_argument("--clang", default=os.environ.get("LEAN_C_CLANG", "clang"))
    parser.add_argument("--record-name", default=None,
                        help="restrict the price to one record name (default: all records)")
    parser.add_argument("--cache-root",
                        help="source cache root, overriding the manifest's recorded path")
    parser.add_argument("--name", action="append",
                        help="restrict the price to this manifest name (repeatable)")
    parser.add_argument("--out-dir")
    parser.add_argument("--json")
    parser.add_argument("--page")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    try:
        if args.self_test:
            self_test()
            return 0
        if not args.manifest or not args.plugin or not args.out_dir:
            parser.error("--manifest, --plugin, and --out-dir are required")
        report = run(args)
        if args.page:
            Path(args.page).write_text(render(report))
        return 0
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as error:
        print("c_record_layout_join_price: %s" % error, file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
