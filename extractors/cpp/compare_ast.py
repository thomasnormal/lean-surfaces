#!/usr/bin/env python3
"""Compare complete parsed C++ AST projections, not C++ program semantics."""

import argparse
import hashlib
import json
import os
import pathlib
import re
import sys
import tempfile
import time


FORMAT = "cpp-ast-fingerprint-2"
POINTER_FIELDS = frozenset((
    "id", "previousDecl", "parentDeclContextId", "firstRedecl", "declId",
    "referencedMemberDecl", "labelDeclId", "targetLabelDeclId", "typeAliasDeclId", "temp",
))
POINTER_PATTERN = re.compile(r"0x[0-9a-fA-F]+\Z")


def child_path(path, segment):
    return path + "/" + str(segment).replace("~", "~0").replace("/", "~1")


def nested_containers(value):
    if isinstance(value, dict):
        children = ((field, value[field]) for field in sorted(value, reverse=True))
    else:
        children = ((ordinal, value[ordinal]) for ordinal in reversed(range(len(value))))
    for segment, child in children:
        if isinstance(child, (dict, list)):
            yield segment, child


def index_witnesses(ast):
    witnesses = {}
    records = 0
    pending = [("", ast)]
    while pending:
        path, value = pending.pop()
        if not isinstance(value, (dict, list)):
            continue
        if isinstance(value, dict):
            identifier = value.get("id")
            if isinstance(identifier, str):
                records += 1
                if identifier not in witnesses:
                    witnesses[identifier] = path
        pending.extend((child_path(path, segment), child)
                       for segment, child in nested_containers(value))
    return witnesses, records


def text_bytes(value):
    return value.encode("utf-8", errors="surrogatepass")


def pointer_tokens(value, field, parent_path, witnesses, problems, counters):
    counters["pointer_slots"] += 1
    path = child_path(parent_path, field)
    if field not in POINTER_FIELDS:
        problems["unrecognized_pointer_slots"].append(path)
        token = b"s" + text_bytes(value)
        return token, token
    if value not in witnesses:
        problems["unwitnessed_pointer_slots"].append(path)
        return b"p", b"u"
    return b"p", b"r" + text_bytes(witnesses[value])


def scalar_tokens(value, field, parent_path, witnesses, problems, counters):
    if isinstance(value, str):
        if POINTER_PATTERN.fullmatch(value):
            return pointer_tokens(value, field, parent_path, witnesses, problems, counters)
        token = b"s" + text_bytes(value)
    elif value is None:
        token = b"n"
    elif isinstance(value, bool):
        token = b"b1" if value else b"b0"
    elif isinstance(value, int):
        token = b"i" + str(value).encode("ascii")
    else:
        raise ValueError("AST contains a non-integer JSON number or non-JSON value")
    return token, token


def token_pairs(ast, witnesses, problems, counters):
    pending = [("value", "", None, ast)]
    while pending:
        operation, parent_path, field, value = pending.pop()
        if operation == "token":
            yield value, value
        elif isinstance(value, dict):
            path = parent_path if field is None else child_path(parent_path, field)
            yield b"{", b"{"
            pending.append(("token", "", None, b"}"))
            for child_field in sorted(value, reverse=True):
                pending.append(("value", path, child_field, value[child_field]))
                pending.append(("token", "", None, b"k" + text_bytes(child_field)))
        elif isinstance(value, list):
            path = parent_path if field is None else child_path(parent_path, field)
            yield b"[", b"["
            pending.append(("token", "", None, b"]"))
            for ordinal in reversed(range(len(value))):
                pending.append(("value", path, ordinal, value[ordinal]))
        else:
            yield scalar_tokens(value, field, parent_path, witnesses, problems, counters)


def update_token(digest, token):
    digest.update(len(token).to_bytes(8, "big"))
    digest.update(token)


def fingerprint_ast(ast):
    started = time.monotonic()
    witnesses, records = index_witnesses(ast)
    indexed = time.monotonic()
    problems = {"unrecognized_pointer_slots": [], "unwitnessed_pointer_slots": []}
    counters = {"pointer_slots": 0, "tokens": 0}
    nonpointer = hashlib.sha256()
    witnessed = hashlib.sha256()
    for erased_token, witnessed_token in token_pairs(ast, witnesses, problems, counters):
        update_token(nonpointer, erased_token)
        update_token(witnessed, witnessed_token)
        counters["tokens"] += 1
    return {
        "format": FORMAT,
        "nonpointer_sha256": nonpointer.hexdigest(),
        "witnessed_sha256": witnessed.hexdigest(),
        "id_bearing_records": records,
        "distinct_ids": len(witnesses),
        **counters,
        "problems": {name: sorted(paths) for name, paths in problems.items()},
        "index_seconds": indexed - started,
        "fingerprint_seconds": time.monotonic() - indexed,
    }


def compare_fingerprints(left, right):
    if left["format"] != FORMAT or right["format"] != FORMAT:
        raise ValueError("fingerprint format mismatch")
    nonpointer_equal = left["nonpointer_sha256"] == right["nonpointer_sha256"]
    witnessed_equal = left["witnessed_sha256"] == right["witnessed_sha256"]
    unknown = any(record["problems"]["unrecognized_pointer_slots"] for record in (left, right))
    missing = any(record["problems"]["unwitnessed_pointer_slots"] for record in (left, right))
    return {
        "nonpointer_digest_equal": nonpointer_equal,
        "witnessed_digest_equal": witnessed_equal,
        "nonpointer_comparison_status": (
            "refused-unrecognized-pointer-slots" if unknown
            else "equal" if nonpointer_equal else "different"
        ),
        "witnessed_comparison_status": (
            "refused-unwitnessed-or-unrecognized-pointer-slots" if unknown or missing
            else "equal" if witnessed_equal else "different"
        ),
    }


def refuse_numeric_token(token):
    raise ValueError("non-integer JSON numeric token: " + token)


def unique_object(pairs):
    result = {}
    for field, value in pairs:
        if field in result:
            raise ValueError("duplicate JSON object field: " + field)
        result[field] = value
    return result


def load_fingerprint(path, maximum_bytes):
    size = path.stat().st_size
    if size > maximum_bytes:
        raise ValueError("input exceeds explicit byte bound: " + str(path))
    started = time.monotonic()
    with path.open(encoding="utf-8") as source:
        document = json.load(source, parse_float=refuse_numeric_token,
                             parse_constant=refuse_numeric_token, object_pairs_hook=unique_object)
    parsed = time.monotonic()
    if not isinstance(document, dict):
        raise ValueError("input must wrap a TranslationUnitDecl AST: " + str(path))
    ast = document.get("ast")
    if not isinstance(ast, dict) or ast.get("kind") != "TranslationUnitDecl":
        raise ValueError("input must wrap a TranslationUnitDecl AST: " + str(path))
    fingerprint = fingerprint_ast(ast)
    return {"file": str(path.resolve()), "file_bytes": size,
            "parse_seconds": parsed - started, **fingerprint}


def refuse_output_alias(output, inputs):
    for source in inputs:
        if output.resolve() == source.resolve():
            raise ValueError("output aliases input: " + str(source))
        if output.exists() and source.exists() and os.path.samefile(output, source):
            raise ValueError("output aliases input: " + str(source))


def publish_report(output, report):
    temporary_path = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", delete=False,
                                         dir=output.parent, prefix=".cpp-ast-comparison-") as target:
            temporary_path = pathlib.Path(target.name)
            json.dump(report, target, indent=2, ensure_ascii=True)
            target.write("\n")
        os.replace(temporary_path, output)
    finally:
        if temporary_path is not None and temporary_path.exists():
            temporary_path.unlink()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=pathlib.Path)
    parser.add_argument("--out", required=True, type=pathlib.Path)
    parser.add_argument("--max-input-mib", default=64, type=int)
    arguments = parser.parse_args(argv)
    if arguments.max_input_mib <= 0:
        parser.error("--max-input-mib must be positive")
    try:
        refuse_output_alias(arguments.out, arguments.inputs)
        fingerprints = [load_fingerprint(path, arguments.max_input_mib * 1024 * 1024)
                        for path in arguments.inputs]
        comparisons = [{"left": fingerprints[0]["file"], "right": record["file"],
                        **compare_fingerprints(fingerprints[0], record)}
                       for record in fingerprints[1:]]
        report = {"schema_version": "cpp-ast-comparison-1", "inputs": fingerprints,
                  "comparisons": comparisons, "max_input_bytes": arguments.max_input_mib * 1024 * 1024,
                  "claim": "Parsed full-AST fingerprint evidence only; no C++ semantic admission",
                  "policy": "Sequential bounded parses; all AST fields; first occurrence-path ID witnesses"}
        publish_report(arguments.out, report)
    except (OSError, ValueError, RecursionError) as error:
        print("cpp-ast-comparison-refused: " + str(error), file=sys.stderr)
        return 2
    print(json.dumps({"out": str(arguments.out), "comparisons": comparisons}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
