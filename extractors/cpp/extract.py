#!/usr/bin/env python3
"""Retain a complete Clang C++23 JSON AST and its translation inputs."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


SCHEMA_VERSION = "cpp-0.1"
PROFILE_ID = "cpp23-clang-json-0.1"
VALUE_FLAGS = {
    "-I", "-isystem", "-iquote", "-idirafter", "-include", "-imacros",
    "-D", "-U", "-target", "--target", "-isysroot", "--sysroot", "-resource-dir",
}
SWITCH_FLAGS = {
    "-pthread", "-nostdinc", "-nostdinc++", "-fexceptions", "-fno-exceptions",
    "-frtti", "-fno-rtti", "-fsigned-char", "-funsigned-char", "-m32", "-m64",
    "-Wall", "-Wextra", "-stdlib=libc++", "-stdlib=libstdc++",
}
ENVIRONMENT_KEYS = {
    "CPATH", "CPLUS_INCLUDE_PATH", "C_INCLUDE_PATH", "SDKROOT",
    "MACOSX_DEPLOYMENT_TARGET", "SOURCE_DATE_EPOCH",
}
DRIVER_OVERRIDE_KEYS = {"CCC_OVERRIDE_OPTIONS", "CCC_ADD_ARGS"}


class ExtractionError(Exception):
    """An input cannot be admitted under the declared translation profile."""


def digest(path):
    checksum = hashlib.sha256()
    try:
        with Path(path).open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                checksum.update(chunk)
    except OSError as error:
        raise ExtractionError(f"cannot hash input {path}: {error}") from error
    return checksum.hexdigest()


def validate_flags(flags):
    pending = None
    for flag in flags:
        if pending is not None:
            if not flag or flag.startswith(("@", "-")):
                raise ExtractionError(f"invalid value for {pending}: {flag!r}")
            pending = None
        elif flag in VALUE_FLAGS:
            pending = flag
        elif flag in SWITCH_FLAGS:
            continue
        elif any(flag.startswith(prefix) and len(flag) > len(prefix)
                 for prefix in ("-I", "-D", "-U", "--target=", "--sysroot=", "-resource-dir=")):
            continue
        else:
            raise ExtractionError(f"flag outside {PROFILE_ID}: {flag!r}")
    if pending is not None:
        raise ExtractionError(f"missing value for {pending}")


def frontend_flags(flags):
    arguments = []
    entries = iter(flags)
    for flag in entries:
        if flag == "-include":
            arguments.extend(["-Xclang", "-include", "-Xclang", next(entries)])
        else:
            arguments.append(flag)
    return arguments


def run(command, environment):
    try:
        result = subprocess.run(command, capture_output=True, text=True,
                                stdin=subprocess.DEVNULL, env=environment,
                                timeout=300, check=False)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise ExtractionError(f"frontend failed: {error}") from error
    if result.returncode != 0:
        raise ExtractionError(f"frontend exit {result.returncode}:\n{result.stderr}")
    return result


def dependency_escape(contents, offset):
    end = offset
    while end < len(contents) and contents[end] == "\\":
        end += 1
    count = end - offset
    if end == len(contents) or contents[end] not in " \t\r\n#":
        return "\\" * count, end, False
    following = contents[end]
    if following in "\r\n":
        if count != 1:
            raise ExtractionError("ambiguous dependency line continuation")
        end += 2 if contents[end:end + 2] == "\r\n" else 1
        return "", end, True
    literal = "\\" * (count // 2)
    if count % 2:
        return literal + following, end + 1, False
    if following == "#":
        raise ExtractionError("unescaped dependency comment")
    return literal, end + 1, True


def dependency_tokens(contents):
    names = []
    token = []
    offset = 0
    while offset < len(contents):
        character = contents[offset]
        separates = False
        if character == "\\":
            literal, offset, separates = dependency_escape(contents, offset)
            token.append(literal)
        elif character == "$":
            if contents[offset:offset + 2] != "$$":
                raise ExtractionError("unescaped dependency variable")
            token.append("$")
            offset += 2
        elif character == "#":
            raise ExtractionError("unescaped dependency comment")
        else:
            separates = character in " \t\r\n"
            if not separates:
                token.append(character)
            offset += 1
        if separates and token:
            name = "".join(token)
            if name:
                names.append(name)
            token = []
    if token:
        names.append("".join(token))
    return names


def dependency_paths(contents, cwd):
    target, separator, dependencies = contents.partition(":")
    if not separator or target.strip() != "cpp-input":
        raise ExtractionError("malformed frontend dependency manifest")
    names = dependency_tokens(dependencies)
    paths = sorted({str((cwd / name).resolve()) for name in names})
    if not paths:
        raise ExtractionError("frontend returned an empty dependency manifest")
    return paths


def manifest(paths):
    return [{"path": path, "sha256": digest(path)} for path in paths]


def parse_ast(contents):
    try:
        ast = json.loads(contents, parse_float=refuse_numeric_token,
                         parse_constant=refuse_numeric_token)
    except json.JSONDecodeError as error:
        raise ExtractionError(f"malformed frontend AST: {error}") from error
    if not isinstance(ast, dict) or ast.get("kind") != "TranslationUnitDecl":
        raise ExtractionError("frontend AST is not a translation unit")
    return ast


def refuse_numeric_token(token):
    raise ExtractionError(f"non-integer JSON numeric token outside {PROFILE_ID}: {token}")


def extract(source, *, clang="clang++", flags=None):
    flags = list(flags or [])
    validate_flags(flags)
    try:
        source = Path(source).resolve(strict=True)
    except OSError as error:
        raise ExtractionError(f"source unavailable: {error}") from error
    executable = shutil.which(str(clang))
    if executable is None:
        raise ExtractionError(f"frontend not found: {clang}")
    executable = str(Path(executable).absolute())
    compiler_hash = digest(executable)
    cwd = Path.cwd()
    environment = dict(os.environ)
    for key in sorted(DRIVER_OVERRIDE_KEYS):
        if key in environment:
            raise ExtractionError(f"frontend driver override environment refused: {key}")
    environment.setdefault("SOURCE_DATE_EPOCH", "0")
    command = [executable, "--no-default-config", "-x", "c++", "-std=c++23",
               "-pedantic-errors", *frontend_flags(flags)]
    with tempfile.TemporaryDirectory(prefix="leancpp-") as directory:
        depfile = Path(directory) / "inputs.d"
        run([*command, "-M", "-MT", "cpp-input", "-MF", str(depfile), str(source)], environment)
        paths = dependency_paths(depfile.read_text(), cwd)
        before = manifest(paths)
        argv = [*command, "-fsyntax-only", "-Xclang", "-ast-dump=json",
                "-MD", "-MT", "cpp-input", "-MF", str(depfile), str(source)]
        result = run(argv, environment)
        ast = parse_ast(result.stdout)
        after_paths = dependency_paths(depfile.read_text(), cwd)
        predefines = run([*command, "-dM", "-E", "-"], environment)
        after = manifest(after_paths)
    if paths != after_paths or before != after or compiler_hash != digest(executable):
        raise ExtractionError("translation inputs changed during extraction")
    source_entry = next((entry for entry in before if entry["path"] == str(source)), None)
    if source_entry is None:
        raise ExtractionError("source missing from frontend dependency manifest")
    return {
        "schema_version": SCHEMA_VERSION, "language": "cpp", "edition": "c++23",
        "profile_id": PROFILE_ID, "source_file": str(source),
        "source_sha256": source_entry["sha256"], "dependencies": before,
        "frontend": {
            "path": executable, "sha256": compiler_hash,
            "version": run([executable, "--version"], environment).stdout,
            "target": run([*command, "-dumpmachine"], environment).stdout.strip(),
            "argv": argv, "cwd": str(cwd), "predefined_macros": predefines.stdout,
            "environment": {key: environment[key] for key in sorted(ENVIRONMENT_KEYS)
                            if key in environment},
            "diagnostics": result.stderr,
        },
        "ast": ast,
    }


def validate_output(envelope, output):
    resolved = output.resolve()
    for dependency in envelope["dependencies"]:
        path = Path(dependency["path"])
        if resolved == path or (output.exists() and output.samefile(path)):
            raise ExtractionError(f"output aliases translation input: {path}")


def write_envelope(envelope, output):
    if output is not None:
        output = Path(output)
        validate_output(envelope, output)
    contents = json.dumps(envelope, ensure_ascii=False, separators=(",", ":")) + "\n"
    if output is None:
        sys.stdout.write(contents)
        return
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=output.parent,
                                     prefix=output.name + ".", delete=False) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(contents)
            stream.close()
            temporary.replace(output)
        finally:
            temporary.unlink(missing_ok=True)


def main(argv=None):
    arguments = list(sys.argv[1:] if argv is None else argv)
    split = arguments.index("--") if "--" in arguments else len(arguments)
    flags = arguments[split + 1:]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--clang", default=os.environ.get("LEANCPP_CLANG", "clang++"))
    options = parser.parse_args(arguments[:split])
    try:
        write_envelope(extract(options.source, clang=options.clang, flags=flags), options.out)
    except (ExtractionError, OSError, ValueError) as error:
        print(f"leancpp extraction refused: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
