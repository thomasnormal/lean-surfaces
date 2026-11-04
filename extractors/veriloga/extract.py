#!/usr/bin/env python3
"""Extract a deterministic Verilog-A envelope through OpenVAF's typed AST."""

from __future__ import annotations

import argparse
import os
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = Path(__file__).with_name("openvaf_ast") / "Cargo.toml"


def argument_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def extract(source: Path, output: Path | None = None) -> Path:
    source = source.resolve()
    output = (output or source.with_suffix(".json")).resolve()
    environment = os.environ.copy()
    environment["CARGO_NET_GIT_FETCH_WITH_CLI"] = "true"
    subprocess.run(
        [
            "cargo",
            "run",
            "--quiet",
            "--manifest-path",
            str(MANIFEST),
            "--",
            argument_path(source),
            argument_path(output),
        ],
        cwd=ROOT,
        env=environment,
        check=True,
    )
    return output


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("-o", "--output", type=Path)
    args = parser.parse_args()
    print(extract(args.source, args.output))


if __name__ == "__main__":
    main()
