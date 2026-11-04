"""Bind notebook headers to their envelopes and actual compiled import graph."""

import hashlib
import json
import subprocess
from pathlib import Path


DEPENDENCY_PROBE = Path(__file__).with_name("notebook_dependencies.lean")


def file_hash(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def header_key(envelopes, compiler, environment, root):
    """Return a content key, or None when dependencies cannot be verified."""
    if not compiler:
        return None
    try:
        completed = subprocess.run(
            [compiler, "--run", str(DEPENDENCY_PROBE)],
            cwd=str(root), env=environment, capture_output=True,
            text=True, timeout=120,
        )
        if completed.returncode != 0:
            return None
        dependencies = json.loads(completed.stdout)
        if not isinstance(dependencies, list) or not dependencies:
            return None
        if any(not isinstance(path, str) or not path for path in dependencies):
            return None
        artifacts = {
            (Path(root) / path).resolve() for path in dependencies
        }
        artifacts.update((Path(compiler).resolve(), DEPENDENCY_PROBE.resolve()))
        payload = {
            "artifacts": [(str(path), file_hash(path)) for path in sorted(artifacts)],
            "envelopes": [(stem, str(path), file_hash(path)) for stem, path in envelopes],
        }
        return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()
    except (OSError, ValueError, subprocess.TimeoutExpired):
        return None


def cached_header(metadata, key, artifact):
    """Accept only the verified dependency key and exact compiled header bytes."""
    if key is None:
        return False
    try:
        return json.loads(Path(metadata).read_text(encoding="utf-8")) == {
            "version": 1, "key": key, "artifact": file_hash(artifact),
        }
    except (OSError, ValueError):
        return False


def store_header(metadata, key, artifact):
    Path(metadata).write_text(json.dumps({
        "version": 1, "key": key, "artifact": file_hash(artifact),
    }), encoding="utf-8")
