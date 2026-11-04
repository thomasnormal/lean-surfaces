"""Strict byte observations and bounded process support for probe capture."""

import contextlib
import ctypes
import errno
import functools
import json
import math
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import threading
import time

from extract import DRIVER_OVERRIDE_KEYS, ENVIRONMENT_KEYS, ExtractionError, digest


class CaptureError(Exception):
    """A capture observation or publication cannot be established."""


class IntegerLexeme(str):
    """A JSON integer's exact token, distinct from a decoded JSON string."""


def utf8_string(value, subject):
    if not isinstance(value, str):
        raise CaptureError(f"{subject} must be a string")
    try:
        value.encode("utf-8")
    except UnicodeEncodeError as error:
        raise CaptureError(f"{subject} is not valid Unicode: {error}") from error
    return value


def controlled_environment(host=None):
    host = os.environ if host is None else host
    try:
        for key in host:
            utf8_string(key, "host environment key")
            if key in DRIVER_OVERRIDE_KEYS or key in ("LD_PRELOAD", "LD_LIBRARY_PATH") or key.startswith("DYLD_"):
                raise CaptureError(f"uncontrolled frontend environment refused: {key}")
        environment = {"PATH": os.defpath, "LC_ALL": "C", "TZ": "UTC"}
        for key in sorted(ENVIRONMENT_KEYS):
            if key in host:
                environment[key] = utf8_string(host[key], f"environment value {key}")
        environment.setdefault("SOURCE_DATE_EPOCH", "0")
    except (TypeError, AttributeError) as error:
        raise CaptureError(f"invalid host environment: {error}") from error
    return environment


def hash_file(path):
    try:
        return digest(path)
    except ExtractionError as error:
        raise CaptureError(str(error)) from error


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise CaptureError(f"duplicate decoded JSON key: {key!r}")
        result[key] = value
    return result


def refuse_numeric_token(token):
    raise CaptureError(f"non-integer JSON numeric token refused: {token}")


def validate_unicode(document):
    pending = [document]
    while pending:
        value = pending.pop()
        if isinstance(value, str):
            utf8_string(value, "decoded JSON string")
        elif isinstance(value, dict):
            pending.extend(value.keys())
            pending.extend(value.values())
        elif isinstance(value, list):
            pending.extend(value)


def validate_probe_header(document):
    if not isinstance(document, dict):
        raise CaptureError("probe wrapper must be an object")
    ast = document.get("ast")
    if not isinstance(ast, dict) or ast.get("kind") != "TranslationUnitDecl":
        raise CaptureError("probe AST is not a translation unit")
    metadata = document.get("metadata")
    if not isinstance(metadata, dict):
        raise CaptureError("probe metadata must be an object")
    pins = {"schema_version": "cpp-canonical-probe-0.3",
            "compiled_frontend": "21.1.8", "llvm_headers": "21.1.8"}
    for key, expected in pins.items():
        if metadata.get(key) != expected:
            raise CaptureError(f"unsupported probe {key}: {metadata.get(key)!r}")
    runtime = metadata.get("runtime_frontend")
    if not isinstance(runtime, str) or (runtime != "clang version 21.1.8" and
                                       not runtime.startswith("clang version 21.1.8 ")):
        raise CaptureError(f"unsupported probe runtime_frontend: {runtime!r}")
    if not isinstance(metadata.get("declarations"), list):
        raise CaptureError("probe declarations must be an array")


def strict_probe(path):
    try:
        contents = Path(path).read_bytes().decode("utf-8", errors="strict")
        document = json.loads(contents, object_pairs_hook=unique_object,
                              parse_int=IntegerLexeme,
                              parse_float=refuse_numeric_token,
                              parse_constant=refuse_numeric_token)
    except (OSError, UnicodeError, ValueError, RecursionError) as error:
        raise CaptureError(f"invalid probe JSON {path}: {error}") from error
    validate_unicode(document)
    validate_probe_header(document)
    return document


def validate_process_inputs(argv, cwd, environment, label, timeout, memory_mib):
    if not isinstance(argv, (list, tuple)) or not argv:
        raise CaptureError("process argv must be a nonempty ordered sequence")
    for argument in argv:
        utf8_string(argument, "process argument")
    utf8_string(str(cwd), "process cwd")
    utf8_string(label, "process label")
    if not label or label in (".", "..") or any(character in label for character in ("/", "\\", "\x00")):
        raise CaptureError("process label must be a safe artifact basename")
    if type(timeout) not in (int, float) or not math.isfinite(timeout) or timeout <= 0:
        raise CaptureError("process timeout must be finite and positive")
    if type(memory_mib) is not int or memory_mib <= 0:
        raise CaptureError("process memory bound must be a positive integer")
    if not isinstance(environment, dict):
        raise CaptureError("process environment must be an explicit mapping")
    for key, value in environment.items():
        utf8_string(key, "process environment key")
        utf8_string(value, f"process environment value {key}")
    if sys.platform != "linux" or not hasattr(os, "wait4"):
        raise CaptureError("bounded capture requires Linux wait4 and RLIMIT_AS")
    if threading.active_count() != 1:
        raise CaptureError("bounded capture requires a single-threaded Python launcher")


def limit_process_resources(memory_mib):
    memory_bytes = memory_mib * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_AS, (memory_bytes, memory_bytes))
    file_size_bytes = 4 * 1024 * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_FSIZE, (file_size_bytes, file_size_bytes))


def kill_process_group(process):
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def process_group_survives(process):
    try:
        os.killpg(process.pid, 0)
    except ProcessLookupError:
        return False
    return True


def reap_process(process, timeout, started):
    deadline = started + timeout
    while True:
        waited_pid, status, usage = os.wait4(process.pid, os.WNOHANG)
        if waited_pid:
            process.returncode = os.waitstatus_to_exitcode(status)
            return usage, False
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            kill_process_group(process)
            waited_pid, status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
            return usage, True
        time.sleep(min(0.01, remaining))


def process_receipt(argv, cwd, label, timeout, memory_mib, elapsed, usage,
                    process, timed_out, observation_error):
    exit_status = None if process is None else process.returncode
    signal_number = -exit_status if exit_status is not None and exit_status < 0 else None
    return {"argv": list(argv), "cwd": str(cwd),
            "stdout": f"{label}.stdout", "stderr": f"{label}.stderr",
            "launched": process is not None, "exit_status": exit_status,
            "signal": signal_number, "timed_out": timed_out,
            "elapsed_seconds": elapsed,
            "max_rss_kib": None if usage is None else usage.ru_maxrss,
            "measurement_scope": "not-observed" if usage is None else
                "linux-wait4-child-resource-usage-including-reaped-descendants",
            "observation_error": observation_error,
            "bounds": {"timeout_seconds": timeout, "memory_mib": memory_mib,
                       "file_size_bytes": 4 * 1024 * 1024 * 1024,
                       "scope": "frontend-subprocess-only",
                       "memory_scope": "inherited-per-process-address-space-limit",
                       "file_size_scope": "inherited-per-file-size-limit"}}


def write_process_receipt(directory, label, receipt):
    path = directory / f"{label}.process.json"
    try:
        with path.open("x", encoding="utf-8") as stream:
            json.dump(receipt, stream, ensure_ascii=False, allow_nan=False)
            stream.write("\n")
    except (OSError, UnicodeError, ValueError) as error:
        raise CaptureError(f"cannot retain process observation {path}: {error}") from error


def cleanup_process(process):
    if process is None or process.returncode == 0:
        return None
    kill_process_group(process)
    if process.returncode is None:
        waited_pid, status, usage = os.wait4(process.pid, 0)
        process.returncode = os.waitstatus_to_exitcode(status)
        return usage
    return None


def run_process(argv, cwd, environment, directory, label, timeout, memory_mib):
    validate_process_inputs(argv, cwd, environment, label, timeout, memory_mib)
    directory = Path(directory)
    stdout_path = directory / f"{label}.stdout"
    stderr_path = directory / f"{label}.stderr"
    logs = f"stdout={stdout_path}, stderr={stderr_path}"
    process = None
    usage = None
    timed_out = False
    observation_error = None
    started = time.monotonic()
    try:
        with contextlib.ExitStack() as stack:
            stdout = stack.enter_context(stdout_path.open("xb"))
            stderr = stack.enter_context(stderr_path.open("xb"))
            process = subprocess.Popen(argv, cwd=cwd, env=environment,
                                       stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
                                       start_new_session=True,
                                       preexec_fn=functools.partial(limit_process_resources, memory_mib))
            usage, timed_out = reap_process(process, timeout, started)
            if process.returncode == 0 and process_group_survives(process):
                kill_process_group(process)
                observation_error = "frontend process group outlived completed subprocess"
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        observation_error = str(error)
    finally:
        cleanup_usage = cleanup_process(process)
        if cleanup_usage is not None:
            usage = cleanup_usage
    elapsed = time.monotonic() - started
    receipt = process_receipt(argv, cwd, label, timeout, memory_mib, elapsed,
                              usage, process, timed_out, observation_error)
    write_process_receipt(directory, label, receipt)
    if observation_error is not None:
        raise CaptureError(f"process launch or observation failed: {observation_error}; {logs}")
    if timed_out:
        raise CaptureError(f"process timed out after {timeout} seconds; {logs}")
    if process.returncode != 0:
        raise CaptureError(f"process exit status {process.returncode}; {logs}")
    return receipt


def atomic_publish(staging, destination):
    if sys.platform != "linux":
        raise CaptureError("atomic no-overwrite publication requires Linux renameat2")
    staging = Path(staging).absolute()
    destination = Path(destination).absolute()
    if staging.is_symlink() or not staging.is_dir():
        raise CaptureError(f"publication staging is not a directory: {staging}")
    source_bytes = utf8_string(str(staging), "publication staging path").encode("utf-8")
    destination_bytes = utf8_string(str(destination), "publication destination path").encode("utf-8")
    library = ctypes.CDLL(None, use_errno=True)
    rename = getattr(library, "renameat2", None)
    if rename is None:
        raise CaptureError("atomic no-overwrite publication unavailable: renameat2 missing")
    rename.argtypes = (ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint)
    rename.restype = ctypes.c_int
    if rename(-100, source_bytes, -100, destination_bytes, 1) != 0:
        error_number = ctypes.get_errno()
        if error_number in (errno.EEXIST, errno.ENOTEMPTY):
            raise CaptureError(f"publication destination already exists: {destination}")
        if error_number in (errno.ENOSYS, errno.EINVAL, errno.EOPNOTSUPP):
            raise CaptureError("atomic no-overwrite publication unavailable on this filesystem")
        raise CaptureError(f"publication failed: {os.strerror(error_number)}")
