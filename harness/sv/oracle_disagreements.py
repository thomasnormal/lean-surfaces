"""Exact, source-bound simulator disagreements shared by the SV runners.

The model continues to implement IEEE 1800. Both complete observed traces
are checked on every run, and changed or resolved discrepancies fail.

A declaration names the departing simulator in `sim`: `"iverilog"` (the
original and still the common case) or `"xcelium"` (round 6, 2026-10-29: the
reference simulator itself departs from an explicit IEEE 1800-2023 sentence,
and the departure cannot be refused statically -- the run-time-base partial
out-of-range part-select, docs/sv-oracle-disagreements.md). Xcelium is not
available everywhere, so an Xcelium declaration is checked in two places: by
a LIVE `xrun` run exactly like an Icarus one (`oracle_disagreement`, where the
harness's simulator name `xrun` and the declaration's name `xcelium` are the
same simulator), and against the PINNED trace of
`harness/sv/xcelium_golden.json` (`golden_disagreement`, used by
`diff_test2.py --golden`), where the pin plays the simulator. Either way both
complete traces are compared with the recorded ones; a resolved or a changed
departure is a hard failure.
"""

import hashlib
import json
import re


class HarnessError(Exception):
    pass


# HOST FRAMING OF ONE ICARUS FAILURE (2026-10-28). The unavailable-oracle
# signatures were recorded with Ubuntu's Icarus 12.0-2build2; Homebrew's
# Icarus 12.0 on macOS fails at the same stage, with the same exit status and
# the same tool diagnostic, but the HOST wraps it differently in two places:
#
#   * a C `assert` in vvp is printed by the C library -- glibc writes
#     `vvp: FILE:LINE: PRETTY-FUNCTION: Assertion `EXPR' failed.`, macOS libc
#     writes `Assertion failed: (EXPR), function FUNC, file FILE, line LINE.`;
#   * an aborted `ivl` (Icarus's own `assert:` line, unchanged on both hosts)
#     is reported by the `/bin/sh` that the iverilog driver runs its pipeline
#     in -- dash prints `Aborted (core dumped)`, macOS's bash prints a job
#     report naming the preprocessor `Done` and the `ivl` stage `Abort trap: 6`
#     with process ids and temporary file names that differ on every run.
#
# Both sides of a comparison are reduced to the same canonical text before
# comparing, and ONLY these forms are rewritten: the assertion keeps its
# file, line, function name and expression (a different assertion, or the
# same one at another line, still differs), and the abort report keeps which
# pipeline stage died and of which signal (an ivlpp abort, a segmentation
# fault or a bare `Aborted` without the recorded framing still differs).
# Stage, exit status, stdout and every other stderr line stay exact.
_GLIBC_ASSERT = re.compile(
    r"^[\w.+-]+: (?P<file>[^\s:]+):(?P<line>\d+): (?P<func>[^\n]+?): "
    r"Assertion `(?P<expr>[^\n]*)' failed\.$", re.M)
_DARWIN_ASSERT = re.compile(
    r"^Assertion failed: \((?P<expr>[^\n]*)\), function (?P<func>[^,\n]+), "
    r"file (?P<file>[^,\n]+), line (?P<line>\d+)\.$", re.M)
_DASH_IVL_ABORT = re.compile(r"^Aborted \(core dumped\)$", re.M)
_DARWIN_IVL_ABORT = re.compile(
    r"^sh: line \d+: +\d+ Done +\S*/lib/ivl/ivlpp [^\n]*\n"
    r" +\d+ Abort trap: 6 +\| \S*/lib/ivl/ivl [^\n]*$", re.M)
_IVL_ABORT = "<sh: ivl stage aborted (SIGABRT)>"


def _short_function(name):
    """`bool vvp_vector4_t::set_vec(unsigned int, ...)` -> `set_vec`, the
    name macOS libc prints (`__func__`); glibc prints the pretty signature."""
    head = name.split("(", 1)[0].strip()
    return re.split(r"[\s:*&]+", head)[-1]


def _canonical_assert(match):
    return "<assert %s:%s %s: %s>" % (match.group("file"), match.group("line"),
                                      _short_function(match.group("func")),
                                      match.group("expr"))


def canonical_tool_output(text):
    """Rewrite only the host-specific framing described above."""
    text = _GLIBC_ASSERT.sub(_canonical_assert, text)
    text = _DARWIN_ASSERT.sub(_canonical_assert, text)
    text = _DASH_IVL_ABORT.sub(_IVL_ABORT, text)
    return _DARWIN_IVL_ABORT.sub(_IVL_ABORT, text)


def canonical_failure(failure):
    return dict(stage=failure.get("stage"), returncode=failure.get("returncode"),
                stdout=canonical_tool_output(failure.get("stdout", "")),
                stderr=canonical_tool_output(failure.get("stderr", "")))


class SimulatorError(HarnessError):
    def __init__(self, message, stage, result):
        super().__init__(message)
        self.stage = stage
        self.returncode = result.returncode
        self.stdout = result.stdout
        self.stderr = result.stderr


def binding_inputs(case, source, envelope, tb_text):
    """The four byte strings a declaration is bound to (docs/sv-oracle-disagreements.md)."""
    return {
        "source": source,
        "envelope": envelope,
        "case": json.dumps({k: v for k, v in case.items()
                            if k not in ("oracle_disagreement", "icarus_unavailable")},
                           sort_keys=True, separators=(",", ":")).encode(),
        "testbench": tb_text.encode(),
    }


def binding_digests(case, source, envelope, tb_text):
    """`{source_sha256, envelope_sha256, case_sha256, testbench_sha256}` of a
    declaration's inputs: what `_check_bindings` compares. Used to write a
    declaration (`harness/sv/declare_disagreement.py`)."""
    return {label + "_sha256": hashlib.sha256(data).hexdigest()
            for label, data in binding_inputs(case, source, envelope, tb_text).items()}


def _check_bindings(case, row, source, envelope, tb_text):
    for field in ("id", "declared", "reference", "observed", "retirement_condition"):
        if not isinstance(row.get(field), str) or not row[field].strip():
            raise HarnessError("oracle declaration missing %s" % field)
    for label, data in binding_inputs(case, source, envelope, tb_text).items():
        if hashlib.sha256(data).hexdigest() != row.get(label + "_sha256"):
            raise HarnessError("%s: changed %s; review the oracle declaration"
                               % (row["id"], label))


def oracle_unavailability(case, source, envelope, tb_text, source_path, error):
    """Recognize only a bound, previously observed Icarus tool failure.

    Successful compilation/simulation is checked by the caller's retirement
    alarm. No successful trace can be classified as an unavailable oracle.
    """
    row = case.get("icarus_unavailable")
    if row is None:
        return None
    _check_bindings(case, row, source, envelope, tb_text)
    observed = dict(stage=error.stage, returncode=error.returncode,
                    stdout=error.stdout.replace(source_path, "<source>"),
                    stderr=error.stderr.replace(source_path, "<source>"))
    recorded = [canonical_failure(f) for f in row.get("failures", [])]
    if canonical_failure(observed) not in recorded:
        raise HarnessError("%s: unexpected simulator failure; review the declaration\n%s"
                           % (row["id"], json.dumps(observed, indent=2, sort_keys=True)))
    return row["id"]


# The simulators a declaration may name, by the name the declaration uses. The
# harness calls Xcelium `xrun` (its binary); a declaration calls it `xcelium`.
DECLARABLE_SIMULATORS = ("iverilog", "xcelium")


def declaration_simulator(sim):
    """The declaration-side name of a harness simulator name."""
    return "xcelium" if sim == "xrun" else sim


def oracle_disagreement(case, sim, source, envelope, tb_text,
                        sim_trace, lean_by_sigma):
    """Check an exact simulator discrepancy, including its retirement alarm.

    This records a simulator's departure from the standard, not permission
    for the model to depart from it. No trace is normalized or projected.
    `sim` is the harness's simulator name (`iverilog`, `xrun`) or the
    declaration's (`xcelium`).
    """
    row = case.get("oracle_disagreement")
    if row is None:
        return None
    if not isinstance(row, dict) or row.get("sim") not in DECLARABLE_SIMULATORS:
        raise HarnessError("invalid oracle_disagreement declaration")
    if declaration_simulator(sim) != row["sim"]:
        return None
    _check_bindings(case, row, source, envelope, tb_text)
    identity = row["id"]
    sigma = row.get("sigma")
    if sigma not in ("src", "rev") or list(lean_by_sigma) != [sigma]:
        raise HarnessError("%s: changed schedule set" % identity)
    lean = lean_by_sigma[sigma]
    if sim_trace == lean:
        raise HarnessError("%s: disagreement resolved; retire the declaration"
                           % identity)
    if sim_trace != row.get("sim_trace") or lean != row.get("lean_trace"):
        raise HarnessError("%s: unexpected trace; disagreement has changed"
                           % identity)
    return identity


def check_declaration_bindings(case, source, envelope, tb_text):
    """The input bindings of a declaration alone (source, envelope, case,
    testbench digests); raises `HarnessError` on any change. None when the
    case declares nothing."""
    row = case.get("oracle_disagreement")
    if row is None:
        return None
    if not isinstance(row, dict) or row.get("sim") not in DECLARABLE_SIMULATORS:
        raise HarnessError("invalid oracle_disagreement declaration")
    _check_bindings(case, row, source, envelope, tb_text)
    return row["id"]


def golden_disagreement(case, source, envelope, tb_text, pinned_trace, lean_by_sigma):
    """The pinned-Xcelium twin of `oracle_disagreement`: the PIN plays the
    simulator (`harness/sv/xcelium_golden.json`, docs/sv-xcelium-reference.md).

    Returns the declaration id when the case declares an `xcelium` departure
    and the pinned trace and the model trace are exactly the recorded ones;
    None when the case declares nothing about Xcelium (an Icarus declaration
    is not this function's business); raises `HarnessError` when the
    departure is resolved (the pin equals the model) or has changed (either
    trace differs from the recorded one) or an input binding changed.
    """
    row = case.get("oracle_disagreement")
    if not isinstance(row, dict) or row.get("sim") != "xcelium":
        return None
    return oracle_disagreement(case, "xcelium", source, envelope, tb_text,
                               pinned_trace, lean_by_sigma)


def report_annotation(message, level="warning", title="SV oracle coverage"):
    import os
    if os.environ.get("GITHUB_ACTIONS") == "true":
        # Workflow-command data escapes preserve multiline diagnostics as one
        # annotation, retrievable even when the job log needs authentication.
        escaped = message.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
        print("::%s title=%s::%s" % (level, title, escaped))
