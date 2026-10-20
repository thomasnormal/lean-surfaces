"""Exact, source-bound simulator disagreements shared by the SV runners.

The model continues to implement IEEE 1800. Both complete observed traces
are checked on every run, and changed or resolved discrepancies fail.
"""

import hashlib
import json


class HarnessError(Exception):
    pass


class SimulatorError(HarnessError):
    def __init__(self, message, stage, result):
        super().__init__(message)
        self.stage = stage
        self.returncode = result.returncode
        self.stdout = result.stdout
        self.stderr = result.stderr


def _check_bindings(case, row, source, envelope, tb_text):
    for field in ("id", "declared", "reference", "observed", "retirement_condition"):
        if not isinstance(row.get(field), str) or not row[field].strip():
            raise HarnessError("oracle declaration missing %s" % field)
    inputs = {
        "source": source,
        "envelope": envelope,
        "case": json.dumps({k: v for k, v in case.items()
                            if k not in ("oracle_disagreement", "icarus_unavailable")},
                           sort_keys=True, separators=(",", ":")).encode(),
        "testbench": tb_text.encode(),
    }
    for label, data in inputs.items():
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
    if observed not in row.get("failures", []):
        raise HarnessError("%s: unexpected simulator failure; review the declaration\n%s"
                           % (row["id"], json.dumps(observed, indent=2, sort_keys=True)))
    return row["id"]


def oracle_disagreement(case, sim, source, envelope, tb_text,
                        sim_trace, lean_by_sigma):
    """Check an exact simulator discrepancy, including its retirement alarm.

    This records a simulator's departure from the standard, not permission
    for the model to depart from it. No trace is normalized or projected.
    """
    row = case.get("oracle_disagreement")
    if row is None:
        return None
    if not isinstance(row, dict) or row.get("sim") != "iverilog":
        raise HarnessError("invalid oracle_disagreement declaration")
    if sim != row["sim"]:
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


def report_annotation(message, level="warning", title="SV oracle coverage"):
    import os
    if os.environ.get("GITHUB_ACTIONS") == "true":
        # Workflow-command data escapes preserve multiline diagnostics as one
        # annotation, retrievable even when the job log needs authentication.
        escaped = message.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
        print("::%s title=%s::%s" % (level, title, escaped))
