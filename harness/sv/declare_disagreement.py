#!/usr/bin/env python3
"""Write an `oracle_disagreement` declaration of harness/sv/cases2.json.

A declaration (docs/sv-oracle-disagreements.md) binds ONE departing simulator
to ONE row: the standard clause, the observation, the retirement condition,
the SHA-256 of the DUT source, its envelope, the canonical case and the
generated testbench, and BOTH complete traces. Until round 6 the digests were
computed by hand; this tool is the recipe, kept next to the checker that
verifies it (`oracle_disagreements.binding_digests`).

  python3 harness/sv/declare_disagreement.py --case NAME --sim xcelium --text T.json
        [--lean-wrapper CMD] [--write]

  --sim xcelium   the simulator trace is the PINNED one (xcelium_golden.json),
                  accepted only if its hash matches the DUT, testbench and
                  parameters as they are NOW and its status is `ok`;
  --sim iverilog  the simulator trace is a fresh local Icarus run;
  --text T.json   {"id", "declared", "reference", "observed",
                   "retirement_condition"} (all strings, as the checker requires);
  --write         insert (or replace) the block in cases2.json, keeping the
                  file's formatting; without it the block is printed.

The model trace comes from the Lean runner (`diff_test2.run_lean`; put the
machine's Lean slot in `--lean-wrapper`). The declaration is refused when the
two traces are equal (there is nothing to declare) or when the pin is stale,
failed or absent.
"""

import argparse
import json
import os
import sys
import tempfile

HARNESS_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HARNESS_DIR)
import diff_test2  # noqa: E402
import gen_tb2  # noqa: E402
import xcelium_batch  # noqa: E402
import xcelium_golden  # noqa: E402
from oracle_disagreements import DECLARABLE_SIMULATORS, HarnessError, binding_digests  # noqa: E402

TEXT_FIELDS = ("id", "declared", "reference", "observed", "retirement_condition")


def build_declaration(case, sim, text, source, envelope, tb_text, sim_trace, lean_trace, sigma="src"):
    """The `oracle_disagreement` block for `case`, key order as the committed
    declarations have it. Pure: no tool is run here."""
    if sim not in DECLARABLE_SIMULATORS:
        raise HarnessError("--sim must be one of %s" % ", ".join(DECLARABLE_SIMULATORS))
    for field in TEXT_FIELDS:
        if not isinstance(text.get(field), str) or not text[field].strip():
            raise HarnessError("declaration text is missing %s" % field)
    if sim_trace == lean_trace:
        raise HarnessError("the %s trace equals the model trace: nothing to declare" % sim)
    digests = binding_digests(case, source, envelope, tb_text)
    row = {"id": text["id"], "sim": sim}
    for field in TEXT_FIELDS[1:]:
        row[field] = text[field]
    for label in ("source", "envelope", "case", "testbench"):
        row[label + "_sha256"] = digests[label + "_sha256"]
    row["sigma"] = sigma
    row["sim_trace"] = list(sim_trace)
    row["lean_trace"] = list(lean_trace)
    return row


def pinned_trace(golden_path, name, dut_sv, tb_text, params):
    """The pinned Xcelium trace of `name`, only if it describes these sources."""
    golden = xcelium_golden.load(golden_path)
    if golden is None:
        raise HarnessError("no golden file at %s" % (golden_path or xcelium_golden.GOLDEN_JSON))
    entry = golden["rows"].get(name)
    if entry is None:
        raise HarnessError("row %s is not pinned" % name)
    now = xcelium_golden.row_hash(name, xcelium_golden.read_text(dut_sv), tb_text, params)
    if entry.get("hash") != now:
        raise HarnessError("the pin of %s is stale (the DUT, testbench or parameters changed)" % name)
    if entry.get("status") != xcelium_golden.STATUS_OK:
        raise HarnessError("the pin of %s is not ok: %s" % (name, entry.get("status")))
    return list(entry["cycles"])


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--case", required=True)
    ap.add_argument("--sim", required=True, choices=DECLARABLE_SIMULATORS)
    ap.add_argument("--text", required=True, help="JSON file with the declaration's text fields")
    ap.add_argument("--golden", default=None)
    ap.add_argument("--lean-wrapper", default=os.environ.get("SV_LEAN_WRAPPER"))
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()

    with open(diff_test2.CASES_JSON, encoding="utf-8") as handle:
        raw = handle.read()
    spec = json.loads(raw)
    matches = [c for c in spec["cases"] if c["name"] == args.case]
    if len(matches) != 1:
        raise SystemExit("no unique case named %r" % args.case)
    case = matches[0]
    if "refusal" in case:
        raise SystemExit("%s is a loud-refusal row: nothing is simulated, nothing to declare" % args.case)
    with open(args.text, encoding="utf-8") as handle:
        text = json.load(handle)
    sigmas = case.get("accept_sigmas", ["src"])
    if len(sigmas) != 1:
        raise SystemExit("a declaration is bound to ONE schedule; %s accepts %s" % (args.case, sigmas))

    xcelium_batch.install_lean_wrapper(args.lean_wrapper)
    dut_sv = os.path.join(diff_test2.REPO, "Examples", "system-verilog", case["example"],
                          case.get("file", case["top"]) + ".sv")
    envelope_path = dut_sv + ".json"
    try:
        ports, lean_trace = diff_test2.run_lean(envelope_path, case["name"], sigmas[0])
        tb_text = gen_tb2.generate_tb2(case["top"], ports, case)
        if args.sim == "xcelium":
            sim_trace = pinned_trace(args.golden, case["name"], dut_sv, tb_text, case.get("params"))
        else:
            with tempfile.TemporaryDirectory(prefix="sv-declare-") as work:
                sim_trace = diff_test2.run_iverilog(dut_sv, tb_text, work)
        with open(dut_sv, "rb") as handle:
            source = handle.read()
        with open(envelope_path, "rb") as handle:
            envelope = handle.read()
        row = build_declaration(case, args.sim, text, source, envelope, tb_text,
                                sim_trace, lean_trace, sigmas[0])
    except (HarnessError, gen_tb2.TbError) as error:
        raise SystemExit("declare_disagreement: %s" % error)

    if not args.write:
        print(json.dumps(row, indent=2, ensure_ascii=False))
        return 0
    # Re-read right before writing: other jobs edit this file too. The file must
    # round-trip byte for byte (indent 2, no ASCII escapes, trailing newline), or
    # the rewrite would reformat unrelated rows.
    with open(diff_test2.CASES_JSON, encoding="utf-8") as handle:
        fresh_raw = handle.read()
    fresh = json.loads(fresh_raw)
    if json.dumps(fresh, indent=2, ensure_ascii=False) + "\n" != fresh_raw:
        raise SystemExit("cases2.json no longer round-trips through json.dumps(indent=2); not rewriting it")
    target = next(c for c in fresh["cases"] if c["name"] == args.case)
    target["oracle_disagreement"] = row
    with open(diff_test2.CASES_JSON, "w", encoding="utf-8") as handle:
        handle.write(json.dumps(fresh, indent=2, ensure_ascii=False) + "\n")
    print("wrote the %s declaration %s into %s" % (args.sim, row["id"], args.case))
    return 0


if __name__ == "__main__":
    sys.exit(main())
