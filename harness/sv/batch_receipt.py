#!/usr/bin/env python3
"""Run one seeded ordinary-E/source differential pass over the clean-room rows.

The manifest is deliberately explicit: the SystemVerilog frontend remains the
only source parser, while this script only describes the ports needed to drive
the parser-produced design.  A temporary Lean program loads every envelope
through ``load_design_sv2`` and executes ``CoreMemDesign``.  The same stimulus
is emitted into a generated source testbench for Icarus and Xcelium.

Run from the repository root, for example::

    python3 harness/sv/batch_receipt.py --cleanroom-dir /path/to/cleanroom

The command prints one ``CYCLE`` line per simulator and fixture, followed by a
per-cycle MATCH/DIVERGE verdict.  No generated source, envelope, simulator
work library, or Lean file is written into the repository.
"""

from __future__ import annotations

import argparse
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXTRACT = ROOT / "extractors" / "sv" / "extract.py"
SEED = 0x5EED_2026
CYCLES = 8


@dataclass(frozen=True)
class Port:
    name: str
    width: int
    clock: bool = False
    reset_active_low: bool = False


@dataclass(frozen=True)
class Point:
    label: str
    args: tuple[int, ...]


@dataclass(frozen=True)
class Fixture:
    source: str
    top: str
    inputs: tuple[Port, ...]
    outputs: tuple[Port, ...]
    points: tuple[Point, ...] = (Point("default", ()),)
    retain_loops: bool = False
    retain_proc_rewrites: bool = False


# This is the bounded runnable set from the ordinary-route census.  Widths are
# source facts, not a second parser: Slang still produces and validates each
# envelope before Lean or a simulator sees it.
FIXTURES: tuple[Fixture, ...] = (
    # The inbox order starts with the storage/index walls that external users
    # are waiting on, then the variable-index loop, explicit width conversion,
    # and packed-register family.  The remaining runnable census rows follow.
    Fixture("parameterized_unpacked_storage.sv", "parameterized_unpacked_storage",
            (Port("x", 8),), (Port("y", 8),),
            (Point("N1", (1,)), Point("N2", (2,)))),
    Fixture("default_point_array.sv", "default_point_array",
            (Port("clk", 1, clock=True), Port("d", 8)), (Port("q", 8),),
            retain_loops=True, retain_proc_rewrites=True),
    Fixture("generated_array_index.sv", "generated_array_index",
            (Port("x", 8),), (Port("y", 8),),
            retain_proc_rewrites=True),
    Fixture("generate_if_unpacked_array.sv", "generate_if_unpacked_array",
            (Port("x", 8),), (Port("y", 8),),
            (Point("N1", (1,)), Point("N2", (2,))),
            retain_proc_rewrites=True),
    Fixture("for_loop.sv", "for_loop",
            (Port("clk", 1, clock=True), Port("d", 8)), (Port("q", 8),),
            retain_loops=True, retain_proc_rewrites=True),
    Fixture("constant_width_conversion.sv", "constant_width_conversion",
            (Port("x", 1),), (Port("y", 1),),
            (Point("E8", (8,)), Point("E4", (4,)))),
    Fixture("localparam_shift.sv", "localparam_shift",
            (Port("x", 8),), (Port("y", 8),),
            (Point("E8", (8,)), Point("E4", (4,)))),
    Fixture("array_index.sv", "array_index",
            (Port("i", 2),), (Port("y", 8),)),
    Fixture("memory_edge_loop.sv", "memory_edge_loop",
            (Port("clk", 1, clock=True), Port("d", 8)), (Port("q", 8),),
            (Point("default", ()),),
            retain_loops=True, retain_proc_rewrites=True),
    Fixture("function_source_edge.sv", "function_source_edge",
            (Port("clk", 1, clock=True), Port("d", 1)), (Port("q", 1),),
            retain_proc_rewrites=True),
    Fixture("generate_parameter.sv", "generate_parameter",
            (Port("x", 1),), (Port("y", 1),),
            (Point("W8", (8,)), Point("W3", (3,)))),
    Fixture("initial_syscall.sv", "initial_syscall",
            (Port("x", 1),), (Port("y", 1),)),
    Fixture("multi_clock_domain.sv", "multi_clock_domain",
            (Port("aclk", 1, clock=True), Port("bclk", 1, clock=True), Port("d", 1)),
            (Port("x", 1), Port("y", 1))),
    Fixture("preempt_block_refuse.sv", "preemptive_schedule",
            (Port("a", 1), Port("b", 1)),
            (Port("q", 1), Port("r", 1), Port("z", 1))),
    Fixture("profile_mixed.sv", "profile_mixed",
            (Port("clk", 1, clock=True), Port("rst", 1, reset_active_low=True),
             Port("d", 1)), (Port("q", 1), Port("y", 1))),
    Fixture("signed_bit_select.sv", "signed_select",
            (Port("x", 8),), (Port("y", 1),)),
    Fixture("signed_decl.sv", "signed_comparison",
            (Port("x", 8),), (Port("y", 1),)),
    Fixture("timed_event_loop.sv", "timed_event_loop",
            (Port("x", 8),), (Port("y", 4),)),
    Fixture("typed_bit_localparam.sv", "typed_localparam",
            (Port("d", 1),), (Port("q", 1),)),
    Fixture("wire_output_port.sv", "wire_output_port",
            (Port("a", 1),), (Port("y", 1),)),
)


def run_checked(argv: list[str], cwd: Path, timeout: int = 120) -> str:
    proc = subprocess.Popen(argv, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
        raise RuntimeError(f"{' '.join(argv)} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{' '.join(argv)} exited {proc.returncode}:\n{out}{err}")
    return out


def bits(value: int | str, width: int) -> str:
    if isinstance(value, str):
        return value * width
    return format(value & ((1 << width) - 1), f"0{width}b")


def port_width(fixture: Fixture, point: Point, port: Port) -> int:
    if fixture.top == "localparam_shift" and point.args:
        return point.args[0]
    if fixture.top == "memory_edge_loop" and point.args:
        return point.args[0]
    return port.width


def stimuli(fixture: Fixture, point: Point, seed: int) -> list[dict[str, int | str]]:
    stable_tag = sum((i + 1) * ord(c) for i, c in enumerate(fixture.top + point.label))
    rng = random.Random(seed ^ stable_tag)
    result: list[dict[str, int | str]] = []
    for cycle in range(CYCLES):
        row: dict[str, int | str] = {}
        for port in fixture.inputs:
            if port.clock:
                # The x/z rows deliberately include clocks.  0/1 rows provide
                # ordinary edges before and after those unknown transitions.
                value: int | str = (0, 1, 0, 1, "x", "z", 0, 1)[cycle]
            elif cycle == 4:
                value = "x"
            elif cycle == 5:
                value = "z"
            elif port.reset_active_low and cycle == 0:
                value = 0
            elif port.reset_active_low:
                value = 1
            else:
                value = rng.randrange(1 << port_width(fixture, point, port))
            # The initial syscall is a safety check rather than a reset port.
            # Give its first sample a known one so the simulator's time-zero
            # initial block is independent of active-region ordering.
            if fixture.top == "initial_syscall" and port.name == "x" and cycle == 0:
                value = 1
            row[port.name] = value
        result.append(row)
    return result


def lean_literal(value: int | str, width: int) -> str:
    if isinstance(value, str):
        return f'LVec.lit "{value * width}"'
    return f"LVec.ofNat {width} {value}"


def lean_stimulus(rows: list[dict[str, int | str]], fixture: Fixture, point: Point) -> str:
    rendered = []
    for row in rows:
        fields = ", ".join(
            f'("{p.name}", {lean_literal(row[p.name], port_width(fixture, point, p))})'
            for p in fixture.inputs)
        rendered.append(f"[{fields}]")
    return "[" + ",\n   ".join(rendered) + "]"


def sv_literal(value: int | str, width: int) -> str:
    if isinstance(value, str):
        return f"{width}'b" + value * width
    return f"{width}'b" + format(value & ((1 << width) - 1), f"0{width}b")


def testbench(fixture: Fixture, point: Point, rows: list[dict[str, int | str]]) -> str:
    params = ""
    if point.args:
        names = {
            "constant_width_conversion": ("E",),
            "generate_parameter": ("W",),
            "localparam_shift": ("E",),
            "memory_edge_loop": ("W", "N"),
            "parameterized_unpacked_storage": ("N",),
            "generate_if_unpacked_array": ("N",),
        }[fixture.top]
        params = "#(" + ", ".join(f".{n}({v})" for n, v in zip(names, point.args)) + ")"
    declarations = []
    connections = []
    for p in fixture.inputs:
        width = port_width(fixture, point, p)
        typ = "logic" if width == 1 else f"logic [{width - 1}:0]"
        declarations.append(f"  {typ} {p.name};")
        connections.append(f".{p.name}({p.name})")
    for p in fixture.outputs:
        width = port_width(fixture, point, p)
        typ = "wire" if width == 1 else f"wire [{width - 1}:0]"
        declarations.append(f"  {typ} {p.name};")
        connections.append(f".{p.name}({p.name})")
    displays = " ".join(f"%b" for _ in fixture.outputs)
    display_args = ", ".join(p.name for p in fixture.outputs)
    assignments = []
    for i, row in enumerate(rows):
        assignments.extend(f"    {p.name} = {sv_literal(row[p.name], port_width(fixture, point, p))};"
                           for p in fixture.inputs)
        assignments.append(f"    #1 $display(\"ROW {i} {displays}\", {display_args});")
    return "\n".join([
        "`timescale 1ns/1ps",
        f"module batch_tb;",
        *declarations,
        f"  {fixture.top} {params} dut ({', '.join(connections)});",
        "  initial begin",
        *assignments,
        "    $finish;",
        "  end",
        "endmodule",
        "",
    ])


def lean_program(entries: list[tuple[Fixture, Point, Path, list[dict[str, int | str]]]]) -> str:
    loads = []
    runs = []
    for number, (fixture, point, envelope, rows) in enumerate(entries):
        name = f"batch_{number}_{re.sub('[^A-Za-z0-9]', '_', fixture.top)}"
        loads.append(f'load_design_sv2 {name} from "{envelope}"')
        args = " ".join(str(x) for x in point.args)
        family = f"{name}.e" + ((" " + args) if args else "")
        stim = lean_stimulus(rows, fixture, point)
        outs = "[" + ", ".join(f'"{p.name}"' for p in fixture.outputs) + "]"
        runs.append(f'#eval emit "{fixture.top}" "{point.label}" ({family}) {stim} {outs}')
    return "\n".join([
        "import LeanModels.Sv.Ingest2",
        "import LeanModels.Sv.Kernel.CoreMemExec",
        "open LeanModels.Sv",
        "open LeanModels.Sv.Kernel",
        "set_option maxRecDepth 100000",
        "",
        *loads,
        "",
        "def runRows (d : CoreMemDesign) (s : CoreMemState) : List SvState → Res (List CoreMemState)",
        "  | [] => .ok []",
        "  | row :: rest => do",
        "      let s' ← d.step s row",
        "      let tail ← runRows d s' rest",
        "      .ok (s' :: tail)",
        "",
        "def emitRows (tag point : String) (d : CoreMemDesign) (rows : List CoreMemState)",
        "    (names : List String) (i : Nat) : IO Unit :=",
        "  match rows with",
        "  | [] => pure ()",
        "  | s :: rest => do",
        "      let vals := names.map (SvState.showSignal (CoreMemState.view d s))",
        "      IO.println (\"E \" ++ tag ++ \" \" ++ point ++ \" \" ++ toString i ++ \" \" ++ String.intercalate \" \" vals)",
        "      emitRows tag point d rest names (i + 1)",
        "",
        "def emit (tag point : String) (r : Res CoreMemDesign) (stim : List SvState)",
        "    (names : List String) : IO Unit :=",
        "  match r with",
        "  | .ok d =>",
        "      match d.initialState with",
        "      | .ok s =>",
        "          match runRows d s stim with",
        "          | .ok rows => emitRows tag point d rows names 0",
        "          | .timeout => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" timeout\")",
        "          | .unsupported e => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" \" ++ e)",
        "      | .timeout => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" initial-timeout\")",
        "      | .unsupported e => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" \" ++ e)",
        "  | .timeout => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" instantiate-timeout\")",
        "  | .unsupported e => IO.println (\"ERROR \" ++ tag ++ \" \" ++ point ++ \" \" ++ e)",
        "",
        *runs,
        "def main : IO Unit := pure ()",
        "",
    ])


def parse_rows(text: str, prefix: str) -> dict[tuple[str, str], list[list[str]]]:
    result: dict[tuple[str, str], list[list[str]]] = {}
    for line in text.splitlines():
        parts = line.split()
        if len(parts) < 5 or parts[0] != prefix:
            continue
        key = (parts[1], parts[2])
        result.setdefault(key, []).append(parts[4:])
    return result


def simulator_rows(text: str, fixture: Fixture) -> list[list[str]]:
    result = []
    for line in text.splitlines():
        parts = line.split()
        if len(parts) >= 2 + len(fixture.outputs) and parts[0] == "ROW":
            result.append(parts[2:])
    return result


def run_simulator(sim: str, fixture: Fixture, point: Point,
                  rows: list[dict[str, int | str]], source: Path, work: Path) -> tuple[str, list[list[str]]]:
    tb = work / "batch_tb.sv"
    tb.write_text(testbench(fixture, point, rows))
    sources = [str(source), str(tb)]
    if sim == "iverilog":
        exe = work / "sim.out"
        run_checked(["iverilog", "-g2012", "-s", "batch_tb", "-o", str(exe)] + sources,
                    work)
        out = run_checked(["vvp", str(exe)], work)
    else:
        out = run_checked(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                           "-top", "batch_tb"] + sources, work)
    return out, simulator_rows(out, fixture)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cleanroom-dir", type=Path, default=Path("cleanroom"),
                        help="directory containing the census .sv fixtures")
    parser.add_argument("--seed", type=lambda x: int(x, 0), default=SEED)
    parser.add_argument("--lean-group-size", type=int, default=2,
                        help="number of fixture points per ordinary Lean process")
    parser.add_argument("--ordinary-timeout", type=int, default=60,
                        help="seconds allowed for one ordinary Lean group")
    parser.add_argument("--only", nargs="*", default=None,
                        help="optional fixture tops to measure (default: all)")
    args = parser.parse_args()
    cleanroom = args.cleanroom_dir.resolve()
    if not cleanroom.is_dir():
        raise SystemExit(f"clean-room directory does not exist: {cleanroom}")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise SystemExit("Icarus Verilog 13.0 is required")
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    print(f"seed=0x{args.seed:x} cycles={CYCLES}")
    iverilog_version = run_checked(["iverilog", "-V"], ROOT, timeout=30).splitlines()[0]
    print("Icarus:", iverilog_version)
    xrun_version = "unavailable"
    if "xrun" in simulators:
        xrun_version = run_checked(["xrun", "-version"], ROOT, timeout=30).splitlines()[0]
        print("Xcelium:", xrun_version)

    with tempfile.TemporaryDirectory(prefix="sv-batch-") as tmp_name:
        tmp = Path(tmp_name)
        entries = []
        fixtures = tuple(f for f in FIXTURES if args.only is None or f.top in args.only)
        if not fixtures:
            raise SystemExit("--only selected no known fixture")
        for fixture in fixtures:
            source = cleanroom / fixture.source
            if not source.exists():
                raise SystemExit(f"missing fixture: {source}")
            flags = ["--top", fixture.top]
            if fixture.retain_proc_rewrites:
                flags.append("--retain-proc-rewrites")
            if fixture.retain_loops:
                flags.append("--retain-loops")
            envelope = tmp / f"{fixture.top}.sv.json"
            run_checked([sys.executable, str(EXTRACT), *flags, "-o", str(envelope), str(source)], ROOT)
            for point in fixture.points:
                rows = stimuli(fixture, point, args.seed)
                entries.append((fixture, point, envelope, rows))

        # Keeping a few source-shaped designs per generated Lean file avoids a
        # single enormous kernel reduction while preserving one top-level batch
        # command and one shared manifest.  The resulting ordinary rows are
        # still collected before either simulator is run.
        ordinary: dict[tuple[str, str], list[list[str]]] = {}
        errors: list[str] = []
        group_size = max(1, args.lean_group_size)
        for group_no in range(0, len(entries), group_size):
            group = entries[group_no:group_no + group_size]
            lean_file = tmp / f"batch_{group_no // group_size}.lean"
            lean_file.write_text(lean_program(group))
            print(f"ordinary group {group_no // group_size + 1}/{(len(entries) + group_size - 1) // group_size}",
                  flush=True)
            try:
                lean_out = run_checked(["lake", "env", "lean", "--run", str(lean_file)], ROOT,
                                       timeout=args.ordinary_timeout)
            except RuntimeError as exc:
                errors.append(f"ERROR ordinary group {group_no // group_size + 1}: {exc}")
                continue
            for key, rows in parse_rows(lean_out, "E").items():
                ordinary[key] = rows
            errors.extend(line for line in lean_out.splitlines()
                          if line.startswith("ERROR "))
        if errors:
            print("ordinary-route errors:")
            print("\n".join(errors))

        all_match = True
        for fixture, point, envelope, rows in entries:
            key = (fixture.top, point.label)
            expected = ordinary.get(key, [])
            print(f"FIXTURE {fixture.top} {point.label}: ordinary={len(expected)} "
                  f"Icarus={iverilog_version} Xcelium={xrun_version}")
            if len(expected) != CYCLES:
                print(f"  RUNS NO (ordinary route returned {len(expected)} cycles)")
                all_match = False
                # Still run both pinned source simulators.  There is no E
                # comparison for this point, but the source rows make the
                # refusal/timeout measurable rather than silently skipped.
                source_rows: dict[str, list[list[str]]] = {}
                for sim in simulators:
                    source = cleanroom / fixture.source
                    with tempfile.TemporaryDirectory(prefix="sv-batch-sim-") as sim_name:
                        try:
                            _, actual = run_simulator(sim, fixture, point, rows, source, Path(sim_name))
                        except RuntimeError as exc:
                            print(f"  {sim}: ERROR {exc}")
                            continue
                    source_rows[sim] = actual
                    print(f"  {sim}: {len(actual)} source cycles (no E comparison)")
                if len(source_rows) == 2:
                    left, right = (source_rows[s] for s in simulators)
                    for i, (lrow, rrow) in enumerate(zip(left, right)):
                        verdict = "MATCH" if lrow == rrow else "DIVERGE"
                        print(f"  SOURCE CYCLE {i} {verdict} {simulators[0]}={' '.join(lrow)} "
                              f"{simulators[1]}={' '.join(rrow)}")
                        if verdict == "DIVERGE":
                            all_match = False
                continue
            for sim in simulators:
                source = cleanroom / fixture.source
                with tempfile.TemporaryDirectory(prefix="sv-batch-sim-") as sim_name:
                    try:
                        sim_out, actual = run_simulator(sim, fixture, point, rows, source, Path(sim_name))
                    except RuntimeError as exc:
                        print(f"  {sim}: ERROR {exc}")
                        all_match = False
                        continue
                print(f"  {sim}: {len(actual)} source cycles")
                for i, (e_row, s_row) in enumerate(zip(expected, actual)):
                    verdict = "MATCH" if e_row == s_row else "DIVERGE"
                    print(f"  CYCLE {i} {sim} {verdict} E={' '.join(e_row)} S={' '.join(s_row)}")
                    if verdict == "DIVERGE":
                        all_match = False
                if len(actual) != CYCLES:
                    print(f"  CYCLE COUNT {sim} DIVERGE expected={CYCLES} actual={len(actual)}")
                    all_match = False
        return 0 if all_match else 1


if __name__ == "__main__":
    raise SystemExit(main())
