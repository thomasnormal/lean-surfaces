#!/usr/bin/env python3
"""Testbench generator for the SV phase-2 (semantic tier) differential
harness (python3 / 3.9+).

Unlike M0's gen_tb.py, port widths are NOT read from the envelope (they are
symbolic there): the Lean runner (`runner2.lean`) elaborates the design at
the case's parameter values and reports `PORT <name> <dir> <width> <signed>` lines —
the single source of truth for widths — which diff_test2.py passes in here.

Same observation conventions as M0: clock period 3 (inputs at 3k, posedge
3k+1, negedge 3k+2), stimulus applied while the clock is low, sampling in
`always @(negedge clk)` printing `CYCLE <k> <name>=%b ...` with hierarchical
`dut.<name>` references. Parameter overrides are emitted on the DUT
instantiation (`#(.LEN(32))`). The case may name its clock port (`"clock"`,
default `"clk"`); a DUT without that port still gets a pacing TB clock. Rows
whose input widths vary by parameter point may provide `stimulus_by_params`
using canonical keys such as `N=4`; the selected list is validated against
the runner's point-specific `PORT` widths.
"""

import re


class TbError(Exception):
    pass


def _port4(port):
    """Accept legacy three-field PORT tuples and signed-aware four-field ones."""
    return port if len(port) == 4 else (port[0], port[1], port[2], False)


def _decl(name, width):
    if width == 1:
        return "  logic %s;" % name
    return "  logic [%d:0] %s;" % (width - 1, name)


_ARRAY_NAME_RE = re.compile(r"^([^\[]+)((?:\[-?\d+\])+)$")


def _array_name(name):
    """Return ``(base, indices)`` for a flattened unpacked-cell name."""
    match = _ARRAY_NAME_RE.match(name)
    if match is None:
        return None
    return match.group(1), tuple(int(value) for value in
                                re.findall(r"\[(-?\d+)\]", match.group(2)))


def _array_groups(ports):
    """Group flattened one- or multi-dimensional ports back into arrays."""
    groups = {}
    for port in ports:
        name, direction, width, signed = _port4(port)
        parsed = _array_name(name)
        if parsed is not None:
            base, indices = parsed
            groups.setdefault(base, []).append(
                (indices, direction, width, signed))
    return groups


def _decl_port_groups(ports):
    groups = _array_groups(ports)
    emitted = set()
    lines = []
    for port in ports:
        name, _direction, width, signed = _port4(port)
        parsed = _array_name(name)
        if parsed is not None and parsed[0] in groups:
            base = parsed[0]
            if base in emitted:
                continue
            cells = groups[base]
            rank = len(cells[0][0])
            if (not rank or any(len(cell[0]) != rank for cell in cells)
                    or any((cell[1], cell[2], cell[3]) !=
                           (cells[0][1], cells[0][2], cells[0][3])
                           for cell in cells)):
                raise TbError("inconsistent flattened port array '%s'" % base)
            values = []
            for dimension in range(rank):
                ordered = []
                for cell in cells:
                    value = cell[0][dimension]
                    if value not in ordered:
                        ordered.append(value)
                if len(ordered) > 1:
                    step = ordered[1] - ordered[0]
                    if step not in (-1, 1) or any(
                            ordered[i] - ordered[i - 1] != step
                            for i in range(2, len(ordered))):
                        raise TbError("non-contiguous flattened port array '%s'" % base)
                values.append((ordered[0], ordered[-1]))
            if len({cell[0] for cell in cells}) != len(cells):
                raise TbError("duplicate flattened port cell in '%s'" % base)
            expected = 1
            for left, right in values:
                expected *= abs(right - left) + 1
            if expected != len(cells):
                raise TbError("sparse flattened port array '%s'" % base)
            sign = " signed" if cells[0][3] else ""
            dimensions = "".join(" [%d:%d]" % bounds for bounds in values)
            lines.append("  logic%s [%d:0] %s%s;" %
                         (sign, width - 1, base, dimensions))
            emitted.add(base)
        else:
            sign = " signed" if signed else ""
            if width == 1:
                lines.append("  logic%s %s;" % (sign, name))
            else:
                lines.append("  logic%s [%d:0] %s;" %
                             (sign, width - 1, name))
    return lines, groups


def _point_key(params):
    """Canonical key for a parameter-specific stimulus list."""
    return "(defaults)" if not params else ",".join(
        "%s=%d" % (name, value) for name, value in sorted(params.items()))


def stimulus_for_case(case):
    """Select the row stimulus, optionally by its integer parameter point."""
    by_point = case.get("stimulus_by_params")
    if by_point is None:
        return case["stimulus"]
    if not isinstance(by_point, dict):
        raise TbError("stimulus_by_params must be an object")
    key = _point_key(case.get("params", {}) or {})
    if key not in by_point:
        raise TbError("stimulus_by_params has no point '%s'" % key)
    return by_point[key]


def generate_tb2(mod_name, ports, case):
    """ports: list of (name, dir, width, signed) from the runner."""
    port_width = {p[0]: p[2] for p in ports}
    in_names = {p[0] for p in ports if p[1] == "in"}
    clock = case.get("clock", "clk")
    params = case.get("params", {}) or {}

    signals = case["signals"]
    stimulus = stimulus_for_case(case)

    for k, entry in enumerate(stimulus):
        for name, bits in entry.items():
            if name not in in_names:
                raise TbError("cycle %d: stimulus name '%s' is not an input port"
                              % (k, name))
            if name == clock:
                raise TbError("cycle %d: the clock is driven by the TB" % k)
            if len(bits) != port_width[name]:
                raise TbError("cycle %d: stimulus '%s' width %d != port width %d"
                              % (k, name, len(bits), port_width[name]))
            if any(c not in "01xz" for c in bits):
                raise TbError("cycle %d: stimulus '%s' has bad digit in %r"
                              % (k, name, bits))

    lines = []
    lines.append("// Auto-generated by harness/sv/gen_tb2.py -- case '%s', module '%s'."
                 % (case["name"], mod_name))
    lines.append("// Canonical output: 'CYCLE <k> <name>=<binary>...' per cycle,")
    lines.append("// sampled at negedge (after the posedge timestep's NBA commit).")
    lines.append("module tb;")
    lines.append("  logic %s = 1'b0;  // decl init: no time-0 transition" % clock)
    decl_lines, array_groups = _decl_port_groups(
        [p for p in ports if p[0] != clock])
    lines.extend(decl_lines)
    if params:
        ovr = ", ".join(".%s(%d)" % (k, v) for k, v in params.items())
        head = "  %s #(%s) dut (" % (mod_name, ovr)
    else:
        head = "  %s dut (" % mod_name
    emitted = set()
    connections = []
    for port in ports:
        name, _direction, _width, _signed = _port4(port)
        parsed = _array_name(name)
        if parsed is not None and parsed[0] in array_groups:
            base = parsed[0]
            if base in emitted:
                continue
            emitted.add(base)
            connections.append(".%s(%s)" % (base, base))
        else:
            connections.append(".%s(%s)" % (name, name))
    conns = ", ".join(connections)
    lines.append(head + conns + ");")
    lines.append("")
    lines.append("  integer cycle = 0;")
    fmt = "CYCLE %0d " + " ".join("%s=%%b" % n for n in signals)
    args = ", ".join(["cycle"] + ["dut.%s" % n for n in signals])
    lines.append("  always @(negedge %s) begin" % clock)
    lines.append('    $display("%s", %s);' % (fmt, args))
    lines.append("    cycle = cycle + 1;")
    lines.append("  end")
    lines.append("")
    lines.append("  initial begin")
    for k, entry in enumerate(stimulus):
        lines.append("    // cycle %d" % k)
        for name, bits in entry.items():
            lines.append("    %s = %d'b%s;" % (name, len(bits), bits))
        lines.append("    #1 %s = 1'b1;" % clock)
        lines.append("    #1 %s = 1'b0;" % clock)
        lines.append("    #1;")
    lines.append("    $finish;")
    lines.append("  end")
    lines.append("endmodule")
    return "\n".join(lines) + "\n"


def generate_multi_tb2(mod_name, ports, case):
    """Generate a testbench for an instant-list multi-clock row.

    All clocks start low.  An instant raises exactly the listed clocks at one
    timestamp, lowers them together, then prints after NBA and combinational
    settling.  Inputs are changed before the instant, and a clock's own input
    is never supplied by the row.
    """
    port_width = {p[0]: p[2] for p in ports}
    in_names = {p[0] for p in ports if p[1] == "in"}
    clock_names = {p[0] for p in ports if p[1] == "in" and p[0] in
                   {r for instant in case["instants"] for r in instant["rises"]}}
    if not clock_names:
        raise TbError("multi-clock row has no rising clock")
    signals = case["signals"]
    for k, instant in enumerate(case["instants"]):
        rises = set(instant["rises"])
        if not rises.issubset(clock_names):
            raise TbError("instant %d names a non-clock rise" % k)
        inputs = instant.get("inputs", {})
        for name, bits in inputs.items():
            if name not in in_names or name in clock_names:
                raise TbError("instant %d has invalid input '%s'" % (k, name))
            if len(bits) != port_width[name] or any(c not in "01xz" for c in bits):
                raise TbError("instant %d input '%s' has wrong bits" % (k, name))
    lines = ["// Auto-generated multi-clock instant-list testbench.", "module tb;"]
    for name in sorted(clock_names):
        lines.append("  logic %s = 1'b0;" % name)
    decl_lines, array_groups = _decl_port_groups(
        [p for p in ports if p[0] not in clock_names])
    lines.extend(decl_lines)
    params = case.get("params", {}) or {}
    if params:
        ovr = ", ".join(".%s(%d)" % (k, v) for k, v in params.items())
        head = "  %s #(%s) dut (" % (mod_name, ovr)
    else:
        head = "  %s dut (" % mod_name
    emitted = set()
    conns = []
    for port in ports:
        name = port[0]
        parsed = _array_name(name)
        if parsed is not None and parsed[0] in array_groups:
            if parsed[0] in emitted:
                continue
            emitted.add(parsed[0])
            conns.append(".%s(%s)" % (parsed[0], parsed[0]))
        else:
            conns.append(".%s(%s)" % (name, name))
    lines.append(head + ", ".join(conns) + ");")
    lines.append("  initial begin")
    for k, instant in enumerate(case["instants"]):
        for name, bits in instant.get("inputs", {}).items():
            lines.append("    %s = %d'b%s;" % (name, len(bits), bits))
        lines.append("    #1;")
        for name in sorted(set(instant["rises"])):
            lines.append("    %s = 1'b1;" % name)
        lines.append("    #1;")
        for name in sorted(set(instant["rises"])):
            lines.append("    %s = 1'b0;" % name)
        lines.append("    #1;")
        fmt = "CYCLE %d " % k + " ".join("%s=%%b" % n for n in signals)
        args = ", ".join("dut.%s" % n for n in signals)
        lines.append('    $display("%s", %s);' % (fmt, args))
    lines.extend(["    $finish;", "  end", "endmodule"])
    return "\n".join(lines) + "\n"
