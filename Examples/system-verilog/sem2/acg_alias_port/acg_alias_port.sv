// An always_comb in a child whose input port `i` and output port `o` are
// connected to the SAME parent variable `w` (ADMITTED by the self-read
// guard: the block reads `i` and writes `o`, different variables).
// Measured (round-3 WP4 verifier, re-measured round 4): Icarus 12.0 KEEPS
// `i` in the block's sensitivity list (`iverilog -g2012` netlist:
// `.event anyedge, i, a`, `i` a net on the variable node of `o`) but the
// write of `o` changes `i` SYNCHRONOUSLY inside the block's run, before
// the block reaches its event control, so nothing wakes it and y keeps the
// previous a. Xcelium 24.03 and Verilator 5.042 re-run the block: y = a.
// IEEE 1800-2023 §4.7/§4.8 permit both interleavings, so this is a tool
// split, not an Icarus departure from a rule; the model gives y = a and the
// Icarus trace is declared on the harness/sv/cases2.json row
// (`iverilog-comb-port-loop-sensitivity`; docs/sv-oracle-disagreements.md).
module acg_alias_port_leaf (
  input  logic [1:0] i, a,
  output logic [1:0] o, y
);
  always_comb begin
    y = i;
    o = a;
  end
endmodule

module acg_alias_port (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] w;
  acg_alias_port_leaf u (.i(w), .a(a), .o(w), .y(y));
endmodule
