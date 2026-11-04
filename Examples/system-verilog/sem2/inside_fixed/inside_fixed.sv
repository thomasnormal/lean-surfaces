// Fixed-width symbolic inside membership reuses wildcard equality and range
// comparison nodes.  The row is verified with the explicit Verilator oracle;
// Icarus 13 rejects the source syntax at parse time.
module inside_fixed (
  input  logic [3:0] value,
  output logic       hit
);
  assign hit = value inside {4'd1, 4'd3, [4'd6:4'd7]};
endmodule
