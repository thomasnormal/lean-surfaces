// Minimal generic witness for the current front-end boundary.
module function_source_edge_canonical_e(input logic clk, input logic d, output logic q);
  function automatic logic invert(input logic x);
    invert = !x;
  endfunction
  always_ff @(posedge clk)
    q <= invert(d);
endmodule
// The call is deliberately retained inside the edge process.
// End of witness.
