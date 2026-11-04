// Clean-room loader loudness fixture for the retained event-control field: iff.
module loader_refuse_iff(input logic clk, rst, en, d, output logic q);
  always_ff @(posedge clk iff en) q <= d;
endmodule
