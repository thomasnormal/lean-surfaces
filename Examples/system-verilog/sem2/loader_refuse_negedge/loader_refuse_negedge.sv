// Clean-room loader loudness fixture for the retained event-control field: negedge.
module loader_refuse_negedge(input logic clk, rst, en, d, output logic q);
  always_ff @(negedge clk) q <= d;
endmodule
