// Clean-room loader loudness fixture for the retained event-control field: areset.
module loader_refuse_areset(input logic clk, rst, en, d, output logic q);
  always_ff @(posedge clk or posedge rst) q <= d;
endmodule
