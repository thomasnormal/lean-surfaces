// Packed parameter-width register; no unpacked storage.
module packed_shift_mem_e #(parameter integer N=4) (
  input logic clk, input logic v, output logic [N-1:0] q);
  logic [N-1:0] t;
  always_ff @(posedge clk) t <= {t[N-2:0], v};
  assign q = t;
endmodule
