// Source-order streams use the same packed concatenation in both processes.
module streaming_pack_fixed (
    input logic [3:0] hi, lo,
    output logic [7:0] ordered, sliced,
    output logic [11:0] wide, procedural_wide
);
  assign ordered = {>> {hi, lo}};
  assign sliced = {>> 3 {hi, lo}};
  assign wide = {>> {lo, hi}};
  always_comb procedural_wide = {>> 16 {hi, lo}};
endmodule
