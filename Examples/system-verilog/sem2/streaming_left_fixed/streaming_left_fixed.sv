// Pure bit and chunk reorderings share the ordinary packed-select evaluator.
module streaming_left_fixed (
    input logic [9:0] source,
    output logic [9:0] bit_order, chunks4, same, procedural, split_chunks,
    output logic [11:0] padded
);
  assign bit_order = {<< {source}};
  assign chunks4 = {<< 4 {source}};
  assign split_chunks = {<< 4 {source[9:6], source[5:0]}};
  assign same = {<< 16 {source}};
  assign padded = {<< 3 {source}};
  always_comb procedural = {<< 3 {source}};
endmodule
