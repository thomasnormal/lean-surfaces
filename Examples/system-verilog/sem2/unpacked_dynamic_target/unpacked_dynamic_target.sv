// Runtime-indexed writes to a fixed unpacked array select one flattened cell.
module unpacked_dynamic_target (
  input  logic [3:0] source,
  input  logic [1:0] index,
  output logic [3:0] out [0:1]
);
  always_comb begin
    out[0] = 4'b0000;
    out[1] = 4'b0000;
    out[index] = source;
  end
endmodule
