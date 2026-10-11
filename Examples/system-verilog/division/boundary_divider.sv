module boundary_divider #(
  parameter int W = 8
) (
  input logic [W-1:0] value,
  output logic [31:0] concat_quotient,
  output logic [31:0] repl_quotient,
  output logic [31:0] reduce_quotient,
  output logic [31:0] unsigned_cast_quotient,
  output logic [31:0] signed_cast_quotient
);
  assign concat_quotient = {(-$signed(value) - 4'sh8)} / 8'd2;
  assign repl_quotient = {2{(-$signed(value) - 4'sh8)}} / 8'd2;
  assign reduce_quotient = (^(-$signed(value) - 4'sh8)) / 1'b1;
  assign unsigned_cast_quotient = $unsigned(-$signed(value) - 4'sh8) / 8'd2;
  assign signed_cast_quotient = $signed(-$signed(value) - 4'sh8) / 8'sd2;
endmodule
// REFERENCE: b475814fae975196878667de independent-simulator 2026-10-11T20:30:09Z
