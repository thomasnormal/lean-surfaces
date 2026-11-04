module case_equality (
  input logic clk,
  input logic [1:0] value,
  output logic eq,
  output logic neq
);
  always_ff @(posedge clk) begin
    eq = value === 2'b1x;
    neq = value !== 2'b1x;
  end
endmodule
