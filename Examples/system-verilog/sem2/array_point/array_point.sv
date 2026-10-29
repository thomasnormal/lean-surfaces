// A fixed unpacked array whose dimension depends on a parameter: the
// semantic tier declares one cell per DEFAULT-point element (verifier row
// `vb4`: at K = 1 the phantom `mem[1]` was written and read). Refused:
// `VariableSymbol:default-point-array`.
module array_point #(parameter int N = 3, parameter int K = 2) (
  input  logic [3:0]   d,
  input  logic         clk,
  output logic [N-1:0] q0,
  output logic [N-1:0] q1
);
  logic [N-1:0] mem [0:K-1];
  always_ff @(posedge clk) begin
    mem[0] <= d[N-1:0];
    mem[1][0] <= d[3];
  end
  assign q0 = mem[0];
  assign q1 = mem[1];
endmodule
