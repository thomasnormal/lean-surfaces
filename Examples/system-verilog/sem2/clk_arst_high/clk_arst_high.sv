// Clean-room active-high asynchronous reset witness.
module clk_arst_high #(parameter int N = 4) (
  input logic clk, rst, en,
  input logic [N-1:0] d,
  output logic [N-1:0] q
);
  always_ff @(posedge clk or posedge rst)
    if (rst) q <= '0;
    else if (en) q <= d;
endmodule
