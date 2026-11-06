// C1: signed WRITE index q[i] with i signed 2-bit (unsigned 0..3, signed 0,1,-2,-1). ls-sv writes
// q[0..3] (toNat? unsigned); SV/Yosys treat -2,-1 as out of range -> no-op. rule 3 xsLhs admits any
// index; does fourstate check WRITE targets?
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic signed [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; i <= 2'b0; end
    else begin i <= i + 2'b1; q[i] <= 1'b1; end
endmodule
