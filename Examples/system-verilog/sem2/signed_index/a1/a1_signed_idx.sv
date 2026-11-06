// ATK-1: signed bit-select index. a[i] with a 4-bit, i 2-bit SIGNED: unsigned 0..3 (ls-sv's
// toNat?), signed -2..1. ls-sv reads a[3]; SV/Yosys treat i signed -> a[-1] out of range.
// rule 3 (XSafe) admits: 2^2 * 1 = 4 <= width(a)=4.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] a;
  logic signed [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 4'b1010; i <= 2'b0; end
    else begin i <= i + 2'b1; q <= {7'b0, a[i]}; end
endmodule
