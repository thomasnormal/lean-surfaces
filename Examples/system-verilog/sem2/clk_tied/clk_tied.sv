// REFUSED by the clock discipline (`Clock:source`, WP-Q0): the clock is tied
// to a constant. The model captured `a & b` every cycle; a simulator sees no
// edge (y stays x), and Yosys drops the flip-flop (`assign y = 1'hx`, 0 GE).
module clk_tied (
  input  logic a, b,
  output logic y
);
  logic clk;
  assign clk = 1'b0;
  always_ff @(posedge clk) y <= a & b;
endmodule
