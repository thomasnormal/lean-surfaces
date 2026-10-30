// REFUSED by the clock discipline (`Clock:source`, WP-Q0): a REGISTER used as
// a clock (a divide-by-two). The second flop's clock `div` is itself clocked
// logic; the model would tick it in every cycle.
module clk_reg (
  input  logic clk, d,
  output logic q
);
  logic div;
  always_ff @(posedge clk) div <= ~div;
  always_ff @(posedge div) q <= d;
endmodule
