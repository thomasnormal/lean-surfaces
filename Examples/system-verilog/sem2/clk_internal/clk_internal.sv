// REFUSED by the clock discipline (`Clock:source`, WP-Q0): an internal net
// as the clock, here a plain rename of the input `sel`. The model runs the
// register in every cycle whatever `sel` does; a simulator captures only on
// the rising edges of `sel`.
module clk_internal (
  input  logic sel, d,
  output logic q
);
  logic ck;
  assign ck = sel;
  always_ff @(posedge ck) q <= d;
endmodule
