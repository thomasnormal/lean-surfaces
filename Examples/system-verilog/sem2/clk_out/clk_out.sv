// REFUSED by the clock discipline (`Clock:data-read`, WP-Q0): the clock is
// exported on an output port. The model reports whatever the stimulus entry
// binds to `clk`; a simulator reports the waveform.
module clk_out (
  input  logic clk, d,
  output logic q, ck_o
);
  always_ff @(posedge clk) q <= d;
  assign ck_o = clk;
endmodule
