// REFUSED by the clock discipline (`Clock:data-read`, WP-Q0): the clock is
// read as data. `clk` is an input port and clocks the register, but the
// continuous assignment `y = clk ^ a` uses its value, which the model never
// gives a meaning (it is whatever the stimulus entry binds; a simulator sees
// the waveform).
module clk_data (
  input  logic clk, a, d,
  output logic y, q
);
  always_ff @(posedge clk) q <= d;
  assign y = clk ^ a;
endmodule
