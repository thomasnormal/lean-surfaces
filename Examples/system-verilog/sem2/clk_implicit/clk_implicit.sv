// Clean-room Sem2 guard witness: data-driven event control is not run2 timing.
module clk_implicit(input logic a, d, output logic q);
  always @(a) q <= d;
endmodule
