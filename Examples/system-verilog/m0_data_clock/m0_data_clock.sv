module m0_data_clock (
  input logic en,
  input logic d,
  output logic q
);
  always_ff @(posedge en) q <= d;
endmodule
