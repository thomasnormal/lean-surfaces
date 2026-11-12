// Clean-room canonical-E fixture for parser-retained unsized x/z conversions.
module unsized_xz_conversion_canonical_e #(parameter int N = 40) (
  output logic [N-1:0] qx,
  output logic [N-1:0] qz,
  output logic [N-1:0] qhx,
  output logic [N-1:0] qhz
);
  assign qx  = 'bx;
  assign qz  = 'bz;
  assign qhx = 'hx0;
  assign qhz = 'hz1;
endmodule
