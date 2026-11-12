// Clean-room canonical-E fixture for unsized x/z literals in a parameter
// family.  The parser keeps each source literal until the concrete context
// width is known; IEEE 1800-2023 §5.7.1 truncates low bits or extends the
// literal's most-significant x/z bit.
module unsized_xz_parametric_e #(parameter int N = 8) (
  output logic [N-1:0] qx,
  output logic [N-1:0] qz,
  output logic [N+7:0] qw,
  output logic [3:0] qn
);
  assign qx = 'bx;
  assign qz = 'hz1;
  assign qw = 'hz1;
  assign qn = 'hz1;
endmodule
