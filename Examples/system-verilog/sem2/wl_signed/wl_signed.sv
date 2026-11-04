// WP-B2 pin P8: signed comparison and sign extension. The symbolic tier REFUSES signed ports (`PortSymbol:signed`), so this is a refusal row; the Xcelium trace is quoted in `measured`.
module wl_signed (
  input  logic signed [3:0] sa, sb,
  input  logic [3:0] ua,
  output logic lt_ss, lt_su,
  output logic signed [4:0] s5,
  output logic [4:0] u5,
  output logic signed [3:0] sh_r
);
  assign lt_ss = sa < sb;
  assign lt_su = sa < ua;
  assign s5 = sa + sb;
  assign u5 = sa + sb;
  assign sh_r = sa >>> 1;
endmodule
