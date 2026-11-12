module int32_const_overflow_e_tb;
  logic [31:0] k0, s0, a0, u0, k1, s1, a1, u1;
  int32_const_overflow_e #(.N(10000)) d0(
    .k_out(k0), .s_out(s0), .a_out(a0), .u_out(u0));
  int32_const_overflow_e #(.N(8)) d1(
    .k_out(k1), .s_out(s1), .a_out(a1), .u_out(u1));
  initial begin
    #1;
    $display("ROW default N=10000 k=%0d s=%0d a=%0d u=%0d kh=%h sh=%h ah=%h uh=%h",
      $signed(k0), $signed(s0), $signed(a0), $signed(u0), k0, s0, a0, u0);
    $display("ROW override N=8 k=%0d s=%0d a=%0d u=%0d kh=%h sh=%h ah=%h uh=%h",
      $signed(k1), $signed(s1), $signed(a1), $signed(u1), k1, s1, a1, u1);
    $finish;
  end
endmodule
