module int32_ashr_huge_e_tb;
  wire signed [31:0] n0,w0,o0,p0,n1,w1,o1,p1;
  int32_ashr_huge_e #(.N(8)) d0(n0,w0,o0,p0);
  int32_ashr_huge_e #(.N(16)) d1(n1,w1,o1,p1);
  initial begin #1;
    $display("ROW N=8 negative=%h width=%h one=%h parameter=%h",n0,w0,o0,p0);
    $display("ROW N=16 negative=%h width=%h one=%h parameter=%h",n1,w1,o1,p1);
    $finish;
  end
endmodule
