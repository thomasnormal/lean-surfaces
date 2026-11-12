module unsized_xz_parametric_e_tb;
  wire [7:0] qx8, qz8;
  wire [15:0] qw8;
  wire [3:0] qn8;
  wire [39:0] qx40, qz40;
  wire [47:0] qw40;
  wire [3:0] qn40;

  unsized_xz_parametric_e #(.N(8)) d8
    (.qx(qx8), .qz(qz8), .qw(qw8), .qn(qn8));
  unsized_xz_parametric_e #(.N(40)) d40
    (.qx(qx40), .qz(qz40), .qw(qw40), .qn(qn40));

  initial begin
    #1;
    $display("ROW N8 qx=%b qz=%b qw=%b qn=%b", qx8, qz8, qw8, qn8);
    $display("ROW N40 qx=%b qz=%b qw=%b qn=%b", qx40, qz40, qw40, qn40);
    $finish;
  end
endmodule
