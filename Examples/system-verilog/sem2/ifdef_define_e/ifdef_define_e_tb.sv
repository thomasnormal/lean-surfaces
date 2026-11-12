module ifdef_define_e_tb;
  logic a;
  wire y;
  ifdef_define_e dut(.a(a), .y(y));

  initial begin
    a = 1'b0; #1; $display("ROW zero a=%b y=%b", a, y);
    a = 1'b1; #1; $display("ROW one a=%b y=%b", a, y);
    a = 1'bx; #1; $display("ROW x a=%b y=%b", a, y);
    a = 1'bz; #1; $display("ROW z a=%b y=%b", a, y);
    $finish;
  end
endmodule
