module top;
  int a[2]='{1,2};
  int b[2]='{3,4};
  int x,z;
  initial begin
    x=100;z=200;
    $display("nested %0d %0d %0d",a.sum(x) with (b.sum(z) with (z+x)),x,z);
    b[0]=10;
    $display("live-with %0d",a.sum(v) with (v+b[0]));
    $finish;
  end
endmodule
