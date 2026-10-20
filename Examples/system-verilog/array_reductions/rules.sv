module top;
  logic [3:0] a[3:1];
  logic signed [3:0] s[-1:1];
  int item;
  initial begin
    a = '{4'd15,4'd2,4'd3};
    s = '{-4'sd2,-4'sd3,-4'sd1};
    item = 10;
    $display("sum %0d %0d %0d",a.sum(),a.sum() with (int'(item)),a.sum(v) with (int'(v)+item));
    $display("product %0d %0d",a.product(),a.product() with (int'(item)));
    $display("signed %0d %0d",s.sum(),s.sum() with (int'(item)));
    a = '{4'b1x0z,4'b0z11,4'b1111};
    $display("bits %b %b %b",a.and(),a.or(),a.xor());
    $display("map %0d %0d",a.sum(v) with (int'($isunknown(v))),s.sum(v) with (v<0 ? 1 : 0));
    $finish;
  end
endmodule
