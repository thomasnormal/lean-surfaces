module top;
  logic [3:0] a;
  logic [7:0] wide, typed, narrow;
  bit [3:0] clean;
  let twice(x)=x+x;
  let fixed(x)=4'(x)+4'(x);
  let two(x)=bit'(x);
  initial begin
    a=4'd12;
    wide=twice(a); typed=fixed(a); narrow=twice(4'(a));
    $display("width %0d %0d %0d",wide,typed,narrow);
    a=4'b1xz1; clean=two(a);
    $display("state %b %b %b",a,twice(a),clean);
    $finish;
  end
endmodule
