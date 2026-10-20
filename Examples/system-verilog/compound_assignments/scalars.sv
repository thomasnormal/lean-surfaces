module top;
  logic [3:0] narrow;
  logic signed [7:0] signed_value;
  logic [7:0] value;
  initial begin
    narrow=7; narrow+=32'h11; narrow*=32'h3;
    $display("wide %h",narrow);
    signed_value=-128; signed_value/=8'sd3;
    $write("signed %0d ",signed_value);
    signed_value%=8'sd5; signed_value>>>=1;
    $display("%0d",signed_value);
    value=8'h54; value+=8'h3; value-=8'h2; value*=8'h2;
    value/=8'h5; value%=8'h7; value|=8'ha0;
    value&=8'hf3; value^=8'h31; value<<=1; value>>=1; value<<<=1; value>>>=1;
    $display("operators %h",value);
    $finish;
  end
endmodule
