module top;
 logic [3:0] observed;
 initial begin : saved
  logic [3:0] count=4'd14;
  repeat(2) count=count+4'd1;
  observed=count;
  $display("certificate %0d %0d",count,observed);
  $finish;
 end
endmodule
