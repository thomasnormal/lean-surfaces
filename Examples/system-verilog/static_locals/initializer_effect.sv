module top;
 int effect;
 function int initialize();effect=7;return 3;endfunction
 initial begin
  if(0) begin : data
   static int saved=initialize();
  end
  $display("effect %0d",effect);$finish;
 end
endmodule
