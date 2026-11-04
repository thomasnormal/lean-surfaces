program leaf;
  initial $display("program");
endprogram
module top;
  leaf child();
  initial begin #1;$finish;end
endmodule
