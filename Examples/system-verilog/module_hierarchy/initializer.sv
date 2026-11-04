module leaf;
  int value=top.seed;
endmodule
module top;
  int seed=7;
  leaf child();
  initial begin #1;$display("initializer %0d",child.value);$finish;end
endmodule
