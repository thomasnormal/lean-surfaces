module atom #(parameter int P=1);
  logic[7:0] value=P;
  initial begin #1;top.root+=P;end
endmodule
module middle;
  atom #(.P(2)) left();
  if(1)begin:g
    atom #(.P(3)) right();
  end
endmodule
module top;
  int root=0;
  middle branch();
  initial begin
    #2;
    branch.g.right.value=branch.left.value+8'h10;
    $display("nested %0d %h %h",root,branch.left.value,branch.g.right.value);
    $finish;
  end
endmodule
