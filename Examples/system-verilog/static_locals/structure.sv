module leaf;
 initial begin : data
  logic [3:0] cells[1:0]='{4'd2,4'd3};
  typedef struct packed {logic[3:0] hi,lo;} pair_t;
  pair_t pair=8'h12;
  #2;
  cells[1]=cells[1]+1;
 end
endmodule
module top;
 leaf left();leaf right();
 initial begin
  $display("initial %0d %0d %h",left.data.cells[1],right.data.cells[0],left.data.pair);
  #1;left.data.cells[1]=9;right.data.pair.lo=7;
  #2;$display("instances %0d %0d %h",left.data.cells[1],right.data.cells[1],right.data.pair);
  $finish;
 end
endmodule
