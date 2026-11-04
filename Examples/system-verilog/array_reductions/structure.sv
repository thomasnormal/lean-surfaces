module worker #(parameter int B=3);
  logic [7:0] cells[-2:0];
  initial begin cells='{B,2,1}; end
endmodule
module top;
  worker #(.B(8)) u();
  worker #(.B(5)) v();
  typedef struct packed {logic [3:0] hi;logic [3:0] lo;} pair_t;
  pair_t pairs[2];
  int item;
  initial begin
    pairs='{8'h12,8'h34};
    item=7;
    #1;
    $display("instances %0d %0d",u.cells.sum(),v.cells.sum());
    $display("fields %0d %0d",pairs.sum(x) with (int'(x.lo)),pairs.product(x) with (int'(x.hi)+item));
    $finish;
  end
endmodule
