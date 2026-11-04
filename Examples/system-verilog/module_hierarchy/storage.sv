module leaf;
  typedef struct packed {logic[3:0]hi;logic[3:0]lo;} pair_t;
  pair_t record_value=8'h12;
  logic[7:0] data[1:-1]='{8'h11,8'h22,8'h33};
endmodule
module top;
  leaf a(),b();
  int index_value=0;
  initial begin
    #1;
    a.data[index_value]+=8'h10;
    b.data[-1]=a.data[index_value];
    a.record_value.hi+=4'h2;
    b.record_value.lo=a.record_value.hi;
    $display("storage %h %h %h %h",a.data[0],b.data[-1],a.record_value,b.record_value);
    $display("separate %h %h",a.data[-1],b.data[0]);
    $finish;
  end
endmodule
