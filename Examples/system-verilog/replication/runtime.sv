module top;
  logic [1:0] source;
  logic [5:0] bus;
  logic [5:0] live;
  initial begin
    source = 2'bxz;
    bus = {3{source}};
    $display("before %b", bus);
    bus <= {3{source}};
    source = 2'b10;
    #1;
    live = {3{source}};
    $display("after %b %b", bus, live);
    $finish;
  end
endmodule
