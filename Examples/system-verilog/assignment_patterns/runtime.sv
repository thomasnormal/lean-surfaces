module top;
  logic source;
  logic [3:0] bus;
  typedef struct packed { logic [3:0] a; logic [3:0] b; } pair_t;
  pair_t pair = '{4'h2, 4'h9};
  initial begin
    source = 1'b1;
    bus = '{3:source, 2:1'bx, 1:1'bz, 0:1'b1};
    pair = '{a:pair.b, b:pair.a};
    $display("live %b %h %h", bus, pair.a, pair.b);
    bus <= '{3:source, 2:1'bx, 1:1'bz, 0:1'b1};
    source = 1'b0;
    #1;
    $display("captured %b %b", bus, source);
    $finish;
  end
endmodule
