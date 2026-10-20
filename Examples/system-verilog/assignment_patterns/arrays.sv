module top;
  int down [3:1] = '{1:10, 2:20, 3:30};
  int up [-1:1] = '{-1:7, 0:8, 1:9};
  typedef struct packed { logic [3:0] a; logic [3:0] b; } pair_t;
  pair_t cells [2:1] = '{1:'{4'h1, 4'h2}, 2:'{a:4'h3, b:4'h4}};
  initial begin
    $display("arrays %0d %0d %0d %0d %0d %0d %h %h",
      down[3], down[2], down[1], up[-1], up[0], up[1], cells[2], cells[1]);
    down = '{1:40, 2:50, 3:60};
    cells = '{1:'{4'h5, 4'h6}, 2:'{4'h7, 4'h8}};
    $display("updated %0d %0d %0d %h %h", down[3], down[2], down[1], cells[2], cells[1]);
    $finish;
  end
endmodule
