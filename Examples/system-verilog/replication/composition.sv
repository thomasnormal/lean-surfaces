module top;
  typedef struct packed { logic [3:0] a; logic [3:0] b; } pair_t;
  logic [1:0] source;
  pair_t pair;
  logic [3:0] values [0:1];
  initial begin
    source = 2'b10;
    pair = '{a:{2{source}}, b:{2{2'bxz}}};
    values = '{default:{2{source}}};
    case ({2{source}})
      {2{2'b10}}: $display("composed %h %b %h %h", pair.a, pair.b, values[0], values[1]);
      default: $display("unexpected");
    endcase
    $finish;
  end
endmodule
