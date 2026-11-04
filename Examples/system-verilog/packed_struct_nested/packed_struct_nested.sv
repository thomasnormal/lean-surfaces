/*
:name: packed_struct_nested
:description: §7.2.1 — nested packed-struct field windows
:tags: 7.2.1
:type: simulation
*/
typedef struct packed { bit [3:0] x; bit [3:0] y; } inner_t;
module top;
  struct packed {
    inner_t top_half;
    inner_t bot_half;
  } s;
  bit [15:0] v;
  initial begin
    s.top_half.x = 4'h1;
    s.top_half.y = 4'h2;
    s.bot_half.x = 4'h3;
    s.bot_half.y = 4'h4;
    v = s;
    if (v === 16'h1234)
      $display("PASS");
    else
      $display("FAIL %h", v);
    $finish;
  end
endmodule
