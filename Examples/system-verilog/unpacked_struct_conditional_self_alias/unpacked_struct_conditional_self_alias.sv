/*
:name: unpacked_struct_conditional_self_alias
:description: §7.2 — conditional whole-struct assignment with a self-alias branch
:tags: 7.2, 11.4
:type: simulation
*/
typedef struct { int count; byte code; } item_t;
module top;
  item_t left, selected;
  logic choose;
  initial begin
    left.count = 17;
    left.code = 8'h2A;
    selected.count = 99;
    selected.code = 8'h63;
    choose = 0;
    selected = choose ? selected : left;
    choose = 1;
    selected = choose ? selected : left;
    if (selected.count == 17 && selected.code == 8'h2A) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
