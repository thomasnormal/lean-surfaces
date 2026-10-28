/*
:name: unpacked_struct_self_copy
:description: §7.2 — exact blocking self-copy of an unpacked integral struct
:tags: 7.2
:type: simulation
*/
typedef struct { int id; bit [3:0] code; } item_t;
module top;
  item_t item;
  initial begin
    item.id = 12;
    item.code = 4'hA;
    item = item;
    if (item.id == 12 && item.code == 4'hA) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
