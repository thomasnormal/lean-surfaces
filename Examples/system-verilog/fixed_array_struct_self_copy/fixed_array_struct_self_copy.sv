/*
:name: fixed_array_struct_self_copy
:description: §7.4 — exact blocking self-copy of a fixed unpacked struct array
:tags: 7.4, 7.5
:type: simulation
*/
typedef struct { int id; int value; } item_t;
module top;
  item_t source [0:1];
  initial begin
    source[0].id = 7;
    source[0].value = 3;
    source[1].id = 5;
    source[1].value = 2;
    source = source;
    if (source[0].id == 7 && source[1].value == 2) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
