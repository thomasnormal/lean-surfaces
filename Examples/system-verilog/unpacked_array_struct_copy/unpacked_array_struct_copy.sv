/*
:name: unpacked_array_struct_copy
:description: IEEE 1800-2023 7.6 — compatible fixed arrays of integral structs copy by value
:tags: 7.6
:type: simulation
*/
module top;
  typedef struct { int id; int value; } item_t;
  initial begin
    item_t source [0:1];
    item_t target [0:1];
    source[0] = '{id: 1, value: 10};
    source[1] = '{id: 2, value: 20};
    target = source;
    source[0].value = 99;
    source[1].id = 9;
    if (target[0].id == 1 && target[0].value == 10 &&
        target[1].id == 2 && target[1].value == 20)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
