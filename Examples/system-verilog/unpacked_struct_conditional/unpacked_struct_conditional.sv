/*
:name: unpacked_struct_conditional
:description: IEEE 1800-2023 11.2.2 — conditional unpacked-struct assignment copies fields
:tags: 11.2.2
:type: simulation
*/
module top;
  typedef struct { int count; byte code; } item_t;
  item_t left, right, selected;
  logic choose;
  initial begin
    left = '{count: 7, code: 8'h41};
    right = '{count: 3, code: 8'h5a};
    choose = 1'b0;
    selected = choose ? left : right;
    if (selected.count == 3 && selected.code == 8'h5a)
      $display("PASS1");
    else
      $display("FAIL1");
    choose = 1'b1;
    selected = choose ? left : right;
    if (selected.count == 7 && selected.code == 8'h41)
      $display("PASS2");
    else
      $display("FAIL2");
    $finish;
  end
endmodule
