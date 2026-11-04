/*
:name: struct_array_field_enum_default
:description: §5.10/5.11 — enum type keys in a nested struct default recurse through fixed unpacked array fields
:tags: 5.10 5.11 enum assignment-pattern unpacked-struct fixed-array
:type: simulation
*/
module top;
  typedef enum int {IDLE = 1, BUSY = 2} state_t;
  typedef struct {
    state_t states [0:1];
    int raw [0:1];
  } item_t;
  item_t item;

  initial begin
    item = '{default: '{state_t: BUSY, default: 7}};
    if (item.states[0] == BUSY && item.states[1] == BUSY &&
        item.raw[0] == 7 && item.raw[1] == 7)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
