/*
:name: unpacked_struct_initializers
:description: IEEE 1800-2023 Section 7.2 -- positional and keyed aggregate
  initializers flatten into direct integral field cells.
:tags: 7.2
:type: simulation
*/
module top;
  typedef struct {
    bit [3:0] bits;
    int count;
  } item_t;

  item_t positional = '{4'b1x0z, 3};
  item_t keyed = '{count: 7, bits: 4'ha};

  initial begin
    if (positional.bits === 4'b1000 && positional.count == 3 &&
        keyed.bits == 4'ha && keyed.count == 7)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
