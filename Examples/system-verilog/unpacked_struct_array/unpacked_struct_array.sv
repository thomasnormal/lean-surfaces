/*
:name: unpacked_struct_array
:description: IEEE 1800-2023 Section 7.2 -- fixed arrays of shallow unpacked integral structs flatten to field cells.
:tags: 7.2
:type: simulation
*/
module top;
  typedef struct {
    bit [3:0] bits;
    struct {
      int count;
      bit valid;
    } meta;
  } item_t;
  item_t values [0:1];

  initial begin
    values[0].bits = 4'ha;
    values[1].meta.count = 3;
    values[1].meta.valid = 1;
    if (values[0].bits == 4'ha && values[1].meta.count == 3 &&
        values[1].meta.valid &&
        values[0].meta.count == 0 && values[1].bits == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
