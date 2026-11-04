/*
:name: unpacked_struct_integral_fields
:description: IEEE 1800-2023 Section 7.2 -- an untagged unpacked struct with integral fields has field lvalues.
:tags: 7.2
:type: simulation
*/
module top;
  typedef struct {
    int count;
    bit [7:0] mask;
  } item_t;
  item_t item;

  initial begin
    item.count = 3;
    item.mask = 5;
    item.count += 4;
    item.mask <<= 1;
    if (item.count == 7 && item.mask == 8'd10)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
