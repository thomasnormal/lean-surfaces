/*
:name: unpacked_struct_copy
:description: IEEE 1800-2023 Section 7.2.2 -- an integral unpacked struct
  assignment copies each field's value.
:tags: 7.2.2
:type: simulation
*/
typedef struct {
  int count;
  bit [3:0] code;
} payload_t;

module top;
  payload_t source, target;
  initial begin
    source.count = 42;
    source.code = 4'hA;
    target = source;
    if (target.count == 42 && target.code == 4'hA)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
