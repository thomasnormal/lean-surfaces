/*
:name: oob_struct_read
:description: out-of-bounds fixed unpacked struct reads use IEEE member defaults
:tags: 7.4.5
:type: simulation
*/
module top;
  typedef struct {
    int a = 42;
    int b;
  } pair_t;
  pair_t arr[3];
  pair_t value;
  initial begin
    value = arr[10];
    if (value.a === 42 && value.b === 0) $display("PASS");
    else $display("FAIL");
  end
endmodule
