/*
:name: streaming_struct_source
:description: right streaming a packed struct source into unpacked array cells
:tags: 11.4.14.1
:type: simulation
*/
module top;
  typedef struct packed { int b1; int b2; } base_t;
  initial begin
    base_t s;
    int arr[2];
    s.b1 = 10;
    s.b2 = 20;
    {>> {arr[0], arr[1]}} = {>> {s}};
    if (arr[0] === 10 && arr[1] === 20) $display("PASS");
    else $display("FAIL");
  end
endmodule
