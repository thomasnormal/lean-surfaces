// Clean-room wall: the first continuous driver reads a signal written later.
module mem_order_e (
  input logic [7:0] a,
  output logic [7:0] y,
  output logic [7:0] q
);
  logic [7:0] mem [0:1];
  logic [7:0] b;
  assign y = b;
  assign b = a;
  assign q = mem[0];
endmodule
