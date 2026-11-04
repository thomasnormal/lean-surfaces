// A fixed internal wire array with one plain driver per cell is net-as-variable safe.
module unpacked_internal_net_fixed (
  input  logic [3:0] a,
  output logic [3:0] y
);
  wire logic [3:0] mem [0:1];
  assign mem[0] = a;
  assign mem[1] = ~a;
  assign y = mem[0] ^ mem[1];
endmodule
