// Clean-room wall: an always_comb process is beside unpacked memory.
module mem_always_comb_e (
  input logic [7:0] a,
  output logic [7:0] y,
  output logic [7:0] q
);
  logic [7:0] mem [0:1];
  always_comb begin
    y = a;
  end
  assign q = mem[0];
endmodule
