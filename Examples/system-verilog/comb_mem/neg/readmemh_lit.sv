// A ROM loaded at time zero by `$readmemh` from a literal file beside the source (`rom.hex`, four words), read by its address.
module readmemh_lit (
  input logic [1:0] addr,
  output logic [7:0] q
);
  logic [7:0] rom [0:3];
  initial $readmemh("rom.hex", rom);
  assign q = rom[addr];
endmodule
