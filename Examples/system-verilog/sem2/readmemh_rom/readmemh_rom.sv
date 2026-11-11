module readmemh_rom (
  input logic [1:0] addr,
  output logic [7:0] q
);
  logic [7:0] rom [0:3];
  initial begin
    $readmemh("rom.hex", rom);
  end
  assign q = rom[addr];
endmodule
