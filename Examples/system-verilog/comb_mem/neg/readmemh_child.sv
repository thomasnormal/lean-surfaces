// A ROM loaded at time zero by `$readmemh` inside a CHILD module, the parent reading it through the child's output port.
module rom4 (
  input logic [1:0] addr,
  output logic [7:0] q
);
  logic [7:0] rom [0:3];
  initial $readmemh("rom.hex", rom);
  assign q = rom[addr];
endmodule
module readmemh_child (
  input logic [1:0] a,
  output logic [7:0] y
);
  rom4 u(.addr(a), .q(y));
endmodule
