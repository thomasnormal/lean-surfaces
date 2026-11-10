// A ROM loaded by `$readmemh` from a file named by a string parameter (the clean-room repro, verbatim below).
module readmemh_rom #(parameter string FILE = "coeff.mem") (
    input wire [3:0] a,
    output wire [7:0] y
);
    reg [7:0] rom [0:15];
    initial $readmemh(FILE, rom);
    assign y = rom[a];
endmodule
