// A FIXED-size unpacked array whose cells are written at a GENVAR index, one stage per generate iteration.
module cell_genvar #(parameter integer W = 8) (
    input logic [W-1:0] x,
    output logic [W-1:0] y
);
    logic [W-1:0] stage [0:3];
    assign stage[0] = x;
    for (genvar i = 0; i < 3; i++) begin : g
      assign stage[i+1] = ~stage[i];
    end
    assign y = stage[3];
endmodule
