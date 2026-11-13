// Clean-room canonical-E row: casez/casex wildcard selection beside memory.
module always_comb_wildcard_case_memory_canonical_e #(parameter integer W = 4) (
    input logic [1:0] sel,
    input logic [W-1:0] d,
    output logic [W-1:0] qz, output logic [W-1:0] qx
);
    logic [W-1:0] mem [0:1];
    initial begin
      mem[0] = 4'h3;
      mem[1] = 4'h7;
    end
    always_comb begin
      casez (sel)
        2'b0?: qz = mem[0];
        2'b1?: qz = mem[1];
        default: qz = d;
      endcase
      casex (sel)
        2'b0?: qx = mem[0];
        2'b1?: qx = mem[1];
        default: qx = d;
      endcase
    end
endmodule
