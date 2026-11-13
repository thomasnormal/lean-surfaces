// Clean-room canonical-E row: case selection beside source-shaped memory.
module always_comb_case_memory_canonical_e #(parameter integer W = 4) (
    input logic [1:0] sel,
    input logic [W-1:0] d,
    output logic [W-1:0] q
);
    logic [W-1:0] mem [0:1];

    initial begin
      mem[0] = 4'h3;
      mem[1] = 4'h7;
    end

    always_comb begin
      case (sel)
        2'd0: q = mem[0];
        2'd1: q = mem[1];
        default: q = d;
      endcase
    end
endmodule
