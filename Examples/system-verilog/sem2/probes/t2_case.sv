// Phase-2 probe: enum-typed state variable, plain case over enum labels
// (async active-low reset), and fifo-style `unique case (1'b1)` with
// signal-valued items.
module t2_case (
    input  logic clk, rst_n,
    input  logic [1:0] op,
    input  logic go,
    output logic [1:0] st_o,
    output logic [2:0] pr_o
);
  typedef enum logic [1:0] { S0, S1, S2 } state_e;
  state_e st;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) st <= S0;
    else begin
      case (st)
        S0: if (go) st <= S1;
        S1: st <= S2;
        S2: st <= S0;
        default: st <= S0;
      endcase
    end
  end
  assign st_o = st;
  always_comb begin
    unique case (1'b1)
      op[0]: pr_o = 3'd1;
      op[1]: pr_o = 3'd2;
      default: pr_o = 3'd4;
    endcase
  end
endmodule
