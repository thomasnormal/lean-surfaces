// A one-hot decoder as ONE always_comb in the "default, then override one
// bit" style: y = '0, then a case writes a single constant bit of y. The
// symbolic execution splices each bit write into y's default
// (`Expr2.splice`); `LeanModels.Sv.Comb2ProcExample.decDesign` is the
// hand-built twin (`dec_terminates`, `dec_correct`).
module onehot_dec (
  input  logic [1:0] sel,
  input  logic       en,
  output logic [3:0] y
);
  always_comb begin
    y = 4'b0000;
    if (en) begin
      case (sel)
        2'd0: y[0] = 1'b1;
        2'd1: y[1] = 1'b1;
        2'd2: y[2] = 1'b1;
        2'd3: y[3] = 1'b1;
      endcase
    end
  end
endmodule
