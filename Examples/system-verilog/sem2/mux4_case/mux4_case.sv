// A 4-way multiplexer as ONE always_comb: a default assignment, then a case
// with a default arm. The hand-built twin
// `LeanModels.Sv.Comb2ProcExample.muxDesign` is proved to select d[sel]
// (`mux_correct`, `mux_terminates`).
module mux4_case (
  input  logic [1:0] sel,
  input  logic [3:0] d,
  output logic       y
);
  always_comb begin
    y = 1'b0;
    case (sel)
      2'd0: y = d[0];
      2'd1: y = d[1];
      2'd2: y = d[2];
      default: y = d[3];
    endcase
  end
endmodule
