// A `case` that writes `t` in every arm and the default before `t` is read
// (ADMITTED); the subject `s` is an input.
// Admitted by the always_comb self-read guard (LeanModels/Sv/CombGuard2.lean).
module acg_case_ok (
  input  logic [1:0] s, a, b, c,
  output logic [1:0] y
);
  logic [1:0] t;
  always_comb begin
    case (s)
      2'd0: t = a;
      2'd1: t = b;
      default: t = c;
    endcase
    y = ~t;
  end
endmodule
