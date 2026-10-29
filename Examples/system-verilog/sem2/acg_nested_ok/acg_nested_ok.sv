// Nested `if`/`case` that write `t` on every path before `t` is read
// (ADMITTED).
// Admitted by the always_comb self-read guard (LeanModels/Sv/CombGuard2.lean).
module acg_nested_ok (
  input  logic       c,
  input  logic [1:0] s, a, b,
  output logic [1:0] y
);
  logic [1:0] t;
  always_comb begin
    if (c) begin
      case (s)
        2'd0: t = a;
        default: t = b;
      endcase
    end else begin
      t = a ^ b;
    end
    y = t + 2'd1;
  end
endmodule
