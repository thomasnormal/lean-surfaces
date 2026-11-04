// Part-select writes that together cover `t` before a whole read (ADMITTED).
// Admitted by the always_comb self-read guard (LeanModels/Sv/CombGuard2.lean).
module acg_part_ok (
  input  logic [1:0] a, b,
  output logic [3:0] y
);
  logic [3:0] t;
  always_comb begin
    t[1:0] = a;
    t[3:2] = b;
    y = ~t;
  end
endmodule
