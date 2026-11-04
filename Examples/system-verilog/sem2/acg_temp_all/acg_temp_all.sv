// A temporary written on every path before it is read (ADMITTED).
// Admitted by the always_comb self-read guard (LeanModels/Sv/CombGuard2.lean).
module acg_temp_all (
  input  logic       c,
  input  logic [1:0] a, b,
  output logic [1:0] y
);
  logic [1:0] t;
  always_comb begin
    if (c) t = a;
    else t = b;
    y = t;
  end
endmodule
