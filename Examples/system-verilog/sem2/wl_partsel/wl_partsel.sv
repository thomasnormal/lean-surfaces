// WP-B2 gate 4a pin P20: constant part selects (the legacy `PartSel`). `r`: a rotation by concatenated part selects; `sw`: part-select TARGETS (a byte swap); `e`: a field; `f`: part selects of equal width under `&`; `h`: part selects whose bounds are affine in a genvar, read and written inside a generate loop (the declaration is parameter-dependent). An x/z bit inside the selected window is carried to the same place of the target; outside it, it is not seen.
module wl_partsel #(parameter int N = 4) (
  input  logic [15:0] x,
  input  logic [4*N-1:0] g,
  output logic [15:0] r,
  output logic [15:0] sw,
  output logic [4:0] e,
  output logic [7:0] f,
  output logic [4*N-1:0] h
);
  assign r = {x[8:0], x[15:9]};
  assign sw[7:0]  = x[15:8];
  assign sw[15:8] = x[7:0];
  assign e = x[14:10];
  assign f = x[15:8] & x[7:0];
  for (genvar i = 0; i < N; i++) begin : gp
    assign h[4*i+3:4*i] = ~g[4*i+3:4*i];
  end
endmodule
