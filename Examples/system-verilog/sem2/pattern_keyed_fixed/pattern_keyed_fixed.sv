// Fixed packed struct assignment patterns preserve field order through Concat.
module pattern_keyed_fixed (
  input  logic [2:0] a,
  input  logic       b,
  output logic [3:0] y,
  output logic [3:0] z
);
  typedef struct packed {
    logic [2:0] x;
    logic       flag;
  } st_t;
  st_t keyed;
  st_t with_default;
  always_comb begin
    keyed = '{x: a, flag: b};
    with_default = '{x: a, default: 1'b0};
    y = keyed;
    z = with_default;
  end
endmodule
