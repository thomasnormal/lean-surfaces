// A negative declared right bound is not yet handled by dynPartPlan.
module unsigned_part_negative_range (
  input logic [3:-4] w,
  input logic [31:0] bu,
  output logic [3:0] y
);
  assign y = w[bu +: 4];
endmodule
