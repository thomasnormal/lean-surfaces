module top;
  logic signed [3:0] signed_narrow;
  logic [3:0] unsigned_narrow;
  logic signed [7:0] signed_wide;
  logic [7:0] unsigned_wide;

  initial begin
    signed_narrow = 4'sb1001;
    unsigned_narrow = 4'b1001;
    signed_wide = signed_narrow;
    unsigned_wide = signed_narrow;
    $display("signed-source=[%b][%b]", signed_wide, unsigned_wide);
    signed_wide = unsigned_narrow;
    unsigned_wide = unsigned_narrow;
    $display("unsigned-source=[%b][%b]", signed_wide, unsigned_wide);
    signed_wide = signed_narrow + 4'sd1;
    unsigned_wide = signed_narrow + 4'd1;
    $display("signed-mixed-add=[%b][%b]", signed_wide, unsigned_wide);
    signed_wide = -signed_narrow;
    unsigned_wide = -unsigned_narrow;
    $display("negation=[%b][%b]", signed_wide, unsigned_wide);
    signed_wide = 8'sb10101011;
    signed_narrow = signed_wide;
    unsigned_narrow = signed_wide;
    $display("truncate=[%b][%b]", signed_narrow, unsigned_narrow);
    $finish;
  end
endmodule
