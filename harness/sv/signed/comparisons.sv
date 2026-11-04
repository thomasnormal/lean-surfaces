module top;
  logic signed [3:0] negative_narrow;
  logic signed [7:0] positive_wide;
  logic signed [7:0] negative_wide;
  logic [7:0] unsigned_wide;
  logic [3:0] unsigned_narrow;

  initial begin
    negative_narrow = -4'sd1;
    positive_wide = 8'sd1;
    negative_wide = -8'sd2;
    unsigned_wide = 8'd1;
    unsigned_narrow = 4'd1;
    $display("signed=[%b][%b][%b][%b]", negative_narrow < positive_wide,
             negative_narrow > positive_wide,
             negative_narrow <= positive_wide,
             negative_narrow >= positive_wide);
    $display("negative=[%b][%b][%b][%b]", negative_wide < negative_narrow,
             negative_wide > negative_narrow,
             negative_wide <= negative_narrow,
             negative_wide >= negative_narrow);
    $display("mixed=[%b][%b][%b][%b]", negative_narrow < unsigned_wide,
             negative_narrow > unsigned_wide,
             negative_narrow < unsigned_narrow,
             negative_narrow > unsigned_narrow);
    $display("equal=[%b][%b]", negative_narrow == negative_wide,
             negative_narrow != negative_wide);
    $finish;
  end
endmodule
