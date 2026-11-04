// Right-streaming sources preserve order, ignore slice size and pad at right.
module top;
  logic signed [3:0] hi;
  logic [3:0] lo;
  logic [7:0] ordered, sliced, reversed;
  logic signed [11:0] wide;
  bit [7:0] known;
  initial begin
    hi = 4'b10xz;
    lo = 4'b0110;
    ordered = {>> {hi, lo}};
    sliced = {>> 3 {hi, lo}};
    reversed = {>> 16 {lo, hi}};
    wide = {>> {hi, lo}};
    known = {>> {hi, lo}};
    $display("%b %b %b %b %b", ordered, sliced, reversed, wide, known);
    if (ordered !== 8'b10xz0110 || sliced !== ordered ||
        reversed !== 8'b011010xz || wide !== 12'b10xz01100000 ||
        known !== 8'b10000110)
      $display("FAIL");
    else
      $display("PASS");
    $finish;
  end
endmodule
