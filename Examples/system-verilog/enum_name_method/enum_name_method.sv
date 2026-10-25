/* §6.19.5: enum.name() returns the declaration spelling of the current member. */
// expected output: name=BLUE
module top;
  typedef enum logic [1:0] { RED = 0, GREEN = 1, BLUE = 2 } color_t;
  color_t color;
  initial begin
    color = GREEN;
    if (color == GREEN)
      $display("PASS");
    else
      $display("FAIL: %s", color.name());
    color = BLUE;
    $display("name=%s", color.name());
    color = color_t'(3);
    // expected output: unknown=''
    $display("unknown='%s'", color.name());
    $finish;
  end
endmodule
