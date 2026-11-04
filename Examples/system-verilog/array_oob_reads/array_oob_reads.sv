/* IEEE 1800-2023 §7.4.5 element defaults for out-of-bounds reads. */
module top;
  typedef enum logic [1:0] { RED = 2'b00, GREEN = 2'b01, BLUE = 2'b10 } color_t;
  bit [7:0] bits [0:3];
  logic [7:0] logic_values [0:3];
  color_t colors [0:3];

  initial begin
    if (bits[10] === 8'h00 &&
        logic_values[10] === 8'hxx &&
        colors[10] === 2'bxx)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
