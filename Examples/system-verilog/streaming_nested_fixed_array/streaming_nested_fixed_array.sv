/*
:name: streaming_nested_fixed_array
:description: IEEE 1800-2023 11.4.14.1/11.4.14.3 -- right streaming recursively unpacks a fixed multidimensional array
:tags: 11.4.14.1 11.4.14.3 streaming unpacked-array recursive
:type: simulation
*/
module top;
  int grid[2][2];

  initial begin
    {>> {grid}} = 128'h0102_0304_0506_0708_1112_1314_1516_1718;

    if (grid[0][0] !== 32'h0102_0304) begin
      $display("FAIL grid[0][0]=%08h", grid[0][0]);
      $finish;
    end
    if (grid[0][1] !== 32'h0506_0708) begin
      $display("FAIL grid[0][1]=%08h", grid[0][1]);
      $finish;
    end
    if (grid[1][0] !== 32'h1112_1314) begin
      $display("FAIL grid[1][0]=%08h", grid[1][0]);
      $finish;
    end
    if (grid[1][1] !== 32'h1516_1718) begin
      $display("FAIL grid[1][1]=%08h", grid[1][1]);
      $finish;
    end
    $display("PASS");
    $finish;
  end
endmodule
