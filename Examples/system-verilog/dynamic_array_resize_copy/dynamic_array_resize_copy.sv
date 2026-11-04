/*
:name: dynamic_array_resize_copy
:description: IEEE 1800-2023 Section 7.5.1 -- a finite scalar dynamic-array
  resize with a distinct source copies cells and pads new elements by default.
:tags: 7.5.1
:type: simulation
*/
module top;
  initial begin
    int src[];
    int dst[];
    logic four_src[];
    logic four_dst[];
    src = new[3];
    src[0] = 5;
    src[1] = 6;
    src[2] = 7;
    dst = new[5](src);
    if (dst[0] == 5 && dst[1] == 6 && dst[2] == 7 &&
        dst[3] == 0 && dst[4] == 0)
      begin
        four_src = new[1];
        four_src[0] = 1'b1;
        four_dst = new[2](four_src);
        if (four_dst[0] === 1'b1 && four_dst[1] === 1'bx)
          $display("PASS");
        else
          $display("FAIL");
      end
    else
      $display("FAIL");
    $finish;
  end
endmodule
