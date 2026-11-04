module leaf #(parameter int N=4);
  logic[N-1:0] value='1;
endmodule
module top;
  for(genvar i=0;i<3;i++)begin:g
    leaf #(.N(4+i*4)) child();
  end
  initial begin
    #1;
    $display("parameters %0d %h %0d %h %0d %h",$bits(g[0].child.value),g[0].child.value,
      $bits(g[1].child.value),g[1].child.value,$bits(g[2].child.value),g[2].child.value);
    $finish;
  end
endmodule
