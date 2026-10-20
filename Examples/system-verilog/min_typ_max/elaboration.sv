module top;
  localparam int WIDTH=(4:8:12);
  logic[WIDTH-1:0] value;
  if((0:1:0)) begin: typical
    initial begin
      value='1;
      $display("typical %0d %h",WIDTH,value);
      $finish;
    end
  end else begin: outer
    initial begin
      value='1;
      $display("outer %0d %h",WIDTH,value);
      $finish;
    end
  end
endmodule
