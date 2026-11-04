module top;
  logic [1:0] values[16] = '{2'b00,2'b01,2'b0x,2'b0z,
    2'b10,2'b11,2'b1x,2'b1z,2'bx0,2'bx1,2'bxx,2'bxz,
    2'bz0,2'bz1,2'bzx,2'bzz};
  logic [15:0] zmatches, xmatches;
  int i,j;
  initial begin
    for(i=0;i<16;i++) begin
      zmatches=0;
      xmatches=0;
      for(j=0;j<16;j++) begin
        casez(values[i]) values[j]: zmatches[j]=1; endcase
        casex(values[i]) values[j]: xmatches[j]=1; endcase
      end
      $display("row %b z %h x %h",values[i],zmatches,xmatches);
    end
    $finish;
  end
endmodule
