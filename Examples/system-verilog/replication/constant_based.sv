module top;
  localparam logic [84:0] VALUE = 'hx;
  if ('hx === 85'hx) begin : selected
    initial begin $display("constant %h", VALUE); $finish; end
  end else begin : wrong
    initial begin $display("unexpected"); $finish; end
  end
endmodule
