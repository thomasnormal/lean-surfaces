module top;
  logic[7:0] minimum_source,typical_source,maximum_source,captured;
  initial begin
    minimum_source=8'h11;typical_source=8'h22;maximum_source=8'h33;
    captured=(minimum_source:typical_source:maximum_source);
    $display("before %h",captured);
    captured<=(minimum_source:typical_source:maximum_source);
    minimum_source=8'h44;typical_source=8'h55;maximum_source=8'h66;
    #1;
    $display("captured %h live %h",captured,(minimum_source:typical_source:maximum_source));
    $finish;
  end
endmodule
