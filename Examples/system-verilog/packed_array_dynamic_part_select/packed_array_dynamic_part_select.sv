/*
:name: packed_array_dynamic_part_select
:description: §11.5.1 — dynamic indexed part-selects on an ascending packed vector
:tags: 11.5.1
:type: simulation
*/
module top;
  logic [0:7] value;
  int i;

  initial begin
    value = 8'b0;
    i = 2;
    value[i +: 2] = 2'b10;
    if (value[i +: 2] !== 2'b10) begin
      $display("FAIL");
    end else begin
      value = 8'b0;
      i = 5;
      value[i -: 2] = 2'b10;
      if (value[i -: 2] === 2'b10)
        $display("PASS");
      else
        $display("FAIL");
    end
  end
endmodule
