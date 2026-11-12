// Clean-room receipt: a generated part-select call to a 5-bit automatic
// function with a local temporary, a complete unique case, a function-name
// default, and an explicit return.
module function_generated_large_case(input logic [64:0] a, output logic [64:0] y);
  function automatic logic [4:0] lookup5(input logic [4:0] x);
    begin
      logic [4:0] t;
      unique case (x)
        5'h00: t = 5'h1f;
        5'h01: t = 5'h1e;
        5'h02: t = 5'h1d;
        5'h03: t = 5'h1c;
        5'h04: t = 5'h1b;
        5'h05: t = 5'h1a;
        5'h06: t = 5'h19;
        5'h07: t = 5'h18;
        5'h08: t = 5'h17;
        5'h09: t = 5'h16;
        5'h0a: t = 5'h15;
        5'h0b: t = 5'h14;
        5'h0c: t = 5'h13;
        5'h0d: t = 5'h12;
        5'h0e: t = 5'h11;
        5'h0f: t = 5'h10;
        5'h10: t = 5'h0f;
        5'h11: t = 5'h0e;
        5'h12: t = 5'h0d;
        5'h13: t = 5'h0c;
        5'h14: t = 5'h0b;
        5'h15: t = 5'h0a;
        5'h16: t = 5'h09;
        5'h17: t = 5'h08;
        5'h18: t = 5'h07;
        5'h19: t = 5'h06;
        5'h1a: t = 5'h05;
        5'h1b: t = 5'h04;
        5'h1c: t = 5'h03;
        5'h1d: t = 5'h02;
        5'h1e: t = 5'h01;
        5'h1f: t = 5'h00;
        default: lookup5 = 5'h00;
      endcase
      return t;
    end
  endfunction
  genvar i;
  generate for (i = 0; i < 13; i += 1) begin : g
    assign y[5*i +: 5] = lookup5(a[5*i +: 5]);
  end endgenerate
endmodule
