// `>>>` of an unsigned operand: a logical shift (IEEE 1800-2023 §11.4.10), which the tactics do not read as `>>>` yet.
module asr_unsigned #(parameter integer W = 8) (
  input  logic [W-1:0] c,
  output logic [W-1:0] y
);
  assign y = c >>> 1;
endmodule
