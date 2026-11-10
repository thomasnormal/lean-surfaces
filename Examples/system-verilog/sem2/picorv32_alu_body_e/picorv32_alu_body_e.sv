// Clean-room source-shaped body from PicoRV32's TWO_CYCLE_ALU branch.
// The event control is retained; this item proves only one E body activation.
module picorv32_alu_body_e (
  input logic [31:0] reg_op1,
  input logic [31:0] reg_op2,
  input logic instr_sub,
  input logic instr_sra,
  input logic instr_srai,
  output logic [31:0] alu_add_sub,
  output logic alu_eq,
  output logic alu_lts,
  output logic alu_ltu,
  output logic [31:0] alu_shl,
  output logic [31:0] alu_shr
);
  always @* begin
    alu_add_sub = instr_sub ? reg_op1 - reg_op2 : reg_op1 + reg_op2;
    alu_eq = reg_op1 == reg_op2;
    alu_lts = $signed(reg_op1) < $signed(reg_op2);
    alu_ltu = reg_op1 < reg_op2;
    alu_shl = reg_op1 << reg_op2[4:0];
    alu_shr = (instr_sra || instr_srai) ? $signed(reg_op1) >>> reg_op2[4:0] : reg_op1 >> reg_op2[4:0];
  end
endmodule
