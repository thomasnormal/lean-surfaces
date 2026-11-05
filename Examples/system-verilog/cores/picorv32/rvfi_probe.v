`timescale 1ns/1ps

// Clean-room witness harness for YosysHQ/picorv32.  The pinned RTL is kept
// outside this repository; the README gives the exact compile command.
module tb_picorv32_rvfi;
  reg clk = 0;
  always #5 clk = ~clk;
  reg resetn = 0;
  wire trap;
  wire mem_valid, mem_instr;
  reg mem_ready = 1;
  wire [31:0] mem_addr, mem_wdata;
  wire [3:0] mem_wstrb;
  reg [31:0] mem_rdata;
  reg [31:0] mem [0:255];
  reg [31:0] mem_index;
  integer i;

  wire mem_la_read, mem_la_write;
  wire [31:0] mem_la_addr, mem_la_wdata;
  wire [3:0] mem_la_wstrb;
  wire rvfi_valid, rvfi_trap, rvfi_halt, rvfi_intr;
  wire [63:0] rvfi_order;
  wire [31:0] rvfi_insn, rvfi_rs1_rdata, rvfi_rs2_rdata, rvfi_rd_wdata;
  wire [31:0] rvfi_pc_rdata, rvfi_pc_wdata, rvfi_mem_addr;
  wire [31:0] rvfi_mem_rdata, rvfi_mem_wdata;
  wire [1:0] rvfi_mode, rvfi_ixl;
  wire [4:0] rvfi_rs1_addr, rvfi_rs2_addr, rvfi_rd_addr;
  wire [3:0] rvfi_mem_rmask, rvfi_mem_wmask;

  always @* begin
    mem_index = mem_addr >> 2;
    if (mem_index < 256) mem_rdata = mem[mem_index];
    else mem_rdata = 32'b0;
  end

  always @(posedge clk) begin
    if (resetn && mem_valid && mem_ready && |mem_wstrb) begin
      if (mem_wstrb[0]) mem[mem_addr >> 2][7:0] <= mem_wdata[7:0];
      if (mem_wstrb[1]) mem[mem_addr >> 2][15:8] <= mem_wdata[15:8];
      if (mem_wstrb[2]) mem[mem_addr >> 2][23:16] <= mem_wdata[23:16];
      if (mem_wstrb[3]) mem[mem_addr >> 2][31:24] <= mem_wdata[31:24];
    end
  end

  picorv32 #(
    .ENABLE_COUNTERS(0), .ENABLE_COUNTERS64(0), .ENABLE_REGS_16_31(1),
    .ENABLE_REGS_DUALPORT(1), .LATCHED_MEM_RDATA(0), .TWO_STAGE_SHIFT(1),
    .BARREL_SHIFTER(0), .TWO_CYCLE_COMPARE(0), .TWO_CYCLE_ALU(0),
    .COMPRESSED_ISA(0), .CATCH_MISALIGN(1), .CATCH_ILLINSN(1),
    .ENABLE_PCPI(0), .ENABLE_MUL(0), .ENABLE_FAST_MUL(0), .ENABLE_DIV(0),
    .ENABLE_IRQ(0), .ENABLE_IRQ_QREGS(1), .ENABLE_IRQ_TIMER(1),
    .ENABLE_TRACE(0), .REGS_INIT_ZERO(1), .PROGADDR_RESET(0),
    .PROGADDR_IRQ(16), .STACKADDR(32'h0000_0400)
  ) dut (
    .clk(clk), .resetn(resetn), .trap(trap),
    .mem_valid(mem_valid), .mem_instr(mem_instr), .mem_ready(mem_ready),
    .mem_addr(mem_addr), .mem_wdata(mem_wdata), .mem_wstrb(mem_wstrb),
    .mem_rdata(mem_rdata),
    .mem_la_read(mem_la_read), .mem_la_write(mem_la_write),
    .mem_la_addr(mem_la_addr), .mem_la_wdata(mem_la_wdata),
    .mem_la_wstrb(mem_la_wstrb),
    .pcpi_valid(), .pcpi_insn(), .pcpi_rs1(), .pcpi_rs2(),
    .pcpi_wr(1'b0), .pcpi_rd(32'b0), .pcpi_wait(1'b0), .pcpi_ready(1'b0),
    .irq(32'b0), .eoi(),
    .rvfi_valid(rvfi_valid), .rvfi_order(rvfi_order), .rvfi_insn(rvfi_insn),
    .rvfi_trap(rvfi_trap), .rvfi_halt(rvfi_halt), .rvfi_intr(rvfi_intr),
    .rvfi_mode(rvfi_mode), .rvfi_ixl(rvfi_ixl),
    .rvfi_rs1_addr(rvfi_rs1_addr), .rvfi_rs2_addr(rvfi_rs2_addr),
    .rvfi_rs1_rdata(rvfi_rs1_rdata), .rvfi_rs2_rdata(rvfi_rs2_rdata),
    .rvfi_rd_addr(rvfi_rd_addr), .rvfi_rd_wdata(rvfi_rd_wdata),
    .rvfi_pc_rdata(rvfi_pc_rdata), .rvfi_pc_wdata(rvfi_pc_wdata),
    .rvfi_mem_addr(rvfi_mem_addr), .rvfi_mem_rmask(rvfi_mem_rmask),
    .rvfi_mem_wmask(rvfi_mem_wmask), .rvfi_mem_rdata(rvfi_mem_rdata),
    .rvfi_mem_wdata(rvfi_mem_wdata),
    .trace_valid(), .trace_data()
  );

  initial begin
    for (i = 0; i < 256; i = i + 1) mem[i] = 32'b0;
    mem[0] = 32'h00500093; // addi x1, x0, 5
    mem[1] = 32'h10102023; // sw x1, 0x100(x0)
    mem[2] = 32'h10002103; // lw x2, 0x100(x0)
    mem[3] = 32'h00110193; // addi x3, x2, 1
    mem[4] = 32'h00100073; // ebreak
    $display("BEGIN");
    repeat (4) @(posedge clk);
    resetn <= 1;
    repeat (100) begin
      @(posedge clk);
      #1;
      if (rvfi_valid)
        $display("RVFI order=%0d insn=%08x pc=%08x next=%08x rd=%0d:%08x rmask=%x wmask=%x memaddr=%08x rdata=%08x wdata=%08x trap=%b intr=%b mode=%0d ixl=%0d",
          rvfi_order, rvfi_insn, rvfi_pc_rdata, rvfi_pc_wdata,
          rvfi_rd_addr, rvfi_rd_wdata, rvfi_mem_rmask, rvfi_mem_wmask,
          rvfi_mem_addr, rvfi_mem_rdata, rvfi_mem_wdata, rvfi_trap, rvfi_intr,
          rvfi_mode, rvfi_ixl);
    end
    $display("END trap=%b", trap);
    $finish;
  end
endmodule
