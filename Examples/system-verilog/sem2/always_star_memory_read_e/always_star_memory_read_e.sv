// IEEE 1800-2023 §§9.4.2.2.2 and 7.4: a plain @* reads a
// runtime-selected cell of a parameter-sized unpacked memory.
module always_star_memory_read_e #(parameter int N = 4) (
    input logic clk,
    input logic we,
    input logic [1:0] widx,
    input logic [1:0] ridx,
    input logic [7:0] d,
    output logic [7:0] q
);
    logic [7:0] mem [0:N-1];

    always_ff @(posedge clk) begin
        if (we)
            mem[widx] <= d;
    end

    always @* begin
        q = mem[ridx];
    end
endmodule
