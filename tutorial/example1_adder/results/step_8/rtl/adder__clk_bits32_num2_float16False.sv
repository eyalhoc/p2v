module adder__clk_bits32_num2_float16False (
    input logic clk,
    input logic resetn,
    input logic valid,
    input logic [31:0] i0,
    input logic [31:0] i1,
    output logic [31:0] o,
    output logic valid_out
);

    // module parameters:
    // clk = clk (p2v_clock)
    // bits = 32 (int): data width
    // num = 2 (int): number of inputs
    // float16 = False (bool): use a float16 adder

    logic [31:0] o_pre;
    assign o_pre = i0 + i1;
    always_ff @(posedge clk or negedge resetn)
        if (!resetn) o <= 32'd0;
        else if (valid) o <= o_pre;

    always_ff @(posedge clk or negedge resetn)
        if (!resetn) valid_out <= 1'd0;
        else valid_out <= valid;


endmodule
