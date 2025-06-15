module adder__bits8_num2_float16False (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [7:0] i0,
    input logic [7:0] i1,
    output logic [7:0] o,
    output logic valid_out
);

    // module parameters:
    // clk = "clock('clk', rst_n='rst_n')" (p2v_clock)
    // bits = 8 (int) # data width
    // num = 2 (int) # number of inputs
    // float16 = False (bool) # use a float16 adder

    logic [7:0] o_pre;
    assign o_pre = i0 + i1;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) o <= 8'd0;
        else if (valid) o <= o_pre;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) valid_out <= 1'd0;
        else valid_out <= valid;


endmodule
