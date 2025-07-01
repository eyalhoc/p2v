module adder__clk_bits32_num4_float16False (
    input logic clk,
    input logic resetn,
    input logic valid,
    input logic [31:0] i0,
    input logic [31:0] i1,
    input logic [31:0] i2,
    input logic [31:0] i3,
    output logic [31:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = "clock('clk', rst_n='resetn')" (p2v_clock)
    //  * bits = 32 (int) # data width
    //  * num = 4 (int) # number of inputs
    //  * float16 = False (bool) # use a float16 adder

    logic [31:0] o0;
    logic valid_out0;
    adder__clk_bits32_num2_float16False adder0 (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid),  // input
        .i0(i0),  // input
        .i1(i1),  // input
        .o(o0),  // output
        .valid_out(valid_out0)  // output
    );

    logic [31:0] o1;
    logic valid_out1;
    adder__clk_bits32_num2_float16False adder1 (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid),  // input
        .i0(i2),  // input
        .i1(i3),  // input
        .o(o1),  // output
        .valid_out(valid_out1)  // output
    );

    adder__clk_bits32_num2_float16False adder_out (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid_out0 & valid_out1),  // input
        .i0(o0),  // input
        .i1(o1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule
