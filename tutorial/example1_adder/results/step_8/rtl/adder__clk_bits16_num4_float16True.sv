module adder__clk_bits16_num4_float16True (
    input logic clk,
    input logic resetn,
    input logic valid,
    input logic [15:0] data_in__0,
    input logic [15:0] data_in__1,
    input logic [15:0] data_in__2,
    input logic [15:0] data_in__3,
    output logic [15:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = "clock('clk', rst_n='resetn')" (p2v_clock) # None
    //  * bits = 16 (int) #  data width
    //  * num = 4 (int) #  number of inputs
    //  * float16 = True (bool) #  use a float16 adder

    logic [15:0] data_out0;
    logic valid_out0;
    adder__clk_bits16_num2_float16True adder0 (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid),  // input
        .data_in__0(data_in__0),  // input
        .data_in__1(data_in__1),  // input
        .o(data_out0),  // output
        .valid_out(valid_out0)  // output
    );

    logic [15:0] data_out1;
    logic valid_out1;
    adder__clk_bits16_num2_float16True adder1 (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid),  // input
        .data_in__0(data_in__2),  // input
        .data_in__1(data_in__3),  // input
        .o(data_out1),  // output
        .valid_out(valid_out1)  // output
    );

    adder__clk_bits16_num2_float16True adder_out (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid((valid_out0 & valid_out1)),  // input
        .data_in__0(data_out0),  // input
        .data_in__1(data_out1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__clk_bits16_num4_float16True
