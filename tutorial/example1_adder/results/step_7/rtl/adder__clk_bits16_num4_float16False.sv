module adder__clk_bits16_num4_float16False (
    input logic clk,
    input logic resetn,
    input logic valid,
    input logic [15:0] data_in0,
    input logic [15:0] data_in1,
    input logic [15:0] data_in2,
    input logic [15:0] data_in3,
    output logic [15:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = "clock('clk', rst_n='resetn')" (p2v_clock) # None
    //  * bits = 16 (int) #  data width
    //  * num = 4 (int) #  number of inputs
    //  * float16 = False (bool) #  use a float16 adder

    logic [15:0] datas0;
    logic [15:0] datas1;
    logic valids0;
    logic valids1;
    adder__clk_bits16_num2_float16False adder0 (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid),  // input
        .data_in0(data_in0),  // input
        .data_in1(data_in1),  // input
        .o(datas0),  // output
        .valid_out(valids0)  // output
    );

    adder__clk_bits16_num2_float16False adder1 (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid),  // input
        .data_in0(data_in2),  // input
        .data_in1(data_in3),  // input
        .o(datas1),  // output
        .valid_out(valids1)  // output
    );

    adder__clk_bits16_num2_float16False adder_out (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid((valids0 & valids1)),  // input
        .data_in0(datas0),  // input
        .data_in1(datas1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__clk_bits16_num4_float16False
