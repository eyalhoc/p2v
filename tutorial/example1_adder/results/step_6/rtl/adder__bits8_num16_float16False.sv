module adder__bits8_num16_float16False (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [7:0] data_in0,
    input logic [7:0] data_in1,
    input logic [7:0] data_in2,
    input logic [7:0] data_in3,
    input logic [7:0] data_in4,
    input logic [7:0] data_in5,
    input logic [7:0] data_in6,
    input logic [7:0] data_in7,
    input logic [7:0] data_in8,
    input logic [7:0] data_in9,
    input logic [7:0] data_in10,
    input logic [7:0] data_in11,
    input logic [7:0] data_in12,
    input logic [7:0] data_in13,
    input logic [7:0] data_in14,
    input logic [7:0] data_in15,
    output logic [7:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 8 (int) #  data width
    //  * num = 16 (int) #  number of inputs
    //  * float16 = False (bool) #  use a float16 adder

    logic [7:0] data_out0;
    logic valid_out0;
    adder__bits8_num8_float16False adder0 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in0(data_in0),  // input
        .data_in1(data_in1),  // input
        .data_in2(data_in2),  // input
        .data_in3(data_in3),  // input
        .data_in4(data_in4),  // input
        .data_in5(data_in5),  // input
        .data_in6(data_in6),  // input
        .data_in7(data_in7),  // input
        .o(data_out0),  // output
        .valid_out(valid_out0)  // output
    );

    logic [7:0] data_out1;
    logic valid_out1;
    adder__bits8_num8_float16False adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in0(data_in8),  // input
        .data_in1(data_in9),  // input
        .data_in2(data_in10),  // input
        .data_in3(data_in11),  // input
        .data_in4(data_in12),  // input
        .data_in5(data_in13),  // input
        .data_in6(data_in14),  // input
        .data_in7(data_in15),  // input
        .o(data_out1),  // output
        .valid_out(valid_out1)  // output
    );

    adder__bits8_num2_float16False adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valid_out0 & valid_out1)),  // input
        .data_in0(data_out0),  // input
        .data_in1(data_out1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits8_num16_float16False
