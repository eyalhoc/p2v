module adder__bits8_num32_float16False (
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
    input logic [7:0] data_in16,
    input logic [7:0] data_in17,
    input logic [7:0] data_in18,
    input logic [7:0] data_in19,
    input logic [7:0] data_in20,
    input logic [7:0] data_in21,
    input logic [7:0] data_in22,
    input logic [7:0] data_in23,
    input logic [7:0] data_in24,
    input logic [7:0] data_in25,
    input logic [7:0] data_in26,
    input logic [7:0] data_in27,
    input logic [7:0] data_in28,
    input logic [7:0] data_in29,
    input logic [7:0] data_in30,
    input logic [7:0] data_in31,
    output logic [7:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 8 (int) #  data width
    //  * num = 32 (int) #  number of inputs
    //  * float16 = False (bool) #  use a float16 adder

    logic [7:0] datas0;
    logic [7:0] datas1;
    logic valids0;
    logic valids1;
    adder__bits8_num16_float16False adder0 (
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
        .data_in8(data_in8),  // input
        .data_in9(data_in9),  // input
        .data_in10(data_in10),  // input
        .data_in11(data_in11),  // input
        .data_in12(data_in12),  // input
        .data_in13(data_in13),  // input
        .data_in14(data_in14),  // input
        .data_in15(data_in15),  // input
        .o(datas0),  // output
        .valid_out(valids0)  // output
    );

    adder__bits8_num16_float16False adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in0(data_in16),  // input
        .data_in1(data_in17),  // input
        .data_in2(data_in18),  // input
        .data_in3(data_in19),  // input
        .data_in4(data_in20),  // input
        .data_in5(data_in21),  // input
        .data_in6(data_in22),  // input
        .data_in7(data_in23),  // input
        .data_in8(data_in24),  // input
        .data_in9(data_in25),  // input
        .data_in10(data_in26),  // input
        .data_in11(data_in27),  // input
        .data_in12(data_in28),  // input
        .data_in13(data_in29),  // input
        .data_in14(data_in30),  // input
        .data_in15(data_in31),  // input
        .o(datas1),  // output
        .valid_out(valids1)  // output
    );

    adder__bits8_num2_float16False adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valids0 & valids1)),  // input
        .data_in0(datas0),  // input
        .data_in1(datas1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits8_num32_float16False
