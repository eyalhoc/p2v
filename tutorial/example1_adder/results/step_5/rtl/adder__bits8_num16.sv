module adder__bits8_num16 (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [7:0] data_in__0,
    input logic [7:0] data_in__1,
    input logic [7:0] data_in__2,
    input logic [7:0] data_in__3,
    input logic [7:0] data_in__4,
    input logic [7:0] data_in__5,
    input logic [7:0] data_in__6,
    input logic [7:0] data_in__7,
    input logic [7:0] data_in__8,
    input logic [7:0] data_in__9,
    input logic [7:0] data_in__10,
    input logic [7:0] data_in__11,
    input logic [7:0] data_in__12,
    input logic [7:0] data_in__13,
    input logic [7:0] data_in__14,
    input logic [7:0] data_in__15,
    output logic [7:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 8 (int) #  data width
    //  * num = 16 (int) #  number of inputs

    logic [7:0] data_out0;
    logic valid_out0;
    adder__bits8_num8 adder0 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in__0(data_in__0),  // input
        .data_in__1(data_in__1),  // input
        .data_in__2(data_in__2),  // input
        .data_in__3(data_in__3),  // input
        .data_in__4(data_in__4),  // input
        .data_in__5(data_in__5),  // input
        .data_in__6(data_in__6),  // input
        .data_in__7(data_in__7),  // input
        .o(data_out0),  // output
        .valid_out(valid_out0)  // output
    );

    logic [7:0] data_out1;
    logic valid_out1;
    adder__bits8_num8 adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in__0(data_in__8),  // input
        .data_in__1(data_in__9),  // input
        .data_in__2(data_in__10),  // input
        .data_in__3(data_in__11),  // input
        .data_in__4(data_in__12),  // input
        .data_in__5(data_in__13),  // input
        .data_in__6(data_in__14),  // input
        .data_in__7(data_in__15),  // input
        .o(data_out1),  // output
        .valid_out(valid_out1)  // output
    );

    adder__bits8_num2 adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valid_out0 & valid_out1)),  // input
        .data_in__0(data_out0),  // input
        .data_in__1(data_out1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits8_num16
