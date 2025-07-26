module adder__bits8_num8 (
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
    output logic [7:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 8 (int) #  data width
    //  * num = 8 (int) #  number of inputs

    logic [7:0] datas__0;
    logic valids__0;
    adder__bits8_num4 adder0 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in__0(data_in__0),  // input
        .data_in__1(data_in__1),  // input
        .data_in__2(data_in__2),  // input
        .data_in__3(data_in__3),  // input
        .o(datas__0),  // output
        .valid_out(valids__0)  // output
    );

    logic [7:0] datas__1;
    logic valids__1;
    adder__bits8_num4 adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in__0(data_in__4),  // input
        .data_in__1(data_in__5),  // input
        .data_in__2(data_in__6),  // input
        .data_in__3(data_in__7),  // input
        .o(datas__1),  // output
        .valid_out(valids__1)  // output
    );

    adder__bits8_num2 adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valids__0 & valids__1)),  // input
        .data_in__0(datas__0),  // input
        .data_in__1(datas__1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits8_num8
