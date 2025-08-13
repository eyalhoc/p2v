module adder__bits17_num2_float16False (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [16:0] data_in__0,
    input logic [16:0] data_in__1,
    output logic [16:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 17 (int) #  data width
    //  * num = 2 (int) #  number of inputs
    //  * float16 = False (bool) #  use a float16 adder

    logic [16:0] o_pre;
    assign o_pre = (data_in__0 + data_in__1);
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) o <= 17'd0;
        else if (valid) o <= o_pre;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) valid_out <= 1'd0;
        else valid_out <= valid;


endmodule  // adder__bits17_num2_float16False
