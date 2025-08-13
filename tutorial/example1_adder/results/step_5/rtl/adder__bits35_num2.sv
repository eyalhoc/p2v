module adder__bits35_num2 (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [34:0] data_in__0,
    input logic [34:0] data_in__1,
    output logic [34:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 35 (int) #  data width
    //  * num = 2 (int) #  number of inputs

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) o <= 35'd0;
        else if (valid) o <= (data_in__0 + data_in__1);

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) valid_out <= 1'd0;
        else valid_out <= valid;


endmodule  // adder__bits35_num2
