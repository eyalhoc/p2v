module adder__bits8 (
    input logic clk,
    input logic rst_n,
    input logic valid,  //  default width is 1 bit
    input logic [7:0] a,
    input logic [7:0] b,
    output logic [7:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 8 (int) #  data width

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) o <= 8'd0;
        else if (valid) o <= (a + b);

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) valid_out <= 1'd0;
        else valid_out <= valid;


endmodule  // adder__bits8
