module ports #(
    parameter BITS = 32
) (
    input logic a,
    input logic b,
    input logic [7:0] c,
    input logic [7:0] dd,
    input logic [7:0] e,
    input logic [7:0] f0,
    input logic [7:0] f1,
    input logic [7:0] f2,
    input logic [7:0] f3,
    input logic [15:0] g,
    output logic ao,
    output logic bo,
    output logic [7:0] co,
    output logic [7:0] ddo,
    output logic [7:0] eo,
    output logic [7:0] f0o,
    output logic [7:0] f1o,
    output logic [7:0] f2o,
    output logic [7:0] f3o,
    output logic [15:0] go,
    inout q,
    input logic [7:0] s__ctrl,
    input logic [31:0] s__data,
    output logic [7:0] t__ctrl,
    output logic [31:0] t__data,
    input logic [BITS-1:0] z,
    output logic [BITS-1:0] zo
);

    assign ao = a;
    assign bo = b;
    assign co = c;
    assign ddo = dd;
    assign eo = e;
    assign f0o = f0;
    assign f1o = f1;
    assign f2o = f2;
    assign f3o = f3;
    assign go = g;

    assign t__ctrl = s__ctrl;
    assign t__data = s__data;

    assign zo = z;

endmodule
