module ports #(
    parameter int BITS = 32
) (
    input logic a,
    input logic b,
    input logic [7:0] c,
    input logic [7:0] dd,
    input logic [7:0] e,
    input logic [7:0] f__0,
    input logic [7:0] f__1,
    input logic [7:0] f__2,
    input logic [7:0] f__3,
    input logic [15:0] g,
    output logic ao,
    output logic bo,
    output logic [7:0] co,
    output logic [7:0] ddo,
    output logic [7:0] eo,
    output logic [7:0] fo__0,
    output logic [7:0] fo__1,
    output logic [7:0] fo__2,
    output logic [7:0] fo__3,
    output logic [15:0] go,
    inout q,
    output logic qo,
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
    assign fo__0 = f__0;
    assign fo__1 = f__1;
    assign fo__2 = f__2;
    assign fo__3 = f__3;
    assign go = g;
    assign qo = q;

    assign t__ctrl = s__ctrl;
    assign t__data = s__data;

    assign zo = z;

endmodule  // ports
