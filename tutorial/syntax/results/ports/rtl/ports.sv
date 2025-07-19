module ports #(
    parameter BITS = 32
) (
    input logic a,  //  default is single bit
    input logic b,  //  same as the above
    input logic [7:0] c,  //  multi bit bus
    input logic [7:0] dd,  //  parametric width
    input logic [7:0] e,  //  parametric width but forces [0:0] bus if width is 1
    input logic [7:0] f0,  //  port in loop
    input logic [7:0] f1,  //  port in loop
    input logic [7:0] f2,  //  port in loop
    input logic [7:0] f3,  //  port in loop
    input logic [15:0] g,  //  conditional port
    output logic ao,  //  default is single bit
    output logic bo,  //  same as the above
    output logic [7:0] co,  //  multi bit bus
    output logic [7:0] ddo,  //  parametric width
    output logic [7:0] eo,  //  parametric width but forces [0:0] bus if width is 1
    output logic [7:0] f0o,  //  port in loop
    output logic [7:0] f1o,  //  port in loop
    output logic [7:0] f2o,  //  port in loop
    output logic [7:0] f3o,  //  port in loop
    output logic [15:0] go,  //  conditional port
    inout q,  // inout ports width is always 1
    input logic [7:0] s__ctrl,
    input logic [31:0] s__data,
    output logic [7:0] t__ctrl,
    output logic [31:0] t__data,
    input logic [BITS-1:0] z,  //  Verilog parametric port - name must be explicit
    output logic [BITS-1:0] zo  //  Verilog parametric port - name must be explicit
);

    // ports module parameters:

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

endmodule  // ports
