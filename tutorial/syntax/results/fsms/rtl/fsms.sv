module fsms (
    input logic clk,
    input logic rst_n,
    input logic a,
    input logic b,
    output logic o0,
    output logic o1,
    output logic o2,
    output logic [1:0] state
);

    // fsms module parameters:
    //  * clk = clk_arst() (p2v_clock) # None

    localparam logic [1:0] START = 2'd0;
    localparam logic [1:0] WAIT = 2'd1;
    localparam logic [1:0] STOP = 2'd2;

    logic [1:0] fsm_my_fsm_ps;
    logic [1:0] fsm_my_fsm_ns;

    always_comb begin
        case (fsm_my_fsm_ps)
            START: fsm_my_fsm_ns = (a ? WAIT : START);
            WAIT:  fsm_my_fsm_ns = (b ? STOP : WAIT);
            STOP:  fsm_my_fsm_ns = START;

            default: fsm_my_fsm_ns = 'x;
        endcase
    end  // fsm_my_fsm (transitions)


    always @* begin
        o0 = 0;
        o1 = 0;

        case (fsm_my_fsm_ps)
            START: begin
                o1 = (a | b);
                o2 = 0;
            end
            WAIT: begin
                o0 = (a & b);
                o2 = b;
            end
            STOP: begin
                o0 = 0;
                o1 = 1;
                o2 = 0;
            end

            default: begin
                o1 = 'x;
                o2 = 'x;
                o0 = 'x;
            end
        endcase
    end  // fsm_my_fsm (assigns)

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) fsm_my_fsm_ps <= START;
        else fsm_my_fsm_ps <= fsm_my_fsm_ns;

    assign state = fsm_my_fsm_ps;

endmodule  // fsms
