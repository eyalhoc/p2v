module tb ();

    // tb_adder module parameters:
    //  * async_reset = True (bool) # sync reset or async reset
    //  * size = 4 (int) # number of inputs to test

    logic clk;
    logic resetn;

    initial
        forever begin
            clk = 0;
            #1;
            clk = 1;
            #1;
        end


    initial begin
        resetn = 1;
        repeat (5) @(negedge clk);  // async reset occurs not on posedge of clock
        resetn = 0;
        repeat (20) @(posedge clk);
        resetn = 1;
    end

    logic valid;
    initial valid = 1'd0;

    logic [31:0] i0;
    initial i0 = 32'd0;

    logic [31:0] i1;
    initial i1 = 32'd0;

    logic [31:0] i2;
    initial i2 = 32'd0;

    logic [31:0] i3;
    initial i3 = 32'd0;

    logic [31:0] o;
    logic valid_out;
    adder__clk_bits32_num4_float16False adder (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid),  // input
        .i0(i0),  // input
        .i1(i1),  // input
        .i2(i2),  // input
        .i3(i3),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );

    logic en;
    initial en = 1'd0;

    reg [127:0] data_in_q [$];
    reg [ 31:0] expected_q[$];

    initial begin

        data_in_q.push_back({4{32'h0000_0000}});
        expected_q.push_back(32'h0000_0000);
        data_in_q.push_back({4{32'h0000_0000}});
        expected_q.push_back(32'h0000_0000);
        data_in_q.push_back({4{32'h0000_0000}});
        expected_q.push_back(32'h0000_0000);
        data_in_q.push_back({4{32'h0000_0000}});
        expected_q.push_back(32'h0000_0000);

    end

    logic [127:0] data_in;
    initial data_in = 128'd0;

    logic [31:0] expected;
    initial expected = 32'd0;


    initial begin
        @(posedge resetn);
        repeat (10) @(posedge clk);
        en = 1;
    end

    // drive inputs
    always @(posedge clk)
        if (en && (data_in_q.size() > 0)) begin
            data_in = data_in_q.pop_front();
            {i0, i1, i2, i3} <= data_in;
            valid <= 1;
        end

    // check output
    always @(posedge clk)
        if (valid_out) begin
            expected = expected_q.pop_front();
            if (o !== expected) begin
                $display("%0d: test FAILED (mismatch expected: 0x%0h, actual: 0x%0h)", $time,
                         expected, o);
                #10;
                $finish;
            end

            if (expected_q.size() == 0) begin
                $display("%0d: test PASSED (successfully tested 4 additions)", $time);
                #10;
                $finish;
            end

        end

    logic [31:0] _count_clk;
    initial _count_clk = 32'd0;


    always @(posedge clk) _count_clk <= _count_clk + 'd1;

    logic assert_never__reached_timeout_after_400_cycles_of_clk;
    assign assert_never__reached_timeout_after_400_cycles_of_clk = _count_clk >= 'd400;

    always @(posedge clk)
        if (resetn & assert_never__reached_timeout_after_400_cycles_of_clk)
            $fatal(0, "reached timeout after 400 cycles of clk");


    initial begin
        $dumpfile("dump.fst");
        $dumpvars;
        $dumpon;
    end


endmodule
