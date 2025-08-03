module tb ();

    // tb_adder module parameters:
    //  * async_reset = True (bool) #  sync reset or async reset
    //  * size = 4 (int) #  number of inputs to test

    logic clk;
    logic resetn;

    initial
        forever begin
            clk = 0;
            #3;
            clk = 1;
            #3;
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

    logic [15:0] inputs__0;
    initial inputs__0 = 16'd0;

    logic [15:0] inputs__1;
    initial inputs__1 = 16'd0;

    logic [15:0] inputs__2;
    initial inputs__2 = 16'd0;

    logic [15:0] inputs__3;
    initial inputs__3 = 16'd0;

    logic [15:0] o;
    logic valid_out;
    adder__clk_bits16_num4_float16True adder (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid),  // input
        .data_in__0(inputs__0),  // input
        .data_in__1(inputs__1),  // input
        .data_in__2(inputs__2),  // input
        .data_in__3(inputs__3),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );

    logic en;
    initial en = 1'd0;

    reg [63:0] data_in_q [$];
    reg [15:0] expected_q[$];

    initial begin

        data_in_q.push_back({16'h36ac, 16'h39c3, 16'h077f, 16'h34d6});
        expected_q.push_back(16'h3dc2);
        data_in_q.push_back({16'h30b2, 16'h2de9, 16'h31f6, 16'h3587});
        expected_q.push_back(16'h3a2a);
        data_in_q.push_back({16'h3659, 16'h384f, 16'h36b5, 16'h397b});
        expected_q.push_back(16'h4014);
        data_in_q.push_back({16'h328b, 16'h3b06, 16'h2703, 16'h395d});
        expected_q.push_back(16'h3f1e);

    end

    logic [63:0] data_in;
    initial data_in = 64'd0;

    logic [15:0] expected;
    initial expected = 16'd0;


    initial begin
        @(posedge resetn);
        repeat (10) @(posedge clk);
        en = 1;
    end

    // drive inputs
    always @(posedge clk)
        if (en && (data_in_q.size() > 0)) begin
            data_in = data_in_q.pop_front();
            {inputs__0, inputs__1, inputs__2, inputs__3} <= data_in;
            valid <= 1;
        end

    // check output
    always @(posedge clk)
        if (valid_out) begin
            expected = expected_q.pop_front();
            if ((o > expected) ? ((o - expected) > 16'd16) : ((expected - o) > 16'd16)) begin
                $display("test FAILED: mismatch expected: 0x%0h, actual: 0x%0h", expected, o);
                #10;
                $finish;
            end

            if (expected_q.size() == 0) begin
                $display("test PASSED: successfully tested 4 additions");
                #10;
                $finish;
            end

        end

    logic [31:0] _count_timeout__clk;
    initial _count_timeout__clk = 32'd0;


    always @(posedge clk) _count_timeout__clk <= (_count_timeout__clk + 32'd1);

    reached_timeout_after_400_cycles_of_clk_assert :
    assert property (@(posedge clk) disable iff (!resetn) (_count_timeout__clk < 32'd400))
    else $fatal(1, "reached timeout after 400 cycles of clk");

    // CODE ADDED TO SUPPORT LEGACY SIMULATOR vvp THAT DOES NOT SUPPORT CONCURRENT ASSERTIONS
    logic assert_never__reached_timeout_after_400_cycles_of_clk;
    assign assert_never__reached_timeout_after_400_cycles_of_clk = ~((_count_timeout__clk < 32'd400));

    always @(posedge clk)
        if (resetn & assert_never__reached_timeout_after_400_cycles_of_clk)
            $fatal(1, "reached timeout after 400 cycles of clk");


    initial begin
        $dumpfile("dump.fst");
        $dumpvars;
        $dumpon;
    end


endmodule  // tb
