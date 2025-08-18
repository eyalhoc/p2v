export SEED=1
export TEST_LEN=4

            # Makefile

            # defaults
            SIM ?= icarus
            WAVES=1
            TOPLEVEL_LANG ?= verilog
            PLUSARGS += -fst
            COMPILE_ARGS += -g2005-sv -gsupported-assertions

            SIM_BUILD = sim_build
            VERILOG_SOURCES += /mnt/c/Users/eyalh/work/p2v_work/p2v/tutorial/example1_adder/results/step_8/rtl/*.*v 

            TOPLEVEL = adder__clk_bits16_num4_float16True

            export PYTHONPATH := $(PYTHONPATH):/mnt/c/Users/eyalh/work/p2v_work:/mnt/c/Users/eyalh/work/p2v_work/p2v/tutorial/example1_adder/step_8:/mnt/c/Users/eyalh/work/p2v_work/p2v/tutorial/example1_adder/step_8:/mnt/c/Users/eyalh/work/p2v_work/p2v/tutorial/example1_adder/results/step_8/rtl
            MODULE = tb_adder_coco

            # include cocotb's make rules to take care of the simulator setup
            include $(shell cocotb-config --makefiles)/Makefile.sim

    
