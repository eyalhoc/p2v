# test_my_design.py (extended)

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge, Timer

import os
import random
from dut_pins import pins

test_flags = {}
test_flags["reset_done"] = False
test_flags["test_done"] = False

SEED = int(os.getenv("SEED", 1))
TEST_LEN = int(os.getenv("TEST_LEN", 32))

random.seed(SEED)

async def generate_clock(dut):
    """Generate clock pulses."""

    cycle = random.randint(2, 10)
    while True:
        dut.clk.value = 0
        await Timer(cycle//2, units="ns")
        dut.clk.value = 1
        await Timer(cycle-(cycle//2), units="ns")

async def generate_reset(dut):
    """Generate reset."""
    dut.rst_n.value = 1
    await FallingEdge(dut.clk)
    dut.rst_n.value = 0
    reset_duration = random.randint(2, 16)
    for _ in range(reset_duration):
        await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)
    test_flags["reset_done"] = True

async def check_data(dut, expected):
    await RisingEdge(dut.rst_n)
    for i in range(TEST_LEN):
        while dut.valid_out.value != 1:
            await FallingEdge(dut.clk)
        assert len(expected) > 0, f"unexpected valid_out"
        next_data = expected[0]
        assert dut.o.value == next_data, f"output = 0x{format(dut.o.value.integer, 'x')} while expecting {hex(next_data)}"
        dut._log.info("DATA CHECK %d: %s", i, hex(next_data))
        expected = expected[1:]
        await FallingEdge(dut.clk)
    test_flags["test_done"] = True
    
async def drive_data(dut, datas):
    cnt = 0
    while cnt < len(datas):
        delay_high = random.randint(1, 8)
        for i in range(delay_high):
            dut.valid.value = 1
            for n, data in enumerate(datas[cnt]):
                getattr(dut, str(pins.data_in[n])).value = data
            await FallingEdge(dut.clk)
            cnt += 1
            if cnt == len(datas):
                break
        delay_low = random.randint(0, 8)
        for i in range(delay_low):
            dut.valid.value = 0
            await FallingEdge(dut.clk)
        
@cocotb.test()
async def test(dut):
    """Try accessing the design."""
    dut._log.info("Starting test with seed: %d", SEED)

    bits = pins.data_in[0].bits()
    
    num = len(pins.data_in)
    datas = []
    expected = []
    for i in range(TEST_LEN):
        data_in = []
        for n in range(num):
            next_val = random.getrandbits(bits)
            data_in.append(next_val)
        datas.append(data_in)
        data_sum = sum(data_in) & ((1<<bits) - 1)
        expected.append(data_sum)
        dut._log.info("EXPECTED %d: %s", i, hex(data_sum))


    dut.valid.value = 0
    for n in range(num):
        getattr(dut, str(pins.data_in[n])).value = 0
        
    await cocotb.start(generate_clock(dut))
    await cocotb.start(generate_reset(dut))
    await cocotb.start(check_data(dut, expected=expected))

    while not test_flags["reset_done"]:
        await FallingEdge(dut.clk)
        
    await cocotb.start(drive_data(dut, datas=datas))
    
    while not test_flags["test_done"]:
        await FallingEdge(dut.clk)
    