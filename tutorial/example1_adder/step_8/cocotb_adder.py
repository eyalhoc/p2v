
import cocotb
from p2v_cocotb import p2v_cocotb, GetParam

import os
import random
from dut_module import pins

test_flags = {}
test_flags["test_done"] = False

TEST_LEN = GetParam("TEST_LEN", 32)


async def check_data(dut, clk, expected):
    common = p2v_cocotb(dut)
    for i in range(TEST_LEN):
        await common.WaitValue(clk, dut.valid_out)
        assert len(expected) > 0, f"unexpected valid_out"
        next_data = expected[0]
        assert dut.o.value == next_data, f"output = 0x{format(dut.o.value.integer, 'x')} while expecting {hex(next_data)}"
        dut._log.info("DATA CHECK %d: %s", i, hex(next_data))
        expected = expected[1:]
        await common.WaitDelay(clk)
    test_flags["test_done"] = True
    
async def drive_data(dut, clk, datas):
    common = p2v_cocotb(dut)
    cnt = 0
    while cnt < len(datas):
        delay_high = random.randint(1, 8)
        for i in range(delay_high):
            dut.valid.value = 1
            for n, data in enumerate(datas[cnt]):
                common.DutSignal(pins.data_in[n]).value = data
            await common.WaitDelay(clk)
            cnt += 1
            if cnt == len(datas):
                break
        delay_low = random.randint(0, 8)
        for i in range(delay_low):
            dut.valid.value = 0
            await common.WaitDelay(clk)
        
@cocotb.test()
async def test(dut):
    """Main test."""

    common = p2v_cocotb(dut)
    clk = pins.clk
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
        common.DutSignal(pins.data_in[n]).value = 0
        
    await common.GenClkRst(clk, timeout=10000)
        
    await common.WaitDelay(clk, 3)
    await cocotb.start(check_data(dut, clk, expected=expected))
    await cocotb.start(drive_data(dut, clk, datas=datas))
    
    while not test_flags["test_done"]:
        await common.WaitDelay(clk)
    