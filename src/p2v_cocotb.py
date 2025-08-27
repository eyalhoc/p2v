# -----------------------------------------------------------------------------
#  Copyright (C) 2025 Eyal Hochberg (eyalhoc@gmail.com)
#
#  This file is part of an open-source Python-to-Verilog synthesizable converter.
#
#  Licensed under the GNU General Public License v3.0 or later (GPL-3.0-or-later).
#  You may use, modify, and distribute this software in accordance with the GPL-3.0 terms.
#
#  This software is distributed WITHOUT ANY WARRANTY; without even the implied
#  warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
#  GPL-3.0 license for full details: https://www.gnu.org/licenses/gpl-3.0.html
# -----------------------------------------------------------------------------

"""
p2v_cocotb module. CocoTb simulation functions.
"""
# pylint: disable=invalid-name

import os
import random
import warnings

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge, Combine, Join, Timer
from cocotb.utils import get_sim_time

def GetParam(name, default):
    """
    Get parameter passed as environment variable.
    """
    cast = type(default)
    return cast(os.getenv(name, str(default)))

SEED = GetParam("SEED", 1)
random.seed(SEED)

class p2v_cocotb:
    """
    This class is a p2v cocotb.
    """
    def __init__(self, dut):
        self.dut = dut

    def SimTime(self):
        """Return simulation time."""
        return get_sim_time()

    def Info(self, msg, *args):
        """Log info."""
        return self.dut._log.info(msg, *args)

    def DutSignal(self, son):
        """Get DUT signal."""
        return getattr(self.dut, str(son))

    async def timeout(self, clk, timeout=10000):
        """Simulation timeout."""
        cnt = 0
        while cnt < timeout:
            await self.WaitDelay(clk)
            cnt += 1
        raise cocotb.result.TestFailure(f"reached timeout after {timeout} cycles")

    async def GenClkRst(self, clk, max_cycle=10, min_cycle=2, units="ns", reset_max=64, reset_min=2, timeout=None):
        """Generate clock and resets."""
        if timeout is not None:
            await cocotb.start(self.timeout(clk, timeout=timeout))
        await cocotb.start(self.GenClk(clk, max_cycle=max_cycle, min_cycle=min_cycle, units=units))
        await self.GenRst(clk, max_duration=reset_max, min_duration=reset_min)

    async def GenClk(self, clk, max_cycle=10, min_cycle=2, units="ns"):
        """Generate clock pulses."""
        dut_clk = self.DutSignal(clk)

        cycle = random.randint(min_cycle, max_cycle)
        cocotb.start_soon(Clock(dut_clk, cycle, units=units).start())

    async def GenSyncRst(self, clk, max_duration=64, min_duration=2):
        """Generate sync reset."""
        if clk.reset is None:
            return
        dut_clk = self.DutSignal(clk)

        self.DutSignal(clk.reset).setimmediatevalue(0)
        await RisingEdge(dut_clk)
        self.DutSignal(clk.reset).value = 1
        reset_duration = random.randint(min_duration, max_duration)
        for _ in range(reset_duration):
            await RisingEdge(dut_clk)
        self.DutSignal(clk.reset).value = 0
        await RisingEdge(dut_clk)

    async def GenAsyncRst(self, clk, max_duration=64, min_duration=2):
        """Generate async reset."""
        if clk.rst_n is None:
            return
        dut_clk = self.DutSignal(clk)

        self.DutSignal(clk.rst_n).setimmediatevalue(1)
        await FallingEdge(dut_clk) # on purpose not sync to clock
        self.DutSignal(clk.rst_n).value = 0
        reset_duration = random.randint(min_duration, max_duration)
        for _ in range(reset_duration):
            await RisingEdge(dut_clk)
        self.DutSignal(clk.rst_n).value = 1
        await RisingEdge(dut_clk)

    async def GenRst(self, clk, max_duration=64, min_duration=2):
        """Generate reset."""
        sync_task = cocotb.start_soon(self.GenSyncRst(clk, max_duration=max_duration, min_duration=min_duration))
        async_task = cocotb.start_soon(self.GenAsyncRst(clk, max_duration=max_duration, min_duration=min_duration))
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", FutureWarning)
            await Combine(
                Join(sync_task),
                Join(async_task)
            )

    async def WaitSyncRstDone(self, clk):
        """Wait for sync reset to be released."""
        if clk.reset is not None:
            reset = self.DutSignal(clk.reset)
            await FallingEdge(reset)

    async def WaitASyncRstDone(self, clk):
        """Wait for async reset to be released."""
        if clk.rst_n is not None:
            rst_n = self.DutSignal(clk.rst_n)
            await RisingEdge(rst_n)

    async def WaitRstDone(self, clk):
        """Wait for resets to be released."""
        dut_clk = self.DutSignal(clk)
        sync_task = cocotb.start_soon(self.WaitSyncRstDone(clk))
        async_task = cocotb.start_soon(self.WaitASyncRstDone(clk))

        with warnings.catch_warnings():
            warnings.simplefilter("ignore", FutureWarning)
            await Combine(
                Join(sync_task),
                Join(async_task)
            )
        await FallingEdge(dut_clk)

    async def WaitDelay(self, clk, max_cycles=1, min_cycles=None):
        """Wait number of cycles."""
        if isinstance(clk, int):
            await Timer(clk, units='ns')
        else:
            dut_clk = self.DutSignal(clk)
            if min_cycles is None:
                cycles = max_cycles
            else:
                cycles = random.randint(min_cycles, max_cycles)
            for _ in range(cycles):
                await FallingEdge(dut_clk)

    async def WaitValue(self, clk, signal, val=1):
        """Wait for signal to match value."""
        dut_clk = self.DutSignal(clk)
        while signal.value != val:
            await FallingEdge(dut_clk)

    async def WaitPosedge(self, signal):
        """Wait for signal positive edge."""
        await FallingEdge(signal)
