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
p2v_tb module. Responsible for behavioral code, building test-benches and testing.
"""

import os
import random
import numpy as np

from p2v_clock import p2v_clock as clock
import p2v_misc as misc

PASS_STATUS = "PASSED"
FAIL_STATUS = "FAILED"

class p2v_tb():
    """
    This class is a p2v test bench function wrapper.
    """

    def __init__(self, parent, seed, max_seed=1024):
        self._parent = parent
        self.seed = self._set_random_seed(seed, max_seed=max_seed)

    def _test_finish(self, status, condition=None, message=None, params=None):
        if params is None:
            params = []
        param_str = ", $time"
        if message is None:
            msg = ""
        else:
            msg = f' ({message})'
            if isinstance(params, str):
                params = [params]
            if len(params) > 0:
                param_str += ", " + ", ".join(params)
        return f""" {misc.cond(condition is not None, f"if ({condition})")}
                    begin
                        $display("%0d: test {status}{msg}"{param_str});
                        #10; $finish;
                    end
                """

    def _set_seed(self, seed):
        random.seed(seed)
        np.random.seed(seed)

    def _set_random_seed(self, seed=0, max_seed=1024):
        if seed == 0:
            seed = random.randint(1, max_seed)
        self._set_seed(seed)
        return seed


    def rand_int(self, min_val, max_val=None):
        """
        Random integer value.

        Args:
            min_val(int): min val (if max_val is None min_val is in range [0, min_val])
            max_val([None, int]: max val

        Returns:
            int
        """
        self._parent._assert_type(min_val, int)
        self._parent._assert_type(max_val, [None, int])

        if max_val is None:
            actual_min_val, actual_max_val = 0, min_val - 1
        else:
            actual_min_val, actual_max_val = min_val, max_val
        if self.seed == 1:
            return actual_min_val
        return random.randint(actual_min_val, actual_max_val)

    def rand_hex(self, bits):
        """
        Random hex value with set width.

        Args:
            bits(int): bits of hex value

        Returns:
            Verilog hex number
        """
        self._parent._assert_type(bits, int)
        return misc.hex(self.rand_int(1<<bits), bits=bits)

    def rand_bool(self):
        """
        Random bool with 50% chance.

        Args:
            NA

        Returns:
            bool
        """
        return self.rand_chance(50)

    def rand_chance(self, chance):
        """
        Random bool with chance.

        Args:
            chance(int): chance for True

        Returns:
            bool
        """
        self._parent._assert_type(chance, int)
        assert 0 <= chance <= 100, chance
        return self.rand_int(100) > chance

    def rand_list(self, l):
        """
        Random item from list.

        Args:
            l(list): list of items to pick one from

        Returns:
            random item from list
        """
        self._parent._assert_type(l, list)
        return l[self.rand_int(len(l))]

    def rand_clock(self, prefix="", has_async=None, has_sync=None):
        """
        Create clock with random resets.

        Args:
            prefix(str): prefix all signal names
            has_async([None, bool]): use async reset, None is random
            has_sync([None, bool]): use sync reset, None is random

        Returns:
            clock
        """
        self._parent._assert_type(prefix, str)
        self._parent._assert_type(has_async, [None, bool])
        self._parent._assert_type(has_sync, [None, bool])
        if has_async is None:
            has_async = self.rand_bool()
        if has_async:
            rst_n = prefix + "rst_n"
        else:
            rst_n = None

        if has_sync is None:
            has_sync = self.rand_bool()
        if has_sync:
            reset = prefix + "reset"
        else:
            reset = None
        return clock(prefix + "clk", rst_n=rst_n, reset=reset)

    def dump(self, filename="dump.fst"):
        """
        Create an fst dump file.

        Args:
            filename(str): dump file name

        Returns:
            None
        """
        self._parent._assert_type(filename, str)

        self._parent.line(f"""
                              initial
                                  begin
                                      $dumpfile("{filename}");
                                      $dumpvars;
                                      $dumpon;
                                  end
                           """)

    def test_pass(self, condition=None, message=None, params=None):
        """
        Finish test successfully if condition is met.

        Args:
            condition([None, str]): condition for finishing test, None is unconditional
            message([None, str]): completion message
            params([str, list]): parameters for Verilog % format string

        Returns:
            None
        """
        if params is None:
            params = []
        self._parent._assert_type(condition, [None, str])
        self._parent._assert_type(message, [None, str])
        self._parent._assert_type(params, [str, list])
        return self._test_finish(PASS_STATUS, condition=condition, message=message, params=params)

    def test_fail(self, condition=None, message=None, params=None):
        """
        Finish test with error if condition is met.

        Args:
            condition([None, str]): condition for finishing test, None is unconditional
            message([None, str]): completion message
            params([str, list]): parameters for Verilog % format string

        Returns:
            None
        """
        if params is None:
            params = []
        self._parent._assert_type(condition, [None, str])
        self._parent._assert_type(message, [None, str])
        self._parent._assert_type(params, [str, list])
        return self._test_finish(FAIL_STATUS, condition=condition, message=message, params=params)

    def test_finish(self, condition, pass_message=None, fail_message=None, params=None):
        """
        Finish test if condition is met.

        Args:
            condition([None, str]): condition for finishing test, None is unconditional
            pass_message([None, str]): good completion message
            fail_message([None, str]): bad completion message
            params([str, list]): parameters for Verilog % format string

        Returns:
            None
        """
        if params is None:
            params = []
        self._parent._assert_type(condition, [None, str])
        self._parent._assert_type(pass_message, [None, str])
        self._parent._assert_type(fail_message, [None, str])
        self._parent._assert_type(params, [str, list])
        return f"""
                if ({condition})
                    {self.test_pass(pass_message, params=params)}
                else
                    {self.test_fail(fail_message, params=params)}
                """

    def gen_clk(self, clk, cycle=10, reset_cycles=20, pre_reset_cycles=5):
        """
        Generate clock and async reset if it exists.

        Args:
            clk(clock): p2v clock
            cycle(int): clock cycle
            reset_cycles(int): number of clock cycles before releasing reset
            pre_reset_cycles(int): number of clock cycles before issuing reset

        Returns:
            None
        """
        self._parent._assert_type(clk, clock)
        self._parent._assert_type(cycle, int)
        self._parent._assert_type(reset_cycles, int)
        self._parent._assert_type(pre_reset_cycles, int)

        self._parent._assert(cycle >= 2, f"clock cycle of {cycle} cannot be generated", fatal=True)

        self._parent._check_declared(clk.name)
        cycle_low = cycle // 2
        cycle_high = cycle - cycle_low
        self._parent.line(f"""
                           initial forever
                               begin
                                   {clk} = 0;
                                   #{cycle_low};
                                   {clk} = 1;
                                   #{cycle_high};
                               end
                           """)
        self._parent.allow_undriven(clk.name)
        if clk.rst_n is not None:
            self._parent.line(f"""
                                 initial
                                     begin
                                         {clk.rst_n} = 1;
                                         repeat ({pre_reset_cycles}) @(negedge {clk}); // async reset occurs not on posedge of clock
                                         {clk.rst_n} = 0;
                                         repeat ({reset_cycles}) @(posedge {clk});
                                         {clk.rst_n} = 1;
                                     end
                              """)
            self._parent.allow_undriven(clk.rst_n)
        if clk.reset is not None:
            self._parent.line(f"""
                                 initial
                                     begin
                                         {clk.reset} = 0;
                                     end
                              """)
            self._parent.allow_undriven(clk.reset)

    def gen_busy(self, clk, name, max_duration=100, max_delay=100, inverse=False):
        """
        Generate random behavior on signal, starts low.

        Args:
            clk(clock): p2v clock
            name(str): signal name
            max_duration(int): maximum number of clock cycles for signal to be high
            max_delay(int): maximum number of clock cycles for signal to be low

        Returns:
            None
        """
        self._parent._assert_type(clk, clock)
        self._parent._assert_type(name, str)
        self._parent._assert_type(max_duration, int)
        self._parent._assert_type(max_delay, int)
        self._parent._assert_type(inverse, bool)

        self._parent.line(f"""
                            integer _gen_busy_{name}_seed = {self.seed};
                            initial forever
                                begin
                                    {name} = {int(inverse)-0};
                                    repeat ($urandom(_gen_busy_{name}_seed) % {max_delay}) @(posedge {clk});
                                    {name} = {int(inverse)-1};
                                    repeat ($urandom(_gen_busy_{name}_seed) % {max_duration}) @(posedge {clk});
                                end
                          """)
        self._parent.allow_undriven(name)

    def gen_en(self, clk, name, max_duration=100, max_delay=100):
        """
        Generate random behavior on signal, starts high.

        Args:
            clk(clock): p2v clock
            name(str): signal name
            max_duration(int): maximum number of clock cycles for signal to be low
            max_delay(int): maximum number of clock cycles for signal to be high

        Returns:
            None
        """
        self._parent._assert_type(clk, clock)
        self._parent._assert_type(name, str)
        self._parent._assert_type(max_duration, int)
        self._parent._assert_type(max_delay, int)
        self.gen_busy(clk, name, max_duration=max_duration, max_delay=max_delay, inverse=True)

    def set_timeout(self, clk, timeout=100000):
        """
        Generate random behavior on signal, starts high.

        Args:
            clk(clock): p2v clock
            timeout(int): number of cycles before test is ended on timeout error

        Returns:
            None
        """
        self._parent._assert_type(clk, clock)
        self._parent._assert_type(timeout, int)

        self._parent.logic(f"_count_{clk}", 32, initial=0)
        self._parent.line(f"""
                             always @(posedge {clk}) _count_{clk} <= _count_{clk} + 'd1;
                          """)
        self._parent.assert_never(clk, f"_count_{clk} >= 'd{timeout}", f"reached timeout after {timeout} cycles of {clk}")

    def register_test(self, args=None):
        """
        Register random module parameters to csv file.

        Args:
            args([None, dict]): argument dictionary to be written

        Returns:
            None
        """
        self._parent._assert_type(args, [None, dict])

        col_width = 16
        if args is None:
            args = {}
            for name in self._parent._params:
                args[name] = self._parent._params[name][0]
        filename = os.path.join(self._parent._args.outdir, f"{self._parent._get_clsname()}.gen.csv")
        if not os.path.isfile(filename):
            headers = []
            for name in args:
                headers.append(name.ljust(col_width))
            misc._write_file(filename, ", ".join(headers))
        vals = []
        for name in args:
            val = args[name]
            if isinstance(val, clock):
                val_str = val._declare()
            elif isinstance(val, bool): # bool must be before int since bool is also an int type
                val_str = f"bool({val})"
            elif isinstance(val, int):
                val_str = f"int({val})"
            elif isinstance(val, str):
                val_str = f'"{val}"'
            else:
                val_str = str(val)

            vals.append(val_str.ljust(col_width))
        misc._write_file(filename, ", ".join(vals), append=True)

    def fifo(self, name, bits=1):
        """
        Create SystemVerilog behavioral fifo (queue).

        Args:
            name(str): name of signal
            bits(int): width of fifo

        Returns:
            None
        """
        self._parent._assert_type(name, str)
        self._parent._assert_type(bits, int)

        if misc._is_int(bits):
            msb = bits - 1
        else:
            msb = f"{bits}-1"
        self._parent.line(f"reg [{msb}:0] {name}[$];")

    def syn_off(self):
        """
        Start of non-synthesizable code.

        Args:
            NA

        Returns:
            None
        """
        self._parent.remark("synopsys translate_off")

    def syn_on(self):
        """
        End of non-synthesizable code.

        Args:
            NA

        Returns:
            None
        """
        self._parent.remark("synopsys translate_on")
