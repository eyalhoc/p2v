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

from p2v_clock import p2v_clock as clock, clk_0rst, clk_arst, clk_srst, clk_2rst
import p2v_misc as misc
from p2v_signal import p2v_signal
import p2v_tools

PASS_STATUS = "PASSED"
FAIL_STATUS = "FAILED"

SYN_OFF = "synopsys translate_off"
SYN_ON = "synopsys translate_on"

class p2v_tb():
    """
    This class is a p2v test bench function wrapper.
    """

    def __init__(self, parent, seed, max_seed=1024, set_seed=True):
        self._parent = parent
        if seed == 0:
            self.seed = random.randint(1, max_seed)
        else:
            self.seed = seed
        if set_seed:
            self._set_seed(self.seed)


    def _test_finish(self, status, condition=None, message=None, params=None, stop=True):
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
                for n, name in enumerate(params):
                    params[n] = str(name)
                param_str += ", " + ", ".join(params)
        return f""" {misc.cond(condition is not None, f"if ({condition})")}
                    begin
                        $display("%0d: test {status}{msg}"{param_str});
                        {misc.cond(stop, "#10; $finish;")}
                    end
                """

    def _set_seed(self, seed):
        random.seed(seed)
        np.random.seed(seed)

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
        self._parent.assert_static(actual_max_val >= actual_min_val, f"random max value {actual_max_val} is less than min value {actual_min_val}", fatal=True)
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
        self._parent.assert_static(bits > 0, f"cannot generate a hex number with {bits} bits")
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

    def rand_clock(self, prefix="", has_async=None, has_sync=None, must_have_reset=False):
        """
        Create clock with random resets.

        Args:
            prefix(str): prefix all signal names
            has_async([None, bool]): use async reset, None is random
            has_sync([None, bool]): use sync reset, None is random
            must_have_reset(bool): use at least one reset

        Returns:
            clock
        """
        self._parent._assert_type(prefix, str)
        self._parent._assert_type(has_async, [None, bool])
        self._parent._assert_type(has_sync, [None, bool])

        if must_have_reset and has_async is None and has_sync is None:
            has_async = self.rand_bool()
            has_sync = not has_async

        if has_async is None:
            has_async = self.rand_bool()
        if has_sync is None:
            has_sync = self.rand_bool()
        if has_async and has_sync:
            return clk_2rst(prefix)
        if has_async:
            return clk_arst(prefix)
        if has_sync:
            return clk_srst(prefix)
        return clk_0rst(prefix)

    def dump(self, filename="dump.fst"):
        """
        Create an fst dump file.

        Args:
            filename(str): dump file name

        Returns:
            None
        """
        self._parent._assert_type(filename, str)

        dump_format = filename.split(".")[-1]
        self._parent._assert(dump_format in ["vcd", "fst", "fsdb"], f"unknown dump format {dump_format}", fatal=True)

        if dump_format == "fsdb":
            self._parent.line(f"""
                                  initial
                                      begin
                                          $fsdbDumpfile("{filename}");
                                          $fsdbDumpvars;
                                      end
                               """)
        else:
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
        self._parent._assert_type(condition, [None, str, p2v_signal])
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
        self._parent._assert_type(condition, [None, str, p2v_signal])
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
                                         repeat ({pre_reset_cycles}) @(posedge {clk});
                                         {clk.reset} = 1;
                                         repeat ({reset_cycles}) @(posedge {clk});
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
        self._parent._assert_type(name, [str, p2v_signal])
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
        self._parent._assert_type(name, [str, p2v_signal])
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

        name = str(clk)
        _count_timeout = {}
        _count_timeout[name] = self._parent.logic(32, initial=0)
        self._parent.line(f"""
                             always @(posedge {clk}) { _count_timeout[name]} <= { _count_timeout[name] + 1};
                          """)
        self._parent.assert_never(clk, _count_timeout[name] >= timeout, f"reached timeout after {timeout} cycles of {clk}")
        self._parent.allow_unused( _count_timeout[name])


    def register_test(self, args=None):
        """
        Register random module parameters to csv file.

        Args:
            args([None, dict]): argument dictionary to be written

        Returns:
            None
        """
        self._parent._assert_type(args, [None, dict])

        col_width = 20
        if args is None:
            args = {}
            for name in self._parent._params:
                args[name] = self._parent._params[name][0]
        filename = os.path.join(self._parent._args.outdir, f"{self._parent._get_clsname()}.gen.csv")
        if not os.path.isfile(filename):
            headers = []
            for name in args:
                if name.startswith("_"): # private argument
                    continue
                headers.append(name.ljust(col_width))
            misc._write_file(filename, ", ".join(headers))
        vals = []
        for name in args:
            if name.startswith("_"): # private argument
                continue
            val = args[name]
            if isinstance(val, clock):
                val_str = val._declare()
            #elif isinstance(val, bool): # bool must be before int since bool is also an int type
            #    val_str = f"bool({val})"
            #elif isinstance(val, int):
            #    val_str = f"int({val})"
            elif isinstance(val, str):
                val_str = f'"{val}"'
            else:
                val_str = str(val)

            vals.append(val_str.ljust(col_width))
        misc._write_file(filename, ", ".join(vals), append=True)

    def fifo(self, bits=1):
        """
        Create SystemVerilog behavioral fifo (queue).

        Args:
            bits(int): width of fifo

        Returns:
            None
        """
        self._parent._assert_type(bits, int)

        name = self._parent._get_receive_name("fifo")

        if misc._is_int(bits):
            msb = bits - 1
        else:
            msb = f"{bits}-1"
        self._parent.line(f"reg [{msb}:0] {name}[$];")
        return self.expr(name, bits=bits)

    def syn_off(self):
        """
        Start of non-synthesizable code.
        """
        self.lint_off()
        last_idx, last_line = self._parent._get_last_line(skip_remark=False)
        if last_line == misc._remark_line(SYN_ON):
            self._parent._rm_line(last_idx)
        else:
            self._parent.remark(SYN_OFF)

    def syn_on(self):
        """
        End of non-synthesizable code.
        """
        last_idx, last_line = self._parent._get_last_line(skip_remark=False)
        if last_line == misc._remark_line(SYN_OFF):
            self._parent._rm_line(last_idx)
        else:
            self._parent.remark(SYN_ON)
        self.lint_on()

    def lint_off(self):
        """
        Start of non-lintable code.
        """
        last_idx, last_line = self._parent._get_last_line(skip_remark=False)
        if last_line == p2v_tools.lint_on(self._parent._args.lint_bin):
            self._parent._rm_line(last_idx)
        else:
            self._parent.line("")
            self._parent.line(p2v_tools.lint_off(self._parent._args.lint_bin))

    def lint_on(self):
        """
        End of non-lintable code.
        """
        last_idx, last_line = self._parent._get_last_line(skip_remark=False)
        if last_line == p2v_tools.lint_off(self._parent._args.lint_bin):
            self._parent._rm_line(last_idx)
        else:
            self._parent.line(p2v_tools.lint_on(self._parent._args.lint_bin))

    def expr(self, line, bits=0):
        """
        Convert a testbench string expression to a p2v signal.
        Args:
            line(str): Verilog expression

        Returns:
            p2v_signal
        """
        return p2v_signal(None, line, bits=bits)
