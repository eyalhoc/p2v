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
import string
import numpy as np

from p2v_clock import p2v_clock as clock, clk_0rst, clk_arst, clk_srst, clk_2rst
import p2v_misc as misc
from p2v_signal import p2v_signal, p2v_type
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
        self._max_seed = max_seed
        if seed == 0:
            self.seed = random.randint(1, max_seed)
        else:
            self.seed = seed
        if set_seed:
            self._set_seed(self.seed)
        self._ifdefs = []
        self._block = None


    def _test_finish(self, condition=None, message="", stop=True, _inline=False):
        self._parent._set_used(condition, allow=True)
        line = f""" {misc.cond(condition is not None, f"if ({condition})")}
                            begin
                                $display({message});
                                {misc.cond(stop, "#10; $finish;")}
                            end
                           """
        if _inline:
            return line
        return self._parent.line(line)

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

    def rand_float(self, min_val, max_val):
        """
        Random float value.

        Args:
            min_val(float): min val
            max(float): max val

        Returns:
            float
        """
        return random.uniform(min_val, max_val)

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

    def rand_char(self):
        """
        Random printable character.

        Args:
            NA

        Returns:
            str
        """
        return random.choice(string.ascii_letters + string.digits)

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

    def rand_clock(self, prefix="", has_async=None, has_sync=None, must_have_reset=True):
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

    def _get_messgae(self, status, message=""):
        self._parent._check_line_balanced(message)
        full_message = f'"test {status}"'
        message = message.strip()
        if message != "":
            if message[0] != '"':
                message = f'"{message}"'
            full_message = full_message[:-1] # remove closing quote
            full_message += f': {message[1:]}'
        return full_message

    def test_pass(self, condition=None, message="", _inline=False):
        """
        Finish test successfully if condition is met.

        Args:
            condition([None, str]): condition for finishing test, None is unconditional
            message(str): completion message

        Returns:
            None
        """
        self._parent._assert_type(condition, [None, str, p2v_signal])
        self._parent._assert_type(message, str)
        full_message = self._get_messgae(PASS_STATUS, message)
        return self._test_finish(condition=condition, message=full_message, _inline=_inline)

    def test_fail(self, condition=None, message="", _inline=False):
        """
        Finish test with error if condition is met.

        Args:
            condition([None, str]): condition for finishing test, None is unconditional
            message(str): completion message

        Returns:
            None
        """
        self._parent._assert_type(condition, [None, str, p2v_signal])
        self._parent._assert_type(message, str)
        full_message = self._get_messgae(FAIL_STATUS, message)
        return self._test_finish(condition=condition, message=full_message, _inline=_inline)

    def test_finish(self, condition, pass_message="", fail_message="", _inline=False):
        """
        Finish test if condition is met.

        Args:
            condition([None, str, p2v_signal]): condition for successfully finishing test, None is unconditional
            pass_message(str): good completion message
            fail_message(str): bad completion message

        Returns:
            None
        """
        self._parent._assert_type(condition, [None, str, p2v_signal])
        self._parent._assert_type(pass_message, str)
        self._parent._assert_type(fail_message, str)
        self._parent._set_used(condition, allow=True)
        return f"""
                if {misc._add_paren(condition)}
                    {self.test_pass(message=pass_message, _inline=_inline)}
                else
                    {self.test_fail(message=fail_message, _inline=_inline)}
                """

    def gen_clk(self, clk, cycle=10, reset_cycles=20, pre_reset_cycles=0, timeout=None):
        """
        Generate clock and async reset if it exists.

        Args:
            clk(clock): p2v clock
            cycle(int): clock cycle
            reset_cycles(int): number of clock cycles before releasing reset
            pre_reset_cycles(int): number of clock cycles before issuing reset
            timeout([None, int]): set timeout on clock

        Returns:
            None
        """
        self._parent._assert_type(clk, clock)
        self._parent._assert_type(cycle, int)
        self._parent._assert_type(reset_cycles, int)
        self._parent._assert_type(pre_reset_cycles, int)
        self._parent._assert_type(timeout, [None, int])

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
        if timeout is not None:
            self.set_timeout(clk, timeout=timeout)

    def gen_busy(self, clk, name=None, max_duration=20, max_delay=20, inverse=False, en=None):
        """
        Generate random behavior on signal, starts low.

        Args:
            clk(clock): p2v clock
            name(str): signal name
            max_duration(int): maximum number of clock cycles for signal to be high
            max_delay(int): maximum number of clock cycles for signal to be low
            inverse(bool): in inversed initial value is high
            en([None,

        Returns:
            None
        """
        self._parent._assert_type(clk, clock)
        self._parent._assert_type(name, [None, p2v_signal])
        self._parent._assert_type(max_duration, int)
        self._parent._assert_type(max_delay, int)
        self._parent._assert_type(inverse, bool)
        self._parent._assert_type(en, [None, bool, p2v_signal])

        if name is None:
            name = self._parent._get_receive_name("gen_busy")
            signal = self._parent.logic(name, _allow_str=True)
        else:
            signal = name

        if en is False:
            self._parent.assign(signal, int(inverse))
        else:
            self._parent.line(f"""
                                integer _gen_busy_{name}_seed = {self.rand_int(self._max_seed)};
                                initial forever
                                    begin
                                        {name} = {int(inverse)-0};
                                        repeat ($urandom(_gen_busy_{name}_seed) % {max_delay}) @(posedge {clk});
                                        {misc.cond(en not in [None, True], f"if ({en}) ")}{name} = {int(inverse)-1};
                                        repeat ($urandom(_gen_busy_{name}_seed) % {max_duration}) @(posedge {clk});
                                    end
                              """)
            self._parent.allow_undriven(name)
        return signal

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

    def set_timeout(self, clk, timeout=100000, success=False):
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
        self._parent.assert_property(clk, _count_timeout[name] < timeout, f"reached timeout after {timeout} cycles of {clk}")
        if success:
            self.always(clk)
            self.test_pass(_count_timeout[name] == (timeout-10), f"successfully completed {timeout} cycles of {clk}")
            self.end()
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

    def write_data(self, filename, data=None, bits=8):
        """ write a list of int values as hex string for Verilog readmemh """
        self._parent._assert((bits%8)==0, f"bits {bits} must be in bytes (divide by 8)", fatal=True)
        if data is None:
            data = filename
            filename = self._parent._get_receive_name("write_data") + ".txt"
        data_hex = []
        for d in data:
            if isinstance(d, np.integer):
                d = int(d)
            if isinstance(d, int):
                for dbyte in misc._to_bytes(d, bits=bits):
                    data_hex.append(str(misc.hex(dbyte, bits=8, add_sep=0, prefix=None)))
            else:
                self._parent._raise(f"unsupported data type {type(d)}")
        fullname = os.path.abspath(os.path.join(self._parent._args.outdir, filename))
        self._parent._assert(not os.path.isfile(fullname), f"{fullname} already exists", fatal=True)
        misc._write_file(fullname, "\n".join(data_hex))
        return fullname

    def fifo(self, bits=1):
        """
        Create SystemVerilog behavioral fifo (queue).

        Args:
            bits(int): width of fifo

        Returns:
            None
        """
        if issubclass(type(bits), p2v_type):
            bits = bits._bits
        self._parent._assert_type(bits, int)

        name = self._parent._get_receive_name("fifo")

        return self.p2v_tb_fifo(parent=self._parent, name=name, bits=bits)

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

    def ifdef(self, name):
        """
        Insert a Verilog `ifdef statement
        """
        self._parent.line(f"`ifdef {name}")
        self._ifdefs.append(name)

    def ifndef(self, name):
        """
        Insert a Verilog `ifndef statement
        """
        self._parent.line(f"`ifndef {name}")
        self._ifdefs.append(name)

    def endif(self, name):
        """
        Insert a Verilog `endif statement
        """
        if self._parent._assert(len(self._ifdefs) > 0, "endif without previous ifdef"):
            if self._parent._assert(self._ifdefs[-1] == name, f"endif {name} while expecting {self._ifdefs[-1]}"):
                self._ifdefs = self._ifdefs[:-1]
        self._parent.line("`endif", remark=name)

    def initial(self):
        """ initial block """
        self._parent.assert_static(self._block is None, f"previous {self._block} block is still open", fatal=True)
        self._parent.line("initial")
        self._parent.line("    begin")
        self._block = "initial"

    def end(self):
        """ clock block """
        self._parent.assert_static(self._block is not None, "trying to end a block that was not openned", fatal=True)
        self._parent.line("    end")
        self._block = None

    def always(self, clk=None, cond=None, posedge=True):
        """ always block """
        self._parent.assert_static(self._block is None, f"previous {self._block} block is still open", fatal=True)
        line = "always"
        if clk is not None:
            line += f" @({misc.cond(posedge, 'posedge', 'negedge')} {clk})"
        self._parent.line(line)
        if cond is not None:
            self._parent.line(f"    if ({cond})")
            self._parent._set_used(cond)
        self._parent.line("    begin")
        self._block = "always"

    def loop(self, size, name=None, _task=False):
        """ for loop block """
        if name is None:
            name = self._parent._get_receive_name("loop")
        var = self._parent.logic(name, 32, _allow_str=True, _task=_task)
        self._parent.line(f"for ({var}=0; {var}<{size}; {var}={var}+1) begin")
        self._parent._set_used(size)
        self._block = "for"
        return var

    def delay(self, signal, num=1, posedge=True, wait_for=None):
        """ wait for a number of clock cycles """
        line = ""
        if wait_for is not None:
            line += f"while ({~wait_for})"
        if num > 1:
            line += f"repeat ({num}) "
        line += f"@({misc.cond(posedge, 'posedge', 'negedge')} {signal});"
        self._parent.line(line)

    def reset_released(self, clk):
        """ return a signal that indicates when reset has been released """
        self._parent._assert_type(clk, clock)
        self._parent.assert_static(clk.reset is not None or clk.rst_n is not None, f"{clk} has no reset", fatal=True)
        released = self._parent.logic(f"_{clk}_reset_released", initial=0, _allow_str=True)
        if clk.rst_n is not None:
            self._parent.line(f"always @(posedge {clk.rst_n})")
            self._parent.assign(released, "$time > 0", _allow_str=True)
        else:
            self._parent.line(f"always @(negedge {clk.reset})")
            self._parent.assign(released, "$time > 0", _allow_str=True)
        return released

    class p2v_tb_fifo:
        """ implements a SystemVerilog fifo """
        def __init__(self, parent, name, bits):
            self.parent = parent
            self.name = name
            self.bits = bits

            if misc._is_int(bits):
                msb = bits - 1
            else:
                msb = f"{bits}-1"
            self.parent.line(f"reg [{msb}:0] {name}[$];")


        def push(self, val):
            """ push to fifo """
            if isinstance(val, list):
                val = misc.concat(val)
            s = f"{self.name}.push_back({val});"
            self.parent.line(s)

        def pop(self):
            """ pop from fifo """
            s = f"{self.name}.pop_front()"
            return p2v_signal(None, s, bits=self.bits)

        def size(self):
            """ returns fifo fullness """
            s = f"{self.name}.size()"
            return p2v_signal(None, s, bits=32)

        def empty(self):
            """ returns fifo empty """
            return self.size() == 0
