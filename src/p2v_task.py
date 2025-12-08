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
p2v_task module. Responsible for creating verilog tasks.
"""

from p2v import p2v, misc
from p2v_signal import p2v_signal, p2v_kind

class p2v_task():
    """
    This class is a p2v task.
    """

    def __init__(self, parent):
        self._parent = parent
        self._p2v = p2v(parent, modname=parent._modname, parse=False)
        self._p2v._base_depth += 1

    def input(self, name="", bits=1):
        """ task input """
        return self._p2v.input(name=name, bits=bits)

    def output(self, name="", bits=1):
        """ task output """
        return self._p2v.output(name=name, bits=bits)

    def assign(self, tgt, src, _allow_str=False):
        """ task assignment """
        return self._p2v.assign(tgt, src, keyword="", _allow_str=_allow_str)

    def write(self, automatic=True):
        """ end task """
        task_name = self.__class__.__name__
        ports = []
        lines = []
        lines.append(f"task {misc.cond(automatic, 'automatic ')}{task_name};")
        for port in self._p2v._get_signals([p2v_kind.INPUT, p2v_kind.OUTPUT]):
            lines.append(f"{port._kind} {port._declare_bits(port._name)};")
            ports.append(port._name)

        lines.append("")
        for port in self._p2v._get_signals([p2v_kind.OUTPUT, p2v_kind.LOGIC]):
            lines.append(f"reg {port._declare_bits(port._name)};")

        lines.append("begin")

        lines += self._p2v._lines

        lines.append("end")
        lines.append(f"endtask // {task_name}")
        lines.append("")

        self._parent._lines += lines

        func = self._make_task_function(task_name)

        self._parent._add_signal(p2v_signal(p2v_kind.TASK, task_name, bits=0, strct=func, used=True, driven=True))
        return func

    def line(self, line="", remark=None):
        """ add line to task """
        return self._p2v.line(line, remark=remark)

    def logic(self, name="", bits=1, assign=None, _allow_str=False):
        """ define task varibale (reg) """
        return self._p2v.logic(name=name, bits=bits, assign=assign, _task=True, _allow_str=_allow_str)

    def loop(self, size, start_idx=0):
        """ start for loop in task body """
        name = self._parent._get_receive_name("loop")
        return self._p2v.tb.loop(size, start_idx=start_idx, name=name, _task=True)

    def end(self):
        """ end loop """
        return self._p2v.tb.end()

    def syn_off(self):
        """ translate off """
        return self._p2v.tb.syn_off()

    def syn_on(self):
        """ translate on """
        return self._p2v.tb.syn_on()

    def assert_property(self, condition=None, message=None, name=None, valid=None, fatal=True, clk=None):
        return self._p2v.assert_property(clk=clk, condition=condition, message=message, \
                                         name=name, valid=valid, fatal=fatal, concurrent=False)

    def display(self, s, params=None, cond=None):
        """ Verilog display """
        return self._p2v.tb.display(s, params=params, cond=cond)

    def delay(self, signal, num=1, posedge=True, wait_for=None):
        """ wait fixed number of cycles or wait for event """
        return self._p2v.tb.delay(signal, num=num, posedge=posedge, wait_for=wait_for)

    def exec(self, func, cond=None):
        """ execute verilog task """
        return self._p2v.exec(func, cond=cond)

    def readmemh(self, filename, dim):
        """ read hex file into memory (2d reg) """
        assert len(dim) == 2, "readmemh memory must be 2d"
        readmemh_array = self.logic(dim)
        self.line(f"$readmemh({filename}, {readmemh_array});")
        return readmemh_array

    def fopen(self, filename):
        """ open file """
        fd = self.logic(32, assign=f'$fopen({filename}, "r")', _allow_str=True)
        return fd

    def fclose(self, fd):
        """ close file """
        self.line(f"$fclose({fd});")

    def get_data(self, fd, bits=8):
        """ get data from file """
        _data = self._parent._get_receive_name("get_data")
        _status = self.logic(f"_status_{_data}", 32, _allow_str=True)
        _line = self.logic(f"_line_{_data}", bits*8, _allow_str=True) # 8 bits for char
        _data = self.logic(bits)
        self.assign(_status, f"$fgets({_line}, {fd})", _allow_str=True)
        self.assign(_status, f'$sscanf({_line}, "%x", {_data})', _allow_str=True)
        return _data

    def _make_task_function(self, task_name):
        def task_func(*args):
            args_str = []
            for arg in args:
                args_str.append(str(arg).strip())
            return f"{task_name}({', '.join(args_str)});"
        task_func.__name__ = task_name
        return task_func
