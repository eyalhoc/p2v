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
from p2v_signal import p2v_kind

class p2v_task():
    """
    This class is a p2v task.
    """

    def __init__(self, parent):
        self._parent = parent
        self._p2v = p2v(parent, modname=parent._modname, parse=False)
        self._p2v._base_depth += 1

    def input(self, name="", bits=1, _allow_str=False):
        return self._p2v.input(name=name, bits=bits, _allow_str=_allow_str)

    def output(self, name="", bits=1, _allow_str=False):
        return self._p2v.output(name=name, bits=bits, _allow_str=_allow_str)

    def assign(self, tgt, src, _allow_str=False):
        self._p2v.assign(tgt, src, keyword="", _allow_str=_allow_str)

    def write(self, automatic=True):
        task_name = self.__class__.__name__
        lines = []
        lines.append(f"task {misc.cond(automatic, 'automatic ')}{task_name};")
        for port in self._p2v._get_signals([p2v_kind.INPUT, p2v_kind.OUTPUT]):
            lines.append(f"{port._kind} {port._declare_bits()} {port._name};")

        lines.append("")
        for port in self._p2v._get_signals([p2v_kind.OUTPUT]):
            lines.append(f"reg {port._declare_bits()} {port._name};")

        lines.append("begin")

        lines += self._p2v._lines

        lines.append("end")
        lines.append(f"endtask // {task_name}")
        lines.append("")

        self._parent._lines += lines

    def line(self, line="", remark=None):
        self._p2v.line(line, remark=remark)

    def display(self):
        pass
