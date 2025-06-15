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

class p2v_clock:
        def __init__(self, name, rst_n=None, reset=None, remark=None):
                self.name = name
                self.rst_n = rst_n
                self.reset = reset
                self.remark = remark

        def __str__(self):
                return self.name
                
        def __eq__(self, other):        
            if isinstance(other, p2v_clock):
                return self.name == other.name and self.rst_n == other.rst_n and self.reset == other.reset
            else:
                return False

        def _declare(self):
            s = f"clock('{self.name}'"
            if self.rst_n is not None:
                s += f", rst_n='{self.rst_n}'"
            if self.reset is not None:
                s += f", reset='{self.reset}'"
            s += ")"
            if "," in s:
                return f'"{s}"'
            else:
                return s

        def get_nets(self):
            """
            Get all clock signals.

            Args:
                NA

            Returns:
                list of signals
            """
            nets = [self.name]
            if self.rst_n is not None:
                nets.append(self.rst_n)
            if self.reset is not None:
                nets.append(self.reset)
            return nets
        
        
default_clk = p2v_clock("clk", rst_n="rst_n", remark="default clock")
