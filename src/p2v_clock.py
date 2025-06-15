# 
#  Copyright (C) 2025 Eyal Hochberg (eyalhoc@gmail.com)
#
#  This file is part of an opensource PythontoVerilog synthesizable converter.
#
#  Licensed under the GNU General Public License v3.0 or later (GPL3.0orlater).
#  You may use, modify, and distribute this software in accordance with the GPL3.0 terms.
#
#  This software is distributed WITHOUT ANY WARRANTY; without even the implied
#  warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
#  GPL3.0 license for full details: https://www.gnu.org/licenses/gpl3.0.html
# 
 
class p2v_clock:
        def __init__(self, name, rst_n=None, reset=None, remark=None):
            assert type(name) is str, name
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

        def  _cmp(self, clk):
            return self.name == clk.name and self.rst_n == clk.rst_n and self.reset == clk.reset

        def _declare(self):
            if self.name.endswith("clk"):
                prefix = self.name[:-3]
                if prefix != "":
                    prefix_str = f'"{prefix}"'
                else:
                    prefix_str = ""
            else:
                prefix = None
                
            if prefix is not None and self._cmp(clk(prefix)):
                return f'p2v_clock.clk({prefix_str})'
            elif prefix is not None and self._cmp(clk_arst(prefix)):
                return f'p2v_clock.clk_arst({prefix_str})'
            elif prefix is not None and self._cmp(clk_srst(prefix)):
                return f'p2v_clock.clk_srst({prefix_str})'
            elif prefix is not None and self._cmp(clk_2rst(prefix)):
                return f'p2v_clock.clk_2rst({prefix_str})'
                
            else: # non trivial clock
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


def clk(prefix=""):
    return p2v_clock(prefix+"clk", remark="clock with no reset")

def clk_arst(prefix=""):
    return p2v_clock(prefix+"clk", rst_n=prefix+"rst_n", remark="clock with async reset")

def clk_srst(prefix=""):
    return p2v_clock(prefix+"clk", reset=prefix+"reset", remark="clock with sync reset")

def clk_2rst(prefix=""):
    return p2v_clock(prefix+"clk", rst_n=prefix+"rst_n", reset=prefix+"reset", remark="clock with both async and sync resets")

default_clk = clk_arst()
