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

import p2v_misc as misc
from p2v_struct import p2v_struct

class p2v_signal:
    def __init__(self, kind, name, bits=None, strct=None, used=False, driven=False, remark=None):
        assert type(name) is str, f"{kind} {name} is of type {type(name)} while expecting str"
        assert type(bits) in [str, int, list, tuple, float], bits
        assert misc._is_legal_name(name), f"{name} does not have a legal name"
        self.kind = kind
        self.name = name
        if strct is None:
            self.strct = None
        else:
            self.strct = p2v_struct(self, name, strct)
        self.ctrl = type(bits) is float
        if self.ctrl:
            assert bits in [1.0, -1.0], f"control {kind} {name} is {bits} but it can only be 1.0 (valid) or -1.0 (ready)"
            bits = int(bits)
        if type(bits) is list:
            assert len(bits) == 1 and type(bits[0]) is int, bits
            self.bits = bits[0]
            self.bus = True
            self.dim = [self.bits]
        elif type(bits) is tuple:
            self.bits = bits[0]
            self.bus = True
            self.dim = list(bits)
        else:
            self.bits = bits
            self.bus = not (type(bits) is int and bits == 1)
            self.dim = [self.bits]
        self.used = used
        self.driven = driven
        if type(bits) is str:
            self.driven_bits = None # don't check bit driven bits is a verilog parameter
        else:
            self.driven_bits = [False] * self.bits
        self.remark = remark

    def __str__(self):
        return f"{self.kind} {self._declare_bits()} {self.name} (driven={self.driven}, used={self.used})"

    def _declare_bits_dim(self, bits):
        if type(bits) is str:
            return f"[{bits}-1:0]"
        else:
            assert type(bits) is int and bits >= 1, f"{self.kind} {self.name} has 0 bits"
            if self.bus:
                return f"[{bits-1}:0]"
            else:
                return ""

    def _declare_bits(self):
        s = ""
        for bits in self.dim:
            s += self._declare_bits_dim(bits)
        return s
        
    def _get_ranges(self, idxs, ranges):
        if len(idxs) == 0:
            return ranges
        msb = lsb = idxs[0]
        i = 0
        for i in range(1, len(idxs)):
            if idxs[i] == (lsb - 1):
                lsb -= 1
            else:
                i -= 1
                break
        if msb == lsb:
            ranges.append(f"[{msb}]")
        else:
            ranges.append(f"[{msb}:{lsb}]")
        return self._get_ranges(idxs[i+1:], ranges=ranges)
                
    def _get_undriven_bits(self):
        undriven = []
        for i in range(self.bits):
            if not self.driven_bits[i]:
                undriven = [i] + undriven
        return undriven
                

    def is_logical_port(self):
        return self.kind in ["input", "output"]
        
    def is_port(self):
        return self.is_logical_port() or self.kind in ["inout"]

    def is_logic(self):
        return self.is_logical_port() or self.kind in ["logic"]
    
    def is_parameter(self):
        return self.kind in ["parameter"]
    
    def declare(self, delimiter=";"):
        s = f"{self.kind} "
        if self.is_logical_port():
            s += "logic "
        if self.is_logic():
            s += f"{self._declare_bits()} "
        s += self.name
        if self.is_parameter():
            s += f" = {self.bits}"
        s += delimiter
        if self.remark is not None:
            s += f" // {self.remark}"
        return s

    def check_used(self):
        return self.used
        
    def check_driven(self):
        if self.driven:
            return True
        if type(self.bits) is str:
            return False
        else:
            return len(self._get_undriven_bits()) == 0
    
    def check_partial_driven(self):
        if self.driven:
            return False
        if type(self.bits) is str:
            return False
        else:
            return len(self._get_undriven_bits()) < self.bits
            
    def get_undriven_ranges(self):
        if self.check_partial_driven():
            undriven = self._get_undriven_bits()
            return ", ".join(self._get_ranges(undriven, []))
        else:
            return None
            