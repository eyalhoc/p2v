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
p2v_signal module. Responsible for p2v siganls.
"""

import p2v_misc as misc
from p2v_struct import p2v_struct

class p2v_signal:
    """
    This class is a p2v signal.
    """
    def __init__(self, kind, name, bits=None, strct=None, used=False, driven=False, remark=None):
        assert isinstance(name, str), f"{kind} {name} is of type {type(name)} while expecting str"
        if kind is not None:
            assert isinstance(bits, (str, int, list, tuple, float)), bits
            assert misc._is_legal_name(name), f"{name} does not have a legal name"
        self._kind = kind
        self._name = name
        if strct is None:
            self._strct = None
        else:
            self._strct = p2v_struct(self, name, strct)
        self._ctrl = isinstance(bits, float)
        if self._ctrl:
            assert bits in [1.0, -1.0], f"control {kind} {name} is {bits} but it can only be 1.0 (valid) or -1.0 (ready)"
            bits = int(bits)
        if isinstance(bits, list):
            assert len(bits) == 1 and isinstance(bits[0], int), bits
            self._bits = bits[0]
            self._bus = True
            self._dim = [self._bits]
        elif isinstance(bits, tuple):
            self._bits = bits[0]
            self._bus = True
            self._dim = list(bits)
        else:
            self._bits = bits
            self._bus = not (isinstance(bits, int) and bits == 1)
            self._dim = [self._bits]
        self._used = used
        self._driven = driven
        if isinstance(bits, str):
            self._driven_bits = None # don't check bit driven bits is a verilog parameter
        else:
            self._driven_bits = [False] * self._bits
        self._remark = remark

    def __str__(self):
        return self._name

    def _create(self, other, op):
        if isinstance(other, int):
            other = misc.dec(other, self._bits)
        expr = misc._remove_extra_paren(f"({self} {op} {other})")
        return p2v_signal(None, expr, bits=self._bits)


    def __add__(self, other):
        return self._create(other, "+")

    def __sub__(self, other):
        return self._create(other, "-")

    def __mul__(self, other):
        return self._create(other, "*")

    def __eq__(self, other):
        return self._create(other, "==")

    def __ne__(self, other):
        return self._create(other, "!=")

    def __lt__(self, other):
        return self._create(other, "<")

    def __le__(self, other):
        return self._create(other, "<=")

    def __gt__(self, other):
        return self._create(other, ">")

    def __ge__(self, other):
        return self._create(other, ">=")

    def __and__(self, other):
        return self._create(other, "&")

    def __or__(self, other):
        return self._create(other, "|")

    def __xor__(self, other):
        return self._create(other, "^")

    def __invert__(self):
        return p2v_signal(None, f"~{self}", bits=self._bits)

    def __lshift__(self, other):
        return self._create(other, "<<")

    def __rshift__(self, other):
        return self._create(other, ">>")


    def _declare_bits_dim(self, bits):
        if isinstance(bits, str):
            return f"[{bits}-1:0]"
        assert isinstance(bits, int) and bits >= 1, f"{self._kind} {self._name} has 0 bits"
        if self._bus:
            return f"[{bits-1}:0]"
        return ""

    def _declare_bits(self):
        s = ""
        for bits in self._dim:
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
        for i in range(self._bits):
            if not self._driven_bits[i]:
                undriven = [i] + undriven
        return undriven


    def is_logical_port(self):
        """
        Checks if signal is an input or an output.

        Args:
            NA

        Returns:
            bool
        """
        return self._kind in ["input", "output"]

    def is_port(self):
        """
        Checks if signal is a port.

        Args:
            NA

        Returns:
            bool
        """
        return self.is_logical_port() or self._kind in ["inout"]

    def is_logic(self):
        """
        Checks if signal is a port or logic.

        Args:
            NA

        Returns:
            bool
        """
        return self.is_logical_port() or self._kind in ["logic"]

    def is_parameter(self):
        """
        Checks if signal is a Verilog parameter.

        Args:
            NA

        Returns:
            bool
        """
        return self._kind in ["parameter", "localparam"]

    def declare(self, delimiter=";"):
        """
        Returns a string that declares the signal.

        Args:
            delimiter(str): string to mark end of line

        Returns:
            str
        """
        s = f"{self._kind} "
        if self.is_parameter():
            if misc._is_int(self._bits):
                s += "int "
            elif "'" in str(self._bits):
                width = str(self._bits).split("'", maxsplit=1)[0]
                if misc._is_int(width):
                    width = int(width)
                    s += "logic "
                    if width > 1:
                        s += f"[{width-1}:0] "
        if self.is_logical_port():
            s += "logic "
        if self.is_logic():
            s += f"{self._declare_bits()} "
        s += self._name
        if self.is_parameter():
            s += f" = {self._bits}"
        s += delimiter
        if self._remark is not None:
            s += f" // {self._remark}"
        return s

    def check_used(self):
        """
        Checks if the signal is used.

        Args:
            NA

        Returns:
            bool
        """
        return self._used

    def check_driven(self):
        """
        Checks if the signal is driven (assigned).

        Args:
            NA

        Returns:
            bool
        """
        if self._driven:
            return True
        if isinstance(self._bits, str):
            return False
        return len(self._get_undriven_bits()) == 0

    def check_partial_driven(self):
        """
        Checks if the signal is partial driven (the signal is multi-bit and only some bits are driven).

        Args:
            NA

        Returns:
            bool
        """
        if self._driven:
            return False
        if isinstance(self._bits, str):
            return False
        return len(self._get_undriven_bits()) < self._bits

    def get_undriven_ranges(self):
        """
        Returns a list of all undriven bit ranges.

        Args:
            NA

        Returns:
            list
        """
        if self.check_partial_driven():
            undriven = self._get_undriven_bits()
            return ", ".join(self._get_ranges(undriven, []))
        return None
