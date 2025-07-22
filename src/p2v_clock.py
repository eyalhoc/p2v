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
p2v_clock module
"""

from p2v_signal import p2v_signal

class p2v_clock:
    """
    This class is a p2v clock which is a clock with attahces async and / or sync resets.
    """
    def __init__(self, name, rst_n=None, reset=None, remark=None):
        assert isinstance(name, str), name
        self.name = p2v_signal("clock", name, bits=1)
        if rst_n is None:
            self.rst_n = None
        else:
            self.rst_n = p2v_signal("async_reset", rst_n, bits=1)
        if reset is None:
            self.reset = None
        else:
            self.reset = p2v_signal("sync_reset", reset, bits=1)

        self._ready = False
        self._remark = remark

    def __str__(self):
        return str(self.name)

    def __eq__(self, other):
        if isinstance(other, p2v_clock):
            return self._cmp(other)
        return False

    def  _cmp(self, other):
        return str(self.name) == str(other.name) and \
               str(self.rst_n) == str(other.rst_n) and \
               str(self.reset) == str(other.reset)

    def _get_prefix(self):
        name = str(self.name)
        if name.endswith("clk"):
            prefix = name[:-3]
        elif name.startswith("clk"):
            prefix = name
        else:
            return None
        if self.rst_n is not None and not str(self.rst_n).startswith(prefix):
            return None
        if self.reset is not None and not str(self.reset).startswith(prefix):
            return None
        return prefix

    def _is_prefixed(self):
        prefix = self._get_prefix()
        if prefix is None:
            return False
        return self._cmp(clk_0rst(prefix)) or self._cmp(clk_arst(prefix)) or self._cmp(clk_srst(prefix)) or self._cmp(clk_2rst(prefix))

    def _declare(self):
        prefix = self._get_prefix()
        if prefix is None or prefix == "":
            prefix_str = ""
        else:
            prefix_str = f"'{prefix}'"

        if prefix is not None and self._cmp(clk_0rst(prefix)):
            return f'clk_0rst({prefix_str})'
        if prefix is not None and self._cmp(clk_arst(prefix)):
            return f'clk_arst({prefix_str})'
        if prefix is not None and self._cmp(clk_srst(prefix)):
            return f'clk_srst({prefix_str})'
        if prefix is not None and self._cmp(clk_2rst(prefix)):
            return f'clk_2rst({prefix_str})'

        # non trivial clock
        declare = f"clock('{self.name}'"
        if self.rst_n is not None:
            declare += f", rst_n='{self.rst_n}'"
        if self.reset is not None:
            declare += f", reset='{self.reset}'"
        declare += ")"
        if "," in declare:
            return f'"{declare}"'
        return declare

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


def _get_name(prefix=""):
    assert isinstance(prefix, str)
    if not prefix.startswith("clk"):
        return prefix + "clk"
    return prefix.strip("_")

def clk_0rst(prefix=""):
    """
    Create a clock with no resets.

    Args:
        prefix(str): prefix for all clock signals

    Returns:
        p2v clock
    """
    if prefix != "" and prefix[-1] != "_":
        prefix += "_"
    return p2v_clock(_get_name(prefix), remark="clock with no reset")

def clk_arst(prefix=""):
    """
    Create a clock with an async reset.

    Args:
        prefix(str): prefix for all clock signals

    Returns:
        p2v clock
    """
    if prefix != "" and prefix[-1] != "_":
        prefix += "_"
    return p2v_clock(_get_name(prefix), rst_n=prefix+"rst_n", remark="clock with async reset")

def clk_srst(prefix=""):
    """
    Create a clock with a sync reset.

    Args:
        prefix(str): prefix for all clock signals

    Returns:
        p2v clock
    """
    if prefix != "" and prefix[-1] != "_":
        prefix += "_"
    return p2v_clock(_get_name(prefix), reset=prefix+"reset", remark="clock with sync reset")

def clk_2rst(prefix=""):
    """
    Create a clock with both async and sync resets.

    Args:
        prefix(str): prefix for all clock signals

    Returns:
        p2v clock
    """
    if prefix != "" and prefix[-1] != "_":
        prefix += "_"
    return p2v_clock(_get_name(prefix), rst_n=prefix+"rst_n", reset=prefix+"reset", remark="clock with both async and sync resets")

default_clk = clk_arst()
