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
import sys
from enum import Enum, auto

import p2v_misc as misc
from p2v_struct import p2v_struct


class p2v_kind(Enum):
    """
    This class is an enumeration of all p2v singal types.
    """
    INPUT = auto()
    OUTPUT = auto()
    INOUT = auto()
    LOGIC = auto()
    PARAMETER = auto()
    LOCALPARAM = auto()
    VAR = auto()
    CLOCK = auto()
    SYNC_RESET = auto()
    ASYNC_RESET = auto()
    ENUM = auto()
    INST = auto()
    TASK = auto()

    def __str__(self):
        return self.name.lower()

class p2v_type: # pylint: disable=too-few-public-methods
    """ complex p2v signals inherit this class to mark it is a signal """
    _bits = None

class p2v_signal:
    """
    This class is a p2v signal.
    """
    def __init__(self, kind, name, bits=None, strct=None, used=False, driven=False, remark=None):
        assert isinstance(kind, (p2v_kind, type(None))), f"unknown signal kind {kind}"
        assert isinstance(name, str), f"{kind} {name} is of type {type(name)} while expecting str"
        if kind is not None:
            assert isinstance(bits, (str, int, list, tuple, float)), bits
            assert misc._is_legal_name(name), f"{name} does not have a legal name"
        self._kind = kind
        self._name = name
        if strct is None:
            self._strct = None
        if isinstance(strct, dict):
            self._strct = p2v_struct(self, name, strct)
        else:
            self._strct = strct
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
            assert len(bits) <= 2, f"{self} bits {bits} exceeds max of 2 dimensions"
            self._bits = bits[-1]
            self._bus = True
            self._dim = []
            for b in bits:
                if hasattr(b, "bits"):
                    self._dim.append(b.bits())
                else:
                    self._dim.append(b)
        else:
            self._bits = bits
            self._bus = not (isinstance(bits, int) and bits == 1)
            self._dim = [self._bits]
        self._used = used
        self._driven = driven
        if isinstance(bits, str):
            self._driven_bits = None # don't check bit driven bits is a verilog parameter
        else:
            self._driven_bits = [False] * self.bits()
        self._initial_pipe_stage = 0
        self._pipe_stage = 0
        self._pipe = None
        self._initial = False
        self._const = False
        self._remark = remark

    def __str__(self):
        return self._name

    def __int__(self):
        raise RuntimeError("p2v_signal does not support int casting use class function .int() instead")

    def __hash__(self):
        return id(self)  # or use something meaningful

    def __iter__(self):
        vals = []
        for n in range(self.bits()):
            vals.append(self[n])
        return iter(vals)

    def __truediv__(self, other):
        return self._create(other, "/")

    def __floordiv__(self, other):
        return self._signal(f"{self} {other}", bits=self._bits)

    def __add__(self, other):
        if isinstance(other, (int, float)):
            if other == 0:
                return self
        return self._create(other, "+")

    def __radd__(self, other):
        if isinstance(other, (int, float)):
            if other < 0:
                return self.__sub__(-other)
            return self.__add__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __sub__(self, other):
        if isinstance(other, (int, float)):
            if other == 0:
                return self
        return self._create(other, "-")

    def __rsub__(self, other):
        if isinstance(other, int):
            other = misc.dec(other, max(self._bits, other.bit_length()))
            return other.__sub__(self)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __mul__(self, other):
        if isinstance(other, (int, float)):
            if other == 0:
                return 0
            if other == 1:
                return self
            if other == -1:
                return -self
        return self._create(other, "*")

    def __rmul__(self, other):
        if isinstance(other, (int, float)):
            return self.__mul__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __pow__(self, other):
        if isinstance(other, (int, float)):
            return self._create(other, "**", convert=False)
        raise RuntimeError("operand pow is unsupported for p2v signal")

    def __rpow__(self, other):
        if isinstance(other, (int, float)):
            return self.__pow__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __neg__(self):
        func_name = self._get_func_name()
        if issubclass(type(self._strct), p2v_type):
            if hasattr(self._strct, func_name):
                func = getattr(self._strct, func_name)
                return func(self)
        zero = self._signal(misc.dec(0, self._bits), bits=self._bits)
        return zero.__sub__(self)

    def __eq__(self, other):
        return self._create(other, "==", bits=1)

    def __req__(self, other):
        if isinstance(other, (int, float)):
            return self.__eq__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __ne__(self, other):
        return self._create(other, "!=", bits=1)

    def __rne__(self, other):
        if isinstance(other, (int, float)):
            return self.__ne__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __lt__(self, other):
        return self._create(other, "<", bits=1)

    def __rlt__(self, other):
        if isinstance(other, (int, float)):
            return self.__lt__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __le__(self, other):
        return self._create(other, "<=", bits=1)

    def __rle__(self, other):
        if isinstance(other, (int, float)):
            return self.__le__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __gt__(self, other):
        return self._create(other, ">", bits=1)

    def __rgt__(self, other):
        if isinstance(other, (int, float)):
            return self.__gt__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __ge__(self, other):
        return self._create(other, ">=", bits=1)

    def __rge__(self, other):
        if isinstance(other, (int, float)):
            return self.__ge__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __and__(self, other):
        if isinstance(other, (int, float)):
            if other == 0:
                return 0
            other = misc.dec(other, self._bits)
        return self._create(other, "&")

    def __rand__(self, other):
        if isinstance(other, (int, float)):
            return self.__and__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __or__(self, other):
        if isinstance(other, (int, float)):
            if other == 0:
                return self
            other = misc.dec(other, self._bits)
        return self._create(other, "|")

    def __ror__(self, other):
        if isinstance(other, (int, float)):
            return self.__or__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __xor__(self, other):
        if isinstance(other, (int, float)):
            if other == 0:
                return self
            other = misc.dec(other, self._bits)
        return self._create(other, "^")

    def __rxor__(self, other):
        if isinstance(other, (int, float)):
            return self.__xor__(other)
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __invert__(self):
        expr = misc._invert(self)
        return self._signal(expr, bits=self._bits)

    def __abs__(self):
        return self.abs()

    def __lshift__(self, other):
        if isinstance(other, int):
            expr = misc.pad(0, self, other)
            return self._signal(expr, bits=self._bits+other)
        return self._create(other, "<<")

    def __rlshift__(self, other):
        if isinstance(other, int):
            return misc.dec(other, bits=self._bits) << self
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __rshift__(self, other):
        if isinstance(other, int):
            assert self._bits >= other, f"cannot shift right {other} a {self._bits} bits signal"
            if self._bits == other:
                expr = misc.dec(0, self._bits)
            else:
                expr = misc.pad(other, self[other:self._bits])
            return self._signal(expr, bits=self._bits)
        return self._create(other, ">>")

    def __rrshift__(self, other):
        if isinstance(other, int):
            return misc.dec(other, bits=self._bits) >> self
        raise RuntimeError(f"unsupported type {type(other)} with p2v signal")

    def __getitem__(self, key):
        if isinstance(key, slice):
            if key.start is None:
                start = 0
            elif key.start < 0:
                start = key.start + self._bits
            else:
                start = key.start
            if key.stop is None:
                stop = self._bits
            elif key.stop < 0:
                stop = key.stop + self._bits
            else:
                stop = key.stop
            return self._bit_range(bits=stop-start, start=start)
        # single bit access
        if isinstance(key, int) and key < 0:
            key = self._bits + key

        if len(self._dim) > 1:
            bits = self._dim[-1]
            if isinstance(key, int):
                return self._signal(f"{self}[{key}]", bits=bits)
        else:
            bits = 1
        return self._bit_range(bits=bits, start=key)

    def _signal(self, expr, bits):
        return p2v_signal(None, str(expr), bits=bits)

    def _auto_pad(self, other):
        left, right = self, other
        if isinstance(other, p2v_signal) and isinstance(self._bits, int) and isinstance(other._bits, int):
            if abs(self._bits) > abs(other._bits):
                left = self
                right = other.pad(abs(self._bits) - abs(other._bits))
            elif abs(self._bits) < abs(other._bits):
                left = self.pad(abs(other._bits) - abs(self._bits))
                right = other
        return left, right

    def _get_func_name(self, depth=1):
        return "_" + sys._getframe(depth).f_code.co_name.replace("_", "")

    def _create(self, other, op, bits=None, auto_pad=True, convert=True):
        if convert and isinstance(other, (float, int)) and hasattr(self._strct, "to_bits"):
            if other != 0: # 0 has simplified operations since 0 int and 0 float are the same
                self._remark = str(other)
                other = self._strct.to_bits(other)
        func_name = self._get_func_name(2)
        if issubclass(type(self._strct), p2v_type):
            if hasattr(self._strct, func_name):
                func = getattr(self._strct, func_name)
                return func(self, other)
        if auto_pad:
            left, right = self._auto_pad(other)
        else:
            left, right = self, other
        if isinstance(right, int):
            right = misc.dec(right, max(self._bits, right.bit_length()))
        expr = misc._remove_extra_paren(f"({left} {op} {right})")
        if bits is None:
            bits = self._bits
        return self._signal(expr, bits=bits)

    def _update_strct(self, other):
        if isinstance(other, list):
            for o in other:
                self._update_strct(o)
        elif isinstance(other, p2v_signal) and other._strct is not None:
            self._strct = other._strct
            self._pipe = other._pipe

    def _declare_bits_dim(self, bits):
        if hasattr(bits, "bits"):
            bits = bits.bits()
        assert isinstance(bits, (str, int)), bits
        if isinstance(bits, int):
            assert bits >= 1, f"{self._kind} {self._name} has 0 bits"
        return misc._declare_bits(misc.cond(self._bus, [bits], bits))

    def _declare_bits(self, name=""):
        s = []
        for bits in self._dim:
            s.append(self._declare_bits_dim(bits))
        if name == "":
            return "".join(s)
        assert len(s) <= 2, "only 2d mem arrays are supported"
        if len(s) == 2:
            return s[1] + name + s[0]
        return s[0] + name

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

    def _bit_range(self, bits, start=0):
        if isinstance(start, p2v_signal): # verilog array access like a[ptr]
            rtrn = f"{self._name}[{start}]"
        else:
            end = start + bits - 1
            assert end >= start, f"msb {end} is less than lsb {start}"
            if start == end:
                rtrn = f"{self._name}[{start}]"
            else:
                rtrn = f"{self._name}[{end}:{start}]"
        return self._signal(rtrn, bits=bits)


    def is_logical_port(self):
        """
        Checks if signal is an input or an output.

        Args:
            NA

        Returns:
            bool
        """
        return self._kind in [p2v_kind.INPUT, p2v_kind.OUTPUT]

    def is_port(self):
        """
        Checks if signal is a port.

        Args:
            NA

        Returns:
            bool
        """
        return self.is_logical_port() or self._kind in [p2v_kind.INOUT]

    def is_logic(self):
        """
        Checks if signal is a port or logic.

        Args:
            NA

        Returns:
            bool
        """
        return self.is_logical_port() or self._kind in [p2v_kind.LOGIC]

    def is_parameter(self):
        """
        Checks if signal is a Verilog parameter.

        Args:
            NA

        Returns:
            bool
        """
        return self._kind in [p2v_kind.PARAMETER, p2v_kind.LOCALPARAM]

    def is_var(self):
        """
        Checks if signal is a Python variable.

        Args:
            NA

        Returns:
            bool
        """
        return self._kind in [p2v_kind.VAR]

    def is_task(self):
        """
        Checks if signal is a Verilog task.

        Args:
            NA

        Returns:
            bool
        """
        return self._kind in [p2v_kind.TASK]

    def is_clock(self):
        """
        Checks if signal is a clock.

        Args:
            NA

        Returns:
            bool
        """
        try:
            if self._strct.name._kind in [p2v_kind.CLOCK, p2v_kind.SYNC_RESET, p2v_kind.ASYNC_RESET]:
                return True
        except AttributeError:
            pass
        return self._kind in [p2v_kind.CLOCK, p2v_kind.SYNC_RESET, p2v_kind.ASYNC_RESET]

    def is_enum(self):
        """
        Checks if signal is an enumerated type.

        Args:
            NA

        Returns:
            bool
        """
        return self._kind in [p2v_kind.ENUM]

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

    def pad(self, left=0, right=0, val=0):
        """
        Verilog zero padding.

        Args:
            left(int): msb padding bits
            right(int): lsb padding bits
            val([int, p2v_signal]): value for padding

        Returns:
            p2v_signal
        """
        return misc.pad(left, self, right=right, val=val)

    def resize(self, bits, val=0, signed=False):
        """
        Verilog zero padding to total size.

        Args:
            bits(int): total number of bits with pad
            val([int, p2v_signal]): value for padding
            signed(bool): sign extend

        Returns:
            p2v_signal
        """
        if bits >= self.bits():
            return misc.pad(bits-self.bits(), self, val=misc.cond(signed, self[-1], val))
        return self[:bits]

    def bits(self):
        """
        Returns signal bits
        """
        _bits = 1
        for x in self._dim:
            _bits *= abs(x)
        return _bits

    def int(self, int_bits=16):
        """
        Convert to int
        """
        if hasattr(self._strct, "int"):
            return self._strct.int(self, int_bits=int_bits)
        raise RuntimeError("undefined int function")

    def abs(self):
        """
        Convert to int
        """
        if hasattr(self._strct, "abs"):
            return self._strct.abs(self)
        return self._signal(misc.cond(self[-1], misc.dec(0, self._bits) - self, self), bits=self._bits)

    def concat(self, num):
        """
        Verilog concatenation of signal like {NUM{x}}.

        Args:
            num(int): number of times to duplicate signal in concatenation

        Returns:
            p2v_signal
        """
        return misc.concat([self] * num)

    def pipe(self, pipeline):
        """
        sync signal to pipeline stage

        Args:
            pipeline(p2v_pipe): pipeline to sync to

        Returns:
            synched signal
        """
        pipeline.parent._assert(not self._const, f"constant signal {self} should not be pipelined")
        pipeline.parent._assert(self._pipe is None or self._pipe == pipeline, f"{self} used multiple pipelines at the same time", fatal=True)
        self._pipe = pipeline

        signal = None
        if pipeline.parent._pipe_stage == 0:
            return self

        if self._pipe_stage < pipeline.parent._pipe_stage:
            if not pipeline._signal_exists(self._name, stage=self._initial_pipe_stage):
                if self._initial_pipe_stage > 0:
                    name_d_initial = pipeline._get_delay_name(self._name, stage=0)
                    src = pipeline.parent.logic(name_d_initial, bits=self._bits, assign=self, _allow_str=True)
                else:
                    src = self

                name_d_initial = pipeline._get_delay_name(self._name, stage=self._initial_pipe_stage)
                signal = pipeline.parent.logic(name_d_initial, bits=self._bits, assign=src, _allow_str=True)
                signal._strct = self._strct

            for i in range(self._initial_pipe_stage, pipeline.parent._pipe_stage):
                if not pipeline._signal_exists(self._name, stage=i+1):
                    signal = pipeline._sample(self._name, bits=self._bits, stage=i)
            self._pipe_stage = pipeline.parent._pipe_stage
            signal._pipe = self._pipe
            return signal

        if self._initial_pipe_stage > 0 and (self._initial_pipe_stage == self._pipe_stage): # never progressed
            return self
        return pipeline._get_signal(self._name, stage=self._pipe_stage)
