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
p2v_connect module
"""

import p2v_misc as misc
from p2v_signal import p2v_signal, p2v_kind
from p2v_clock import p2v_clock as clock
from p2v_struct import p2v_struct

from types import SimpleNamespace

STRCT_NAME = "_NAME"

class p2v_connect():
    """
    Class is the return value of a p2v module. It is used to connect the son instance to the parent module.
    """

    def __init__(self, parent, modname, signals, params=None, verilog=False):
        if params is None:
            params = {}
        self._parent = parent
        self._modname = modname
        self._signals = signals
        self._pins = {}
        self._strct_pins = []
        self._remarks = {}
        self._params = params
        self._verilog = verilog

    def _connect_clocks(self, pin, wire, kind):
        self._parent._assert(isinstance(pin, clock), f"trying to connect clock {wire} to a non clock signal {pin}", fatal=True)
        self._parent._assert(isinstance(wire, clock), f"trying to connect a non clock signal {wire} to clock {pin}", fatal=True)
        self._connect(pin.name, wire.name, kind)
        if pin.rst_n is not None and wire.rst_n is not None:
            self._connect(pin.rst_n, wire.rst_n, kind)
        if pin.reset is not None and wire.reset is not None:
            self._connect(pin.reset, wire.reset, kind)

    def _connect(self, pin, wire, kind):
        if isinstance(pin, clock) or isinstance(wire, clock):
            self._connect_clocks(pin, wire, kind)
        else:
            if isinstance(pin, dict):
                pin = pin[STRCT_NAME]
            elif isinstance(pin, p2v_signal):
                pin = str(pin)
            if isinstance(wire, p2v_signal):
                wire = str(wire)
            self._parent._assert(isinstance(pin, str), f"pin {pin} is of type {misc._type2str(type(pin))} while expecting type str", fatal=True)
            self._parent._assert(pin in self._signals, f"module {self._modname} does not have a pin named {pin}", fatal=True)
            signal = self._signals[pin]
            self._parent._assert(signal._kind == kind, f"trying to connect {signal._kind} {pin} to {kind}")

            remark = self._parent._get_remark(depth=4)
            if remark is not None:
                self._remarks[pin] = remark.strip()
            if kind == p2v_kind.PARAMETER:
                self._parent._assert(pin not in self._params, f"parameter {pin} was previosuly assigned")
                self._params[pin] = wire
            else:
                if isinstance(wire, int):
                    wire = str(misc.dec(wire, signal.bits()))
                self._parent._assert(isinstance(wire, str), f"wire {wire} is of type {misc._type2str(type(wire))} while expecting type str", fatal=True)
                self._parent._assert(pin not in self._pins, f"pin {pin} was previously assigned", fatal=True)
                if signal._bits != 0:
                    self._pins[pin] = wire
                if isinstance(signal._strct, p2v_struct):
                    self._connect_struct(strct=signal._strct, wire=wire)

    def _connect_struct(self, strct, wire):
        self._strct_pins.append(wire)
        for field_name in strct.fields:
            if field_name in self._pins: # struct assignment is soft to allow specific field assignments
                continue
            if wire == "":
                if self._signals[field_name]._kind == p2v_kind.INPUT:
                    field_wire = misc.cond(self._signals[field_name]._ctrl, 1, 0)
                else:
                    field_wire = ""
            else:
                field_wire = strct.update_field_name(wire, field_name)
            self._connect(field_name, field_wire, self._signals[field_name]._kind)

    def _check_connected(self):
        for name in self._signals:
            signal = self._signals[name]
            if signal.is_port() and signal._bits != 0:
                self._parent._assert(name in self._pins, f"port {name} is unconnected")


    def connect_param(self, name, val):
        """
        Connect Verilog parameter to instance.

        Args:
            name(str): Verilog parameter name
            val(str): Verilog parameter name

        Returns:
            None
        """
        if isinstance(val, int):
            val = str(val)
        self._connect(name, val, kind=p2v_kind.PARAMETER)
        self._parent._set_used(val, allow=True)

    def _get_wire(self, pin, wire):
        if isinstance(wire, str) and wire == "":
            return pin
        if isinstance(pin, clock) or isinstance(wire, (clock, int)):
            return wire
        if self._verilog and isinstance(pin, str):
            pass
        else:
            self._parent._assert(isinstance(pin, (p2v_signal, dict)), f"pin is of type {misc._type2str(type(pin))} while expecting type {p2v_signal}", fatal=True)
        if isinstance(wire, str) and wire == "" or wire is None:
            pass
        else:
            if self._verilog and isinstance(wire, str):
                pass
            else:
                self._parent._assert(isinstance(wire, p2v_signal), f"wire is of type {misc._type2str(type(wire))} while expecting type {p2v_signal}", fatal=True)
            wire = str(wire)
        if isinstance(wire, p2v_signal):
            return str(wire)
        if wire is None:
            return ""
        return wire

    def connect_in(self, pin, wire="", _use_wire=False, drive=True):
        """
        Connect input port to instance.

        Args:
            pin(str): Verilog pin name
            wire(str): Verilog wire name
            drive(bool): set struct return fields as driven

        Returns:
            None
        """
        if isinstance(pin, dict) or isinstance(wire, dict):
            if isinstance(wire, int):
                for key in pin:
                    if isinstance(key, str) and key.startswith("_"):
                        continue
                    self.connect_in(pin[key], wire)
            else:
                self._parent._assert(isinstance(pin, dict) and isinstance(wire, dict), "when dict type is used for connect both pin and wire must be of type dict", fatal=True)
                for key in wire:
                    self.connect_in(pin[key], wire[key])
        else:
            if isinstance(wire, list):
                for w in wire:
                    if not isinstance(w, int):
                        self._parent._assert(isinstance(w, p2v_signal), f"{w} is of type {type(w)} while expecting p2v signal", fatal=True)
                        self._parent._assert(not w.is_parameter(), f"parameter {w} is not allowed on port concatenation", fatal=True)
                wire = misc.concat(wire)
            if isinstance(pin, SimpleNamespace):
                pin = vars(pin)

            if not _use_wire:
                wire = self._get_wire(pin, wire)
            self._connect(pin, wire, kind=p2v_kind.INPUT)
            if not isinstance(wire, int):
                self._parent._set_used(wire, drive=drive)

    def connect_out(self, pin, wire="", _use_wire=False):
        """
        Connect output port to instance.

        Args:
            pin(str): Verilog pin name
            wire(str): Verilog wire name

        Returns:
            None
        """
        if isinstance(pin, dict) or isinstance(wire, dict):
            if wire is None:
                for key in pin:
                    if isinstance(key, str) and key.startswith("_"):
                        continue
                    self.connect_out(pin[key], wire)
            else:
                self._parent._assert(isinstance(pin, dict) and isinstance(wire, dict), "when dict type is used for connect both pin and wire must be of type dict", fatal=True)
                for key in wire:
                    for w in wire:
                        if not isinstance(w, int):
                            self._parent._assert(isinstance(w, p2v_signal), f"{w} is of type {type(w)} while expecting p2v signal", fatal=True)
                            self._parent._assert(not w.is_parameter(), f"parameter {w} is not allowed on port concatenation", fatal=True)
                    self.connect_out(pin[key], wire[key])
        else:
            if isinstance(wire, list):
                wire = misc.concat(wire)
            if isinstance(pin, SimpleNamespace):
                pin = vars(pin)
            if not _use_wire:
                wire = self._get_wire(pin, wire)
            self._connect(pin, wire, kind=p2v_kind.OUTPUT)
            self._parent._set_driven(wire)
            if isinstance(pin, p2v_signal) and wire in self._parent._signals:
                self._parent._signals[wire]._pipe_stage += pin._pipe_stage
                self._parent._signals[wire]._initial_pipe_stage += pin._pipe_stage
                self._parent._signals[wire]._const = pin._const

    def connect_io(self, pin, wire="", _use_wire=False):
        """
        Connect inout port to instance.

        Args:
            pin(str): Verilog pin name
            wire(str): Verilog wire name

        Returns:
            None
        """
        if not _use_wire:
            wire = self._get_wire(pin, wire)
        self._connect(pin, wire, kind=p2v_kind.INOUT)

    def connect_auto(self, ports=False, suffix="", const=None):
        """
        Automatically connect all unconnected ports to instance.

        Args:
            ports(bool): Define module ports for all unconnected instance ports
            suffix(str): Suffix all wires of unconnected instance ports
            const([None, int]): Drive constant on inputs and set outputs unconnected

        Returns:
            None
        """
        self._parent._assert(not (ports and const), "unused ports cannot be connected both to constants and to ports", fatal=True)
        for name in self._signals:
            signal = self._signals[name]
            if name not in self._pins and name not in self._strct_pins and signal._bits != 0:
                wire = name + str(suffix)
                if not ports and const is None and signal.is_port() and wire not in self._parent._signals:
                    self._parent.logic(wire, signal._bits, _allow_str=True)
                if signal._kind == p2v_kind.INPUT:
                    if ports:
                        if not (wire in self._parent._signals and self._parent._signals[name]._kind == p2v_kind.INPUT):
                            self._parent.input(wire, signal._bits, _allow_str=True)
                    if const is not None:
                        self.connect_in(name, const)
                    else:
                        self.connect_in(name, wire, _use_wire=True)
                elif signal._kind == p2v_kind.OUTPUT:
                    if ports:
                        if not (wire in self._parent._signals and self._parent._signals[name]._kind == p2v_kind.OUTPUT):
                            self._parent.output(wire, signal._bits, _allow_str=True)
                    if const is not None:
                        self.connect_out(name, None)
                    else:
                        self.connect_out(name, wire, _use_wire=True)
                elif signal._kind == p2v_kind.INOUT:
                    if ports:
                        if not (wire in self._parent._signals and self._parent._signals[name]._kind == p2v_kind.INOUT):
                            self._parent.inout(wire, _allow_str=True)
                    self.connect_io(name, wire, _use_wire=True)

    def inst(self, instname=None, suffix=""):
        """
        Write instance to parent module.

        Args:
            instname(str): Explicitly define instance name
            suffix(str): Suffix module name to create instance name

        Returns:
            None
        """
        self._check_connected()
        lines = []
        if instname is None:
            instname = f"{self._modname.split('__')[0]}{suffix}"
        lines.append(f"{self._modname}")
        if len(self._params) > 0:
            lines.append("#(")
            for n, (name, val) in enumerate(self._params.items()):
                last = (n + 1) == len(self._params)
                line = f".{name}({self._params[name]})" + misc.cond(not last, ",")
                if name in self._remarks:
                    line += f" // {self._remarks[name]}"
                lines.append(line)
                if isinstance(val, p2v_signal):
                    self._parent._set_used(val)
            lines.append(")")
        lines.append(f"{instname} (")
        for n, (name, val) in enumerate(self._pins.items()):
            last = (n + 1) == len(self._pins)
            line = f".{name}({val})" + misc.cond(not last, ",")
            line += f" // {self._signals[name]._kind}{misc.cond(self._signals[name]._ctrl, ' ctrl')}{self._signals[name]._declare_bits()}"
            if name in self._remarks:
                line += f" // {self._remarks[name]}"
            lines.append(line)
        lines.append(");")
        lines.append("")
        self._parent.line("\n".join(lines))
        signal = p2v_signal(p2v_kind.INST, instname, bits=1, used=True, driven=True)
        self._parent._add_signal(signal)
        self._pins = {}
        self._remarks = {}
        self._params = {}

        for _name, _signal in self._signals.items():
            if _signal.is_task():
                new_f = self.wrap_task(_signal, instname)
                new_f.__name__ = f"{instname}.{_name}"
                setattr(signal, _name, new_f)
            else:
                setattr(signal, _name, p2v_signal(None, f"{instname}.{_name}", bits=0))
        return signal

    def wrap_task(self, sig, instname):
        def fn(*args, **kwargs):
            return f"{instname}.{sig._strct(*args, **kwargs)}"
        return fn
