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
                pin = pin["_NAME"]
            elif isinstance(pin, p2v_signal):
                pin = str(pin)
            if isinstance(wire, p2v_signal):
                wire = str(wire)
            self._parent._assert(isinstance(pin, str), f"pin {pin} is of type {misc._type2str(type(pin))} while expecting type str", fatal=True)
            self._parent._assert(pin in self._signals, f"module {self._modname} does not have a pin named {pin}", fatal=True)
            signal = self._signals[pin]
            self._parent._assert(signal._kind == kind, f"trying to connect {signal._kind} {pin} to {kind}")
            if kind == "parameter":
                self._parent._assert(pin not in self._params, f"parameter {pin} was previosuly assigned")
                self._params[pin] = wire
            else:
                if isinstance(wire, int):
                    wire = str(misc.dec(wire, signal._bits))
                self._parent._assert(isinstance(wire, str), f"wire {wire} is of type {misc._type2str(type(wire))} while expecting type str", fatal=True)
                self._parent._assert(pin not in self._pins, f"pin {pin} was previosuly assigned")
                if signal._bits != 0:
                    self._pins[pin] = wire
            if signal._strct is not None:
                strct = signal._strct
                for field_name in strct.fields:
                    self._connect(field_name, strct.update_field_name(wire, field_name), self._signals[field_name]._kind)

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
        self._parent._set_used(val)

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

    def connect_in(self, pin, wire="", _use_wire=False):
        """
        Connect input port to instance.

        Args:
            pin(str): Verilog pin name
            wire(str): Verilog wire name

        Returns:
            None
        """
        if not _use_wire:
            wire = self._get_wire(pin, wire)
        self._connect(pin, wire, kind=p2v_kind.INPUT)
        if not isinstance(wire, int):
            self._parent._set_used(wire)

    def connect_out(self, pin, wire="", _use_wire=False):
        """
        Connect output port to instance.

        Args:
            pin(str): Verilog pin name
            wire(str): Verilog wire name

        Returns:
            None
        """
        if not _use_wire:
            wire = self._get_wire(pin, wire)
        self._connect(pin, wire, kind=p2v_kind.OUTPUT)
        self._parent._set_driven(wire)

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

    def connect_auto(self, ports=False, suffix=""):
        """
        Automatically connect all unconnected ports to instance.

        Args:
            ports(bool): Define module ports for all unconnected instance ports
            suffix(str): Suffix all wires of unconnected instance ports

        Returns:
            None
        """
        for name in self._signals:
            signal = self._signals[name]
            if name not in self._pins:
                wire = name + suffix
                if not ports and wire not in self._parent._signals:
                    self._parent.logic(wire, signal._bits, _allow_str=True)
                if signal._kind == p2v_kind.INPUT:
                    if ports:
                        if not (wire in self._parent._signals and self._parent._signals[name]._kind == p2v_kind.INPUT):
                            self._parent.input(wire, signal._bits, _allow_str=True)
                    self.connect_in(name, wire, _use_wire=True)
                elif signal._kind == p2v_kind.OUTPUT:
                    if ports:
                        if not (wire in self._parent._signals and self._parent._signals[name]._kind == p2v_kind.OUTPUT):
                            self._parent.output(wire, signal._bits, _allow_str=True)
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
            for name in self._params:
                lines.append(f".{name}({self._params[name]}),")
            lines[-1] = lines[-1].rstrip(",")
            lines.append(")")
        lines.append(f"{instname} (")
        for name, val in self._pins.items():
            lines.append(f".{name}({val}), // {self._signals[name]._kind}{misc.cond(self._signals[name]._ctrl, ' ctrl')}")
        lines[-1] = lines[-1].replace(", //", " //", 1)
        lines.append(");")
        lines.append("")
        self._parent.line("\n".join(lines))
        signal = p2v_signal(p2v_kind.INST, instname, bits=1, used=True, driven=True)
        self._parent._add_signal(signal)
        self._pins = {}
        self._params = {}
        return signal
