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
p2v module. Responsible for behavioral code, building test-benches and testing.
"""

import time
import sys
import os
import re
import ast
import glob
import shutil
import logging
import traceback
import inspect
import argparse
import csv
import secrets # required internally by np.random # pylint: disable=unused-import

import p2v_misc as misc
from p2v_clock import clk_0rst, clk_arst, clk_srst, clk_2rst # needed for clock loading from gen csv file # # pylint: disable=unused-import
from p2v_clock import p2v_clock as clock
from p2v_clock import default_clk
from p2v_signal import p2v_signal
from p2v_connect import p2v_connect
from p2v_tb import p2v_tb, PASS_STATUS
import p2v_slang as slang
import p2v_tools

MAX_MODNAME = 150
MAX_DEPTH = 16
MAX_VAR_STR = 64
MAX_SEED = 64 * 1024
MAX_LOOP = 5

SIGNAL_TYPES = [clock, dict, int, float, list, str, tuple]

class p2v():
    """
    This is the main p2v class. All p2v modules inherit this class.
    """

    def __init__(self, parent=None, modname=None, parse=True):
        self._parent = parent
        self._modname = modname
        self._signals = {}
        self._lines = []
        self._params = {}
        self._sons = []

        if parent is None:
            self._outfiles = {}
            self._modules = {}
            self._bbox = {}
            self._processes = []
            self._libs = []
            self._cache = {"files":{}, "ports":{}, "conn":{}}
            self._depth = 0
            if parse:
                self._errors = []
                self._err_num = 0
                self._args = self._parse_args()
                self._create_outdir()
                self._logger = self._create_logger()
                self._search = self._build_seach_path()
                rtrn = self._parse_top()
                sys.exit(rtrn)
        else:
            self._args = parent._args
            try:
                # create new tb instance to sort out parent links but use previous seed
                self.tb = p2v_tb(self, seed=self._parent.tb.seed, set_seed=False) # pylint: disable=invalid-name
            except AttributeError:
                # create first tb instance and generate seed
                self.tb = p2v_tb(self, seed=self._args.seed, max_seed=MAX_SEED, set_seed=True)
            self._logger = parent._logger
            self._outfiles = parent._outfiles
            self._modules = parent._modules
            self._bbox = parent._bbox
            self._processes = parent._processes
            self._libs = parent._libs
            self._cache = parent._cache
            self._errors = parent._errors
            self._err_num = parent._err_num
            self._depth = parent._depth + 1
            self._search = parent._search

        self._assert(self._depth < MAX_DEPTH, f"reached max instance depth of {MAX_DEPTH}", fatal=True)

    def _get_stack(self):
        stack = []
        for s in traceback.extract_stack():
            if not os.path.basename(s.filename).startswith(__class__.__name__) and s.line != "":
                stack.append(s)
        return stack[1:]

    def _assert_type(self, var, var_types, fatal=True):
        if not isinstance(var_types, list):
            var_types = [var_types]
        if None in var_types:
            var_types.append(type(None))
        self._assert(type(var) in var_types, f"{var} of type {type(var)} must be in {misc._type2str(var_types)}", fatal=fatal)

    def _assert(self, condition, message, warning=False, fatal=False, stack_idx=-1):
        if condition:
            return True
        stop = self._args.stop_on == "WARNING" or (self._args.stop_on == "ERROR" and not warning)
        critical = fatal or stop
        stack = self._get_stack()
        if critical:
            if self._args.debug:
                raise Exception(message)
            err_stack = []
            for s in stack:
                err_stack.append(f"  File {s.filename}, line {s.lineno}, in {s.name}\n    {s.line}")
            log_info = []
            for err_str in err_stack:
                log_info.append(err_str)
            if len(log_info) > 0:
                log_info = ["Trace:"] + log_info + [""]
                self._logger.info("\n".join(log_info))
        try:
            filename = stack[stack_idx].filename
            lineno = stack[stack_idx].lineno
        except: # pylint: disable=bare-except
            filename = lineno = None
        self._error(message, filename=filename, lineno=lineno, warning=warning, fatal=fatal)
        if critical:
            sys.exit(1)
        return False

    def _raise(self, message):
        self._assert(False, message, fatal=True)

    def _error(self, s, filename=None, lineno=None, warning=False, fatal=False):
        details = ""
        if filename is not None:
            details += os.path.basename(filename)
            if lineno is not None:
                details += f"@{lineno}"
            vfilename = self._get_filename()
            if vfilename is not None:
                details += f"->{vfilename}"
            details += ": "
        err_str = f"{details}{s}"
        if err_str not in self._errors or fatal:
            self._errors.append(err_str)
            if warning:
                self._logger.warning(err_str)
            elif fatal:
                self._logger.fatal(err_str)
                self._err_num += 1
            else:
                self._logger.error(err_str)
                self._err_num += 1

    def _get_logfile(self):
        return f"{__class__.__name__}.log"

    def _create_outdir(self):
        if os.path.exists(self._args.outdir):
            if not os.listdir(self._args.outdir): # directory exists but it is empty
                pass
            elif self._args.rm_outdir:
                assert os.path.isfile(os.path.join(self._args.outdir, self._get_logfile())), f"cannot remove {self._args.outdir}, it does not look like a {__class__.__name__} output directory"
                shutil.rmtree(self._args.outdir, ignore_errors=True)
        if not os.path.exists(self._args.outdir):
            os.mkdir(self._args.outdir)
        rtl_dir = self._get_rtldir()
        if not os.path.exists(rtl_dir):
            os.mkdir(rtl_dir)

    def _create_logger(self):
        logname = os.path.join(self._args.outdir, self._get_logfile())

        logger = logging.getLogger()
        logger.setLevel(self._args.log.upper())
        formatter = logging.Formatter(f'{self.__class__.__name__}-%(levelname)s: %(message)s')

        stdout_handler = logging.StreamHandler(sys.stdout)
        stdout_handler.setLevel(self._args.log.upper())
        stdout_handler.setFormatter(formatter)

        file_handler = logging.FileHandler(logname)
        file_handler.setLevel(self._args.log.upper())
        file_handler.setFormatter(formatter)

        logger.addHandler(file_handler)
        logger.addHandler(stdout_handler)
        return logger

    def _build_seach_path(self):
        sys.path = []
        search = [os.getcwd()]
        for incdir in [os.path.dirname(self._get_top_filename())] + self._args.I + self._args.Im:
            dirname = os.path.abspath(incdir)
            if self._assert(os.path.isdir(dirname), f"search directory {incdir} does not exist (included by -I argument)", fatal=True):
                if dirname not in search:
                    search.append(dirname)
        for path in search:
            sys.path.append(path)
        search.append(self._get_rtldir())
        return search

    def _lint(self):
        if self._args.lint:
            if self._assert(p2v_tools.en[p2v_tools.LINT_BIN], f"cannot perform lint, {p2v_tools.LINT_BIN} is not installed", warning=self._args.allow_missing_tools):
                if self._modname is None:
                    top_filename = None
                else:
                    top_filename = self._get_filename()
                logfile, success = p2v_tools.lint(dirname=self._get_rtldir(), outdir=self._args.outdir, filename=top_filename)
                if self._assert(success, f"lint completed with errors:\n{misc._read_file(logfile)}"):
                    self._logger.info("verilog lint completed successfully")
                    return True
        return False

    def _comp(self):
        if self._args.sim:
            if self._assert(p2v_tools.en[p2v_tools.COMP_BIN], f"cannot perform verilog compile, {p2v_tools.COMP_BIN} is not installed", warning=self._args.allow_missing_tools):
                logfile, success = p2v_tools.comp(dirname=self._get_rtldir(), outdir=self._args.outdir, modname=self._modname, search=self._search, libs=self._libs)
                comp_str = misc._read_file(logfile)
                if self._assert(success and comp_str=="", f"verilog compilation completed with errors:\n{comp_str}"):
                    self._logger.info("verilog compilation completed successfully")
                    return True
        return False

    def _sim(self):
        if self._args.sim:
            if self._assert(p2v_tools.en[p2v_tools.SIM_BIN], f"cannot perform verilog simulation, {p2v_tools.SIM_BIN} is not installed", warning=self._args.allow_missing_tools):
                if self._comp():
                    logfile, success = p2v_tools.sim(dirname=self._args.outdir, outdir=self._args.outdir, pass_str=PASS_STATUS)
                    if self._assert(success, f"verilog simulation failed, logfile: {logfile}"):
                        self._logger.info("verilog simulation completed successfully")
                        return True
                    self._logger.debug("verilog simulation completed with errors:\n %s", misc._read_file(logfile))
        return False

    def _get_gen_args(self, top_class, params=None):
        if params is None:
            params = {}
        self._assert("gen" in dir(top_class), f"{top_class.__name__} is missing gen() function")
        return top_class.gen(self, **params)

    def _get_cmd(self):
        cmd = sys.executable
        for arg in sys.argv:
            if '"' in arg:
                arg = f"'{arg}'"
            cmd += " " + arg
        if self.tb.seed != 1:
            seed_str = f" -seed {self.tb.seed}"
            if not cmd.endswith(seed_str):
                cmd += seed_str
        return cmd

    def _get_top_class(self):
        top_module = self._get_top_modname()
        try:
            module = __import__(top_module)
        except ValueError:
            self._raise("p2v should not be imported only inherited")
        try:
            top_class = getattr(module, top_module)
        except AttributeError:
            self._raise(f"could not find class {self._get_top_modname()} in {self._get_top_filename()}")
        return top_class

    def _parse_top(self):
        rtrn = 0

        top_class = self._get_top_class()
        self = top_class(self) # pylint: disable=self-cls-assignment
        try:
            self.tb.seed
        except AttributeError:
            self.tb = p2v_tb(self, seed=self._args.seed, max_seed=MAX_SEED)
        misc._write_file(os.path.join(self._args.outdir, f"{__class__.__name__}.cmd"), self._get_cmd()) # write command line to file
        self._logger.info(f"starting with seed {self.tb.seed}")

        gen_loop = self._args.gen_num is not None or isinstance(self._args.params, list)
        if gen_loop:
            if misc._is_int(self._args.gen_num):
                iter_num = self._args.gen_num
            else:
                iter_num = len(self._args.params)
            gen_seeds = []
            for i in range(iter_num):
                gen_seeds.append(self.tb.rand_int(1, MAX_SEED))
        else:
            iter_num = 1

        for i in range(iter_num):
            _start_time = time.time()
            if gen_loop:
                self.tb._set_seed(gen_seeds[i])
                self._logger.info(f"starting gen iteration {i}/{iter_num-1}")
            if self._args.sim or not gen_loop:
                self.__init__(None, modname=misc.cond(not gen_loop, None, f"_tb{i}"), parse=False)
                top_connect = top_class.module(self, **self._args.params)

                for process in self._processes:
                    process.wait()

                self._logger.info(f"verilog generation completed {misc.cond(self._err_num == 0, 'successfully', 'with errors')} ({misc.ceil(time.time() - _start_time)} sec)")
                if top_connect is not None and self._err_num == 0:
                    self._lint()
                    self._sim()
            else:
                self.__init__(None, parse=False)
                if isinstance(self._args.params, list):
                    args = self._args.params[i]
                else:
                    args = self._get_gen_args(top_class, params=self._args.params)
                top_class.module(self, **args)
                self._lint()

        rtrn = int(self._err_num > 0)
        self._logger.info(f"completed {misc.cond(rtrn==0, 'successfully', 'with errors')}")
        return rtrn

    def _param_type(self, value):
        if os.path.isfile(value):
            list_of_params = []
            with open(value, newline='', encoding="utf-8") as csvfile:
                reader = csv.DictReader(csvfile, skipinitialspace=True)
                for row in reader:
                    args = {}
                    for key, val in row.items():
                        key, val = key.strip(), val.strip()
                        try:
                            args[key] = eval(val) # pylint: disable=eval-used
                        except NameError:
                            args[key] = eval(f'"{val}"') # pylint: disable=eval-used
                    list_of_params.append(args)
            return list_of_params
        return ast.literal_eval(value)

    def _parse_args(self):
        parser = argparse.ArgumentParser()
        parser.add_argument("-outdir", type=str, default="cache", help="directory for generated files")
        parser.add_argument("-rm_outdir", action="store_true", default=True, help="remove outdir at start")
        parser.add_argument("--rm_outdir", action="store_false", default=False, help="supress outdir removal")
        parser.add_argument('-I', default=[], action="append", help="append search directory")
        parser.add_argument('-Im', default=[], nargs='*', help="append multiple search directories (supports wildcard *)")
        parser.add_argument("-prefix", type=str, default="", help="prefix all files")
        parser.add_argument("-params", type=self._param_type, default={}, help="top module parameters, dictionary or csv file")
        parser.add_argument("-stop_on", default="CRITICAL", choices=["WARNING", "ERROR", "CRITICAL"], help="stop after non critical errors")
        parser.add_argument("-log", default="DEBUG", choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"], help="logging level")
        parser.add_argument("-allow_missing_tools", action="store_true", default=False, help="do not stop on missing dependencies")
        parser.add_argument("-lint", action="store_true", default=True, help="enable lint")
        parser.add_argument("--lint", action="store_false", default=False, help="supress lint")
        parser.add_argument("-sim", action="store_true", default=False, help="enable verilog simulation")
        parser.add_argument("--sim", action="store_false", default=True, help="supress verilog simulation")
        parser.add_argument("-sim_args", type=ast.literal_eval, default={}, help="simulation override arguments")
        parser.add_argument("-seed", type=int, default=1, help="simulation seed (0 is random)")
        parser.add_argument("-gen_num", type=int, help="generate random permutations")
        parser.add_argument("-indent", action="store_true", default=True, help="enable indent")
        parser.add_argument("--indent", action="store_false", default=False, help="supress indent")
        parser.add_argument("-header", type=str, help="copyright header for generated files")
        parser.add_argument("-debug", action="store_true", default=False, help=argparse.SUPPRESS)
        return parser.parse_args()

    def _get_top_filename(self):
        return sys.argv[0]

    def _get_top_modname(self):
        return os.path.basename(self._get_top_filename()).split(".")[0]

    def _get_clsname(self):
        if self.__class__.__name__ == __class__.__name__:
            return self._get_top_modname()
        return self.__class__.__name__

    def _get_last_line(self, skip_empty=True, skip_remark=False):
        line_idx = len(self._lines)
        while line_idx > 0:
            line_idx -= 1
            last_line = self._lines[line_idx]
            if skip_remark and misc._remove_spaces(last_line).startswith("//"):
                continue
            if skip_empty and misc._remove_spaces(last_line) == "":
                continue
            return line_idx, last_line
        return -1, None

    def _rm_line(self, line_idx):
        del self._lines[line_idx]

    def _add_signal(self, signal):
        if self._exists(): # is called from p2v_connect
            return self._signals[signal.name]
        self._assert(self._modname is not None, "module name was not set (set_modname() was not called)", fatal=True)
        if self._assert(signal.name not in self._signals, f"{signal.name} was previously defined"):
            self._signals[signal.name] = signal
        return signal

    def _get_signals(self, kinds=None):
        if kinds is None:
            kinds = []
        if isinstance(kinds, str):
            kinds = [kinds]
        signals = []
        for name in self._signals:
            signal = self._signals[name]
            if signal.kind in kinds:
                signals.append(signal)
        return signals

    def _get_module_header(self):
        lines = []
        lines.append(f"module {self._modname}")
        parameters = self._get_signals("parameter")
        if len(parameters) > 0:
            lines.append("#(")
            for signal in parameters:
                lines.append(signal.declare(delimiter=","))
            lines[-1] = lines[-1].replace(",", "", 1)
            lines.append(")")
        lines.append("(")
        for port in self._get_signals(["input", "output", "inout"]):
            if port.bits != 0:
                lines.append(port.declare(delimiter=","))
        lines[-1] = lines[-1].replace(",", "", 1)
        lines.append(");")
        lines.append("")
        return lines

    def _get_module_footer(self):
        lines = []
        lines.append("")
        lines.append("endmodule")
        return lines

    def _get_rtldir(self):
        return os.path.join(self._args.outdir, "rtl")

    def _get_outfile(self, ext="sv"):
        filename = f"{self._modname}.{ext}"
        return os.path.join(self._get_rtldir(), filename)

    def _get_modlines(self, lint=True):
        lines = []
        if self._args.header is not None:
            if self._assert(os.path.isfile(self._args.header), f"header file {self._args.header} does not exist"):
                lines += misc._read_file(self._args.header).split("\n")
        lines += self._get_module_header()
        if not lint:
            lines += [p2v_tools.lint_off()]
        lines += self._lines
        if not lint:
            lines += [p2v_tools.lint_on()]
        lines += self._get_module_footer()
        return lines

    def _write_lines(self, outfile, lines, indent=True):
        misc._write_file(outfile, "\n".join(lines))
        if indent and self._args.indent:
            if self._assert(p2v_tools.en[p2v_tools.INDENT_BIN], f"cannot perform verilog indentation, {p2v_tools.INDENT_BIN} is not installed", warning=self._args.allow_missing_tools):
                self._processes.append(p2v_tools.indent(outfile))

    def _exists(self):
        return self._modname in self._cache["conn"]

    def _get_connects(self, parent, modname, signals, params):
        connects = p2v_connect(parent, modname, signals, params=params)
        self._cache["conn"][modname] = connects
        return connects

    def _get_current_line(self):
        extracted = traceback.extract_stack()
        i = -1
        while extracted[i].filename == __file__:
            i -= 1
        return extracted[i].line

    def _get_remark(self):
        return None # - TBD - performance
        #line = self._get_current_line()
        #if "#" in line:
        #    return line.split("#")[-1]
        #return None

    def _get_names(self, wire):
        self._assert_type(wire, str)
        self._check_line_balanced(wire)
        return misc._get_names(wire)

    def _check_declared(self, wire):
        for name in self._get_names(wire):
            self._assert(name in self._signals, f"{name} was not declared", fatal=True)

    def _set_used(self, wire, allow=False, drive=True):
        if isinstance(wire, clock):
            for net in wire.get_nets():
                self._set_used(net, allow=allow)
        elif isinstance(wire, list):
            for name in wire:
                self._set_used(name, allow=allow)
        elif isinstance(wire, str) and wire in self._signals and (self._signals[wire].strct is not None):
            fields = self._signals[wire].strct.fields
            for field_name in fields:
                bits = fields[field_name]
                if bits > 0:
                    self._set_used(field_name, allow=allow)
                elif drive:
                    self._set_driven(field_name, allow=allow)
        else:
            self._assert(isinstance(wire, str), f"unknown type {type(wire)} for signal", fatal=True)
            wire = str(wire)
            for name in self._get_names(wire):
                self._check_declared(name)
                self._signals[name].used = True

    def _set_driven_str(self, wire, allow=False):
        arrays = []
        names = []
        for name in self._get_names(wire):
            if f"[{name}]" in wire.replace(" ", ""):
                if len(names) > 0:
                    arrays.append(names[-1])
                self._set_used(name) # array pointer
            else:
                names.append(name)
        if len(names) > 0:
            if len(names) > 1:
                concat_wire = wire.replace(" ", "")
                if concat_wire.startswith("{") and concat_wire.endswith("}"): # verilog concat
                    concat_wire = concat_wire.lstrip("{").rstrip("}")
                    for name in concat_wire.split(","):
                        self._set_driven(name, allow=allow)
                    return
            self._assert(len(names) == 1, f"illegal assignment to multiple signals {names}", fatal=True)
            name = names[0]
            self._check_declared(name)
            if name in arrays or self._get_signal_bits(wire) == self._signals[name].bits:
                if self._assert(not self._signals[name].driven or allow or name in arrays, \
                                f"{name} was previously driven"): # multiple dimentional arrays are often multiple driven (2 write port)
                    self._signals[name].driven = True
            else:
                msb, lsb = misc._get_bit_range(wire)
                if self._assert(msb < self._signals[name].bits, f"trying to drive {wire} when {name} has only {self._signals[name].bits} bits"):
                    for i in range(lsb, msb+1):
                        if self._assert(not self._signals[name].driven_bits[i] or allow, f"{misc.bit(name, i)} was previously driven"):
                            self._signals[name].driven_bits[i] = True

    def _set_driven(self, wire, allow=False):
        if self._exists(): # is called from p2v_connect
            return
        if isinstance(wire, clock):
            for net in wire.get_nets():
                self._set_driven(net, allow=allow)
        elif isinstance(wire, list):
            for name in wire:
                self._set_driven(name, allow=allow)
        elif isinstance(wire, str) and wire in self._signals and self._signals[wire].strct is not None:
            fields = self._signals[wire].strct.fields
            for field_name in fields:
                bits = fields[field_name]
                if bits > 0:
                    self._set_driven(field_name, allow=allow)
                else:
                    self._set_used(field_name, allow=allow)
        else:
            self._assert(isinstance(wire, str), f"unknown type {type(wire)} for signal", fatal=True)
            self._set_driven_str(wire, allow=allow)

    def _check_signals(self):
        for name in self._signals:
            signal = self._signals[name]
            self._assert(signal.check_used(), f"{signal.kind} {name} is unused", warning=True)
            if not signal.check_driven():
                if signal.check_partial_driven():
                    undriven_ranges = signal.get_undriven_ranges()
                    self._assert(signal.check_driven(), f"{signal.kind} {name} is partially undriven, bits: {undriven_ranges}")
                else:
                    self._assert(signal.check_driven(), f"{signal.kind} {name} is undriven")

    def _check_mod_loop(self):
        count = {}
        for name in self._sons:
            if name in count:
                count[name] = count[name] + 1
            else:
                count[name] = 1
        for name in count:
            self._assert(count[name] < MAX_LOOP, f"{name} was created {count[name]} times in module (performance loss)")

    def _check_line_balanced(self, line):
        for (open, close) in [("(", ")"), ("[", "]"), ("{", "}")]:
            for c in line:
                if c in [open, close]:
                    self._assert(misc._is_paren_balanced(line, open=open, close=close), f"unbalanced parentheses in: {line}", fatal=True)
                    break
        for q in ['"']:
            for c in line:
                if c == q:
                    self._assert(misc._is_quote_closed(line, q=q), f"unbalanced quote in : {line}", fatal=True)
                    break

    def _get_signal_bits(self, name):
        array_name = name.split("[")[0] # support arrays
        is_array = array_name in self._signals and len(self._signals[array_name].dim) > 1
        if misc._is_legal_name(name) or is_array:
            return self._signals[array_name].dim[-1]
        msb, lsb = misc._get_bit_range(name)
        return msb + 1 - lsb

    def _update_outhash(self, modname, outfile, lines):
        outhash = misc._get_hash("\n".join(lines))
        if modname in self._outfiles:
            if outhash != self._outfiles[modname]:
                self._write_lines(f"{outfile}.diff", lines)
                self._assert(False, f"files created with same name but different content: {outfile} {outfile}.diff", fatal=True)
        else:
            self._outfiles[modname] = outhash

    def _port(self, kind, name, bits=1, used=False, driven=False):
        self._assert(type(bits) in SIGNAL_TYPES, f"unknown type {bits} for port", fatal=True)
        if isinstance(name, clock):
            self._assert(bits == 1, f"{kind} clock {name} must be declared with bits = 1")
            for net in name.get_nets():
                self._port(kind, net, used=used, driven=driven)
        elif isinstance(name, list):
            for n in name:
                self._port(kind, n, bits=bits, used=used, driven=driven)
        elif isinstance(bits, dict):
            self._assert(kind in ["input", "output"], f"struct {name} is of illegal kind {kind}")
            signal = self._add_signal(p2v_signal(kind, name, bits=0, strct=bits, used=True, driven=True))
            fields = signal.strct.fields
            for field_name in fields:
                field_bits = fields[field_name]
                input_port = misc.cond(field_bits > 0, kind == "input", kind == "output")
                if input_port:
                    self.input(field_name, abs(field_bits))
                else:
                    self.output(field_name, abs(field_bits))
            return signal.strct.names
        else:
            if isinstance(bits, str):
                for bits_str in self._get_names(bits):
                    self._set_used(bits_str)
            self._add_signal(p2v_signal(kind, name, bits, used=used, driven=driven, remark=self._get_remark()))
        return None

    def _find_file(self, filename, allow_dir=False, allow=False):
        if filename in self._cache["files"]:
            return self._cache["files"][filename]
        found = None
        for dirname in self._search:
            fullname = os.path.join(dirname, filename)
            if os.path.isfile(fullname):
                self._assert(found is None, f"found different versions of file in srarch path: {found} {fullname}")
                found = fullname
            elif allow_dir and os.path.isdir(fullname):
                found = fullname
        if found is not None:
            self._cache["files"][filename] = found
            return found
        if not allow:
            if os.path.isabs(filename):
                self._raise(f"could not find file {filename}")
            else:
                self._raise(f"could not find file {filename} in:\n\t" + "\n\t".join(self._search))
        return None

    def _grep(self, pattern, filename):
        return len(re.findall(pattern, misc._read_file(filename)))

    def _find_module(self, modname, ext=None, allow=False):
        if ext is None:
            ext = [".v", ".sv"]
        if isinstance(ext, str):
            ext = [ext]
        for e in ext:
            filename = self._find_file(modname + e, allow=True)
            if filename is not None:
                if self._grep(rf"\Wmodule *{modname}\W", filename) == 0:
                    self._assert(self._grep(rf"\Wmodule *{modname.upper()}\W", filename) == 0, f"could not find {modname} in {filename} but found the module there in uppercase", fatal=True)
                    self._assert(self._grep(rf"\Wmodule *{modname.lower()}\W", filename) == 0, f"could not find {modname} in {filename} but found the module there in lowercase", fatal=True)
                if self._grep(r"\Wmodule ", filename) > 1 and filename not in self._libs: # multiple module file
                    self._libs.append(filename)
                return filename
        # coudln't find file maybe it is in library
        for dirname in self._search:
            for e in ext:
                for filename in glob.glob(f"{dirname}/*{e}"):
                    if self._grep(rf"\Wmodule *{modname}\W", filename) and filename not in self._libs:
                        self._libs.append(filename)
                        return filename
        if not allow:
            self._raise(f"could not find file for module {modname} in:\n\t" + "\n\t".join(self._search))
        return None

    def _extract_module(self, modname, remove_comments=True):
        filename = self._find_module(modname)
        s = misc._read_file(filename)
        if remove_comments:
            s = misc._comment_remover(s).replace("  ", " ").replace(f"{modname}(", f"{modname} (")

        # extract relevant module
        #s = re.sub(rf".*?\bmodule *{modname}\b", f"module {modname} ", s, flags=re.S) # remove everything before relevant module
        #s = re.sub(r"\bendmodule\b.*", "", s, flags=re.DOTALL) # remove everything after relevant module
        # performance problems - rewrote without regex
        while not s.startswith(f"module {modname} "):
            self._assert(f"module {modname} " in s, f"failed to extract module {modname} from {filename}", fatal=True)
            replace = s.split(f"module {modname} ")[0]
            s = s.replace(replace, "", 1)
        s = s.split("endmodule")[0] + " endmodule"
        return s

    def _empty_module(self, modname):
        s = self._extract_module(modname=modname, remove_comments=True)

        # ansi declare
        begin = re.findall(r"\bmodule\b[\s\S]*?;", s)
        functions = re.findall(r"\bfunction\b[\s\S]*?\bendfunction\b", s)
        end = ["endmodule"]

        # legacy declare
        s = re.sub(r"^.*?;\s*", "", s, flags=re.S) # remove module declare
        for name in ["task", "function"]:
            s = re.sub(rf"\b{name}\b[\s\S]*?\bend{name}\b", "", s)

        declare = re.findall(r"^[ \t]*(?:`.*|input.*?;|output.*?;|inout.*?;|reg.*?;|parameter.*?;|localparam.*?;)", s, re.MULTILINE)

        return begin + declare + functions + end

    def _fix_lint(self, filename):
        if p2v_tools.en[p2v_tools.LINT_BIN]:
            logfile, success = p2v_tools.lint(dirname=self._get_rtldir(), outdir=self._args.outdir, filename=filename)
            if not success:
                s = misc._read_file(logfile)
                lint_errs = re.findall(r"\/\* *verilator *lint_off[\s\S]*?\*\/", s)
                lint_off = "\n".join(lint_errs)
                lint_on = "\n".join(lint_errs).replace("lint_off", "lint_on")
                s = misc._read_file(filename)
                misc._write_file(filename, f"{lint_off}\n{s}\n{lint_on}")

    def _get_filename(self, modname=None):
        if self._modname is None:
            return None
        if modname is None:
            return f"{self._modname}.sv"
        return f"{modname}.sv"

    def _write_empty_module(self, modname):
        bbox_dir = os.path.join(self._args.outdir, "bbox")
        if not os.path.exists(bbox_dir):
            os.mkdir(bbox_dir)
        if modname not in self._bbox:
            empty_lines = self._empty_module(modname)
            empty_outfile = os.path.join(bbox_dir, f"{modname}.sv")
            self._write_lines(empty_outfile, empty_lines, indent=False)
            self._fix_lint(empty_outfile)
            self._bbox[modname] = empty_outfile
            self._logger.debug("created bbox: %s", os.path.basename(empty_outfile))

    def _get_verilog_ports(self, modname, params=None):
        self._assert_type(modname, str)
        if params is None:
            params = {}
        if modname in self._cache["ports"]:
            return self._cache["ports"][modname]
        filename = self._find_module(modname)
        ast = slang.get_ast(filename, modname, params=params)
        self._assert(ast is not None, f"failed to parse verilog file {filename}, manually create wrapper for module", fatal=True)
        ports =  slang.get_ports(ast)
        self._cache["ports"][modname] = ports
        return ports

    def _assign_clocks(self, tgt, src):
        self._assert_type(tgt, clock)
        self._assert_type(src, clock)
        self.line()
        if tgt.name in self._signals and self._signals[tgt.name].driven:
            pass
        else:
            self.assign(tgt.name, src.name)
        if tgt.rst_n is not None and src.rst_n is not None:
            if tgt.rst_n in self._signals and self._signals[tgt.rst_n].driven:
                pass
            else:
                self.assign(tgt.rst_n, src.rst_n)
        if tgt.reset is not None and src.reset is not None:
            if tgt.reset in self._signals and self._signals[tgt.reset].driven:
                pass
            else:
                self.assign(tgt.reset, src.reset)

    def _get_strct_signals(self, strct, data_only=True, ctrl_only=False):
        signals = []
        for name in strct:
            field_name = strct[name]
            if field_name in self._signals:
                signal = self._signals[field_name]
                if signal.ctrl and data_only:
                    continue
                if not signal.ctrl and ctrl_only:
                    continue
                signals.append(signal)
        return signals

    def _check_structs(self, tgt, src):
        self._check_declared(tgt)
        if not isinstance(src, int) and src is not None:
            self._check_declared(src)
            self._assert(self._signals[tgt].strct is not None, f"trying to assign struct {src} to a non struct signal {tgt}", fatal=True)
            self._assert(self._signals[src].strct is not None, f"trying to assign a non struct signal {src} to struct {tgt}", fatal=True)

    def _sample_structs(self, clk, tgt, src, ext_valid=None):
        self._check_structs(tgt, src)
        self.line()
        tgt_strct = self._signals[tgt].strct
        src_strct = self._signals[src].strct

        # control
        if tgt_strct.valid is None:
            valid = ext_valid
            ready = None
        else:
            self._assert(ext_valid is None, f"external valid {ext_valid} cannot be used with struct {tgt} that has an internal qualifier")
            if tgt_strct.ready is None:
                self._assert(src_strct.valid is not None, f"struct {tgt} has valid while {src} does not", fatal=True)
                valid = tgt_strct.valid
                ready = None
            else:
                self._assert(src_strct.valid is not None, f"struct {tgt} has valid while {src} does not", fatal=True)
                self._assert(src_strct.ready is not None, f"struct {tgt} has ready while {src} does not", fatal=True)
                valid = f"{src_strct.valid} & {src_strct.ready}"
                ready = src_strct.ready

        if ready is not None:
            if src_strct.ready in self._signals and self._signals[src_strct.ready].driven:
                pass
            else:
                self.assign(src_strct.ready, tgt_strct.ready)
        if valid is not None:
            self.sample(clk, tgt_strct.valid, src_strct.valid, valid=f"~{tgt_strct.valid}{misc.cond(src_strct.ready is not None, f' | ~{src_strct.ready}')}")
        self.line()

        # data
        self.line()
        tgt_fields = self._signals[tgt].strct.fields
        for tgt_field_name in tgt_fields:
            field_bits = tgt_fields[tgt_field_name]
            if field_bits == 0 or isinstance(field_bits, float):
                continue
            src_field_name = self._signals[src].strct.update_field_name(src, tgt_field_name)
            if src_field_name not in src_strct.fields: # support casting (best effort)
                continue
            if field_bits > 0 and not self._signals[tgt_field_name].driven:
                self.sample(clk, tgt_field_name, src_field_name, valid=valid)
            if field_bits < 0 and not self._signals[src_field_name].driven:
                self.sample(clk, src_field_name, tgt_field_name, valid=valid)
        self.line()

    def _assign_structs(self, tgt, src, keyword="assign"):
        if isinstance(src, int):
            self._check_structs(tgt, None)
            self._assert(src == 0, "struct {src} can only be assigned to 0 when assigned to int", fatal=True)
        else:
            self._check_structs(tgt, src)
            self._assert(self._signals[src].strct is not None, f"trying to assign a non struct signal {src} to struct {tgt}", fatal=True)
        self.line()
        tgt_fields = self._signals[tgt].strct.fields
        for tgt_field_name in tgt_fields:
            field_bits = tgt_fields[tgt_field_name]
            if field_bits == 0:
                continue
            if isinstance(src, int):
                if field_bits > 0 and not self._signals[tgt_field_name].driven:
                    self.assign(tgt_field_name, 0, keyword=keyword)
            else:
                src_fields = self._signals[src].strct.fields
                src_field_name = self._signals[src].strct.update_field_name(src, tgt_field_name)
                if src_field_name not in src_fields: # support casting (best effort)
                    continue
                if field_bits > 0 and not self._signals[tgt_field_name].driven:
                    self.assign(tgt_field_name, src_field_name, keyword=keyword)
                if field_bits < 0 and not self._signals[src_field_name].driven:
                    self.assign(src_field_name, tgt_field_name, keyword=keyword)
        self.line()

    def _get_param_str(self, val):
        if isinstance(val, clock):
            val_str = val._declare()
        elif isinstance(val, str):
            val_str = f'"{val}"'
        else:
            val_str = str(val)
        if len(val_str) > MAX_VAR_STR:
            val_str = val_str[:MAX_VAR_STR] + "..."
        return val_str

    def _get_module_params(self, module_locals, suffix=True):
        simple_types = (int, bool, str)

        suf = []
        if len(module_locals) > 0:
            self.remark("module parameters:")
            for name in module_locals:
                if name.startswith("_"): # local parameter for set_param() modifications
                    continue
                if self._assert(name in self._params, f"module parameter {name} is missing set_param()"):
                    (_, param_remark, param_loose, param_suffix) = self._params[name]
                    if param_remark != "":
                        param_remark = f" # {param_remark}"
                else:
                    (_, param_remark, param_loose, param_suffix) = (None, "", False, None)
                val = module_locals[name]
                val_str = self._get_param_str(val)
                type_str = val.__class__.__name__

                if param_suffix is None:
                    param_remark += " (no affect on module name)"
                elif param_suffix != "":
                    suf.append(str(param_suffix))
                else:
                    if suffix and not param_loose:
                        self._assert(isinstance(val, simple_types), f"module name should be explicitly set when using parameter '{name}' of type {type_str}", fatal=True)
                    if isinstance(val, str):
                        val = misc._fix_legal_name(val)
                    if isinstance(val, simple_types):
                        suf.append(f"{name}{val}")

                self.remark(f"{name} = {val_str} ({type_str}){param_remark}")
            self.line()
        return suf


    def set_modname(self, modname=None, suffix=True):
        """
        Sets module name.

        Args:
            modname([None, str]): explicitly set module name
            suffix(bool): automatically suffix module name with parameter values

        Returns:
            True if module was already created False if not
        """
        self._assert_type(modname, [None, str])
        self._assert_type(suffix, bool)

        # create a new dictionary and remove self since it is illegal to delete items from locals
        module_locals = {}
        frame = inspect.currentframe()
        for name, value in frame.f_back.f_locals.items():
            if name != "self":
                module_locals[name] = value

        suf = self._get_module_params(module_locals, suffix=modname is None and suffix)
        if self._modname is None:
            self._modname = self._args.prefix
            if modname:
                self._modname += modname
            else:
                self._modname += self._get_clsname()
                if suffix and len(suf) > 0:
                    self._modname += "__" + "_".join(suf)
                    self._assert(len(self._modname) <= MAX_MODNAME, \
                    f"module name should be explicitly set generated name {self._modname} of {len(self._modname)} characters exceeds max od {MAX_MODNAME}", fatal=True)
        exists = self._exists()
        if exists:
            self._signals = self._cache["conn"][self._modname]._signals
            if module_locals != self._modules[self._modname]:
                for name in module_locals:
                    if not name.startswith("_"):
                        self._assert(module_locals[name] == self._modules[self._modname][name], \
                        f"module {self._modname} was generated with different {name} values but it does not affect module name", fatal=True)
        else:
            clsname = self._get_clsname()
            if clsname != "_test":
                self._find_file(f"{clsname}.py")
            self._modules[self._modname] = module_locals
        if self._parent is not None:
            self._parent._sons.append(self._modname)
        if self._parent.__class__.__name__ != self.__class__.__name__: # ignore nested recursions
            self.tb.register_test(module_locals)
        return exists

    def set_param(self, var, kind, condition=None, remark="", suffix="", default=None):
        """
        Declare module parameter and set assertions.

        Args:
            var: module parameter
            kind([type, list of type]): type of var
            condition([None, bool]): parameter constraints
            remark(str): comment
            suffix([None, str]): explicitly define parameter suffix
            default: if value matches default the parameter will not affect module name

        Returns:
            None
        """
        self._assert_type(condition, [None, bool])
        self._assert_type(remark, str)
        self._assert_type(suffix, [None, str])


        auto_suffix = suffix == ""
        line = self._get_current_line().replace(" ", "").split("#")[0]
        self._check_line_balanced(line)
        name = line.split("set_param(")[1].split(",")[0]

        if default is not None and var == default:
            suffix = None
        elif kind is clock and auto_suffix:
            if var != default_clk:
                suffix = str(var)
        if not isinstance(kind, list):
            kind = [kind]
        for n, next_kind in enumerate(kind):
            if next_kind is None:
                kind[n] = type(None)
        self._assert(isinstance(var, tuple(kind)), f"{name} is of type {misc._type2str(type(var))} while expecting it to be in {misc._type2str(kind)}", fatal=True)
        loose = condition is None
        if not loose:
            var_str = misc.cond(isinstance(var, str), f'"{var}"', var)
            self._assert(condition, f"{name} = {var_str} failed to pass its assertions", fatal=True)
        self._params[name] = (var, remark, loose, suffix)

    def get_fields(self, strct, attrib="name"):
        """
        Get struct fields.

        Args:
            strct(dict): p2v struct
            attrib(str): field attribute to extract

        Returns:
            list of field names (or other attribute)
        """
        self._assert_type(strct, dict)
        self._assert_type(attrib, str)
        vals = []
        signals = self._get_strct_signals(strct)
        for signal in signals:
            if attrib == "name":
                vals.append(signal.name)
            elif attrib == "bits":
                vals.append(signal.bits)
            else:
                self._raise(f"unknown struct attribute {attrib}")
        return vals

    def gen_rand_args(self, override=None):
        """
        Generate random module parameters and register in csv file.

        Args:
            override(dict): explicitly set these parameters overriding random values

        Returns:
            random arguments (dict)
        """
        if override is None:
            override = {}
        self._assert_type(override, dict)
        self._assert("gen" in dir(self), f"{self._get_clsname()} is missing gen() function")
        for name in self._args.sim_args:
            override[name] = self._args.sim_args[name]
        gen_args = {}
        if len(override) > 0:
            sig = inspect.signature(self.gen) # pylint: disable=no-member
            for sig_name in list(sig.parameters.keys()):
                if sig_name in override:
                    gen_args[sig_name] = override[sig_name]
        args = self.gen(**gen_args) # pylint: disable=no-member
        for name in override:
            if self._assert(name in args, f"trying to override unknown arg {name}, known: [{', '.join(args.keys())}]", fatal=True):
                args[name] = override[name]
        return args

    def line(self, line="", remark=None):
        """
        Insert Verilog code directly into module without parsing.

        Args:
            line(str): Verilog code (can be multiple lines)
            remark([None, str]): optional remark added at end of line

        Returns:
            None
        """
        self._assert_type(line, str)
        self._assert_type(remark, [None, str])
        if self._exists():
            return
        if remark is not None:
            line += misc._remark_line(remark)
        for l in line.split("\n"):
            self._lines.append(l)

    def remark(self, comment):
        """
        Insert a Verilog remark.

        Args:
            comment([str, dict]): string comment or one comment like per dictionary pair

        Returns:
            None
        """
        self._assert_type(comment, [str, dict])
        if isinstance(comment, dict):
            for key in comment:
                self.remark(f"{key} = {comment[key]}")
            self.line()
        else:
            self.line("", remark=comment)

    def parameter(self, name, val, local=False):
        """
        Declare a Verilog parameter.

        Args:
            name([str, clock]): parameter name
            val([int, str]): parameter value
            local(book): local parameter (localparam)

        Returns:
            None
        """
        self._assert_type(name, str)
        self._assert_type(val, [int, str])
        self._assert_type(local, bool)
        if self._exists():
            return
        self._add_signal(p2v_signal(misc.cond(local, "localparam", "parameter"), name, val, driven=True, remark=self._get_remark()))
        if local:
            self.line(f"localparam {name} = {val};", remark=self._get_remark())

    def input(self, name, bits=1):
        """
        Create an input port.

        Args:
            name([str, list, clock]): port name
            bits([clock, int, float, dict, tuple]): clock is used for p2v clock.\n\
                                             int is used fot number of bits.\n\
                                             float is used to mark struct control signals. \n\
                                             list is used to prevent a scalar signal (input x[0:0]; instead of input x;). \n\
                                             tuple is used for multi-dimentional Verilog arrays. \n\
                                             dict is used as a struct.

        Returns:
            p2v struct if type is struct otherwise None
        """
        self._assert_type(name, [str, list ,clock])
        self._assert_type(bits, SIGNAL_TYPES)
        return self._port("input", name, bits, driven=True)

    def output(self, name, bits=1):
        """
        Create an output port.

        Args:
            name([str, list, clock]): port name
            bits([clock, int, float, dict, tuple]): clock is used for p2v clock.\n\
                                             int is used fot number of bits.\n\
                                             float is used to mark struct control signals. \n\
                                             list is used to prevent a scalar signal (input x[0:0]; instead of input x;). \n\
                                             tuple is used for multi-dimentional Verilog arrays. \n\
                                             dict is used as a struct.

        Returns:
            p2v struct if type is struct otherwise None
        """
        self._assert_type(name, [str, list, clock])
        self._assert_type(bits, SIGNAL_TYPES)
        return self._port("output", name, bits, used=True)

    def inout(self, name):
        """
        Create an inout port.

        Args:
            name(str): port name

        Returns:
            None
        """
        self._assert_type(name, [str])
        if self._exists():
            return
        self._port("inout", name, bits=1, used=True, driven=True)

    def logic(self, name, bits=1, assign=None, initial=None):
        """
        Declare a Verilog signal.

        Args:
            name([clock, list, str]): signal name
            bits([clock, int, float, dict, tuple]): clock is used for p2v clock.\n\
                                             int is used fot number of bits.\n\
                                             float is used to mark struct control signals. \n\
                                             list is used to prevent a scalar signal (input x[0:0]; instead of input x;). \n\
                                             tuple is used for multi-dimentional Verilog arrays. \n\
                                             dict is used as a struct.
            assign([int, str, dict, None]): assignment value to signal using an assign statement
            initial([int, str, dict, None]): assignment value to signal using an initial statement

        Returns:
            p2v struct if type is struct otherwise None
        """
        self._assert_type(name, [clock, str, list])
        self._assert_type(bits, SIGNAL_TYPES)
        self._assert_type(assign, [int, str, dict, None])
        self._assert_type(initial, [int, str, dict, None])
        if isinstance(name, clock):
            for net in name.get_nets():
                self.logic(net)
        elif isinstance(name, list):
            for n in name:
                self.logic(n, bits=bits, assign=assign, initial=initial)
            return None
        elif isinstance(bits, dict):
            signal = self._add_signal(p2v_signal("logic", name, bits=0, strct=bits, used=True, driven=True))
            fields = signal.strct.fields
            for field_name in fields:
                self.logic(field_name, abs(fields[field_name]))
            return signal.strct.names
        else:
            for bits_str in self._get_names(str(bits)):
                self._set_used(bits_str)
            signal = self._add_signal(p2v_signal("logic", name, bits, remark=self._get_remark()))
            self.line(signal.declare())
        if assign is not None:
            self.assign(name, assign, keyword="assign")
            self.line()
        elif initial is not None:
            self.assign(name, initial, keyword="initial")
            self.line()
        return None

    def assign(self, tgt, src, keyword="assign"):
        """
        Signal assignment.

        Args:
            tgt([clock, str, dict]): target signal
            src([clock, int, str, dict]): source Verilog expression
            keyword(str): prefix to assignment

        Returns:
            None
        """
        self._assert_type(tgt, [clock, str, dict])
        self._assert_type(src, [clock, int, str, dict])
        self._assert_type(keyword, str)
        if self._exists():
            return
        if isinstance(tgt, clock) or isinstance(src, clock):
            self._assign_clocks(tgt, src)
        else:
            self._assert_type(tgt, [str, dict])
            self._assert_type(src, [str, dict, int])
            if (tgt in self._signals and (self._signals[tgt].strct is not None)) or (src in self._signals and (self._signals[src].strct is not None)):
                self._assign_structs(tgt, src, keyword=keyword)
            else:
                self._set_driven(tgt)
                if isinstance(src, int):
                    bits = self._get_signal_bits(tgt)
                    self._assert(bits > 0, f"illegal assignment to signal {tgt} of 0 bits")
                    src = misc.dec(src, bits)
                self._set_used(src, drive=False)
                self.line(f"{keyword} {tgt} = {src};", remark=self._get_remark())

    def sample(self, clk, tgt, src, valid=None, reset_val=0, bits=None):
        """
        Sample signal using FFs.

        Args:
            clk(clock): p2v clock (including optional reset/s)
            tgt(str): target signal
            src(str): source signal
            valid([str, None]): qualifier signal
            reset_val([int, str]): reset values
            bits([int, None]): explicitly specify number of bits

        Returns:
            None
        """
        if self._exists():
            return
        self._assert_type(clk, clock)
        self._assert_type(src, str)
        self._assert_type(tgt, str)
        self._assert_type(valid, [str, None])
        self._assert_type(reset_val, [int, str])
        self._assert_type(bits, [int, None])
        self._set_used(src, drive=False)
        if (tgt in self._signals and (self._signals[tgt].strct is not None)) or (src in self._signals and (self._signals[src].strct is not None)):
            self._sample_structs(clk, tgt, src, ext_valid=valid)
        else:
            self._set_driven(tgt)
            for net in clk.get_nets():
                self._set_used(net)
            if bits is None:
                bits = self._get_signal_bits(tgt)
            if isinstance(reset_val, int):
                if isinstance(bits, int):
                    reset_val = misc.dec(reset_val, bits)
                else:
                    reset_val = f"'{reset_val}"
            else:
                self._set_used(reset_val)

            self.line(f"always_ff @(posedge {clk.name}{misc.cond(clk.rst_n is not None, f' or negedge {clk.rst_n}')})")
            conds = []
            if clk.rst_n is not None:
                conds.append(f"if (!{clk.rst_n}) {tgt} <= {reset_val};")
            if clk.reset is not None:
                conds.append(f"if ({clk.reset}) {tgt} <= {reset_val};")
            if valid is not None:
                self._check_declared(valid)
                self._set_used(valid)
                conds.append(f"if ({valid}) {tgt} <= {src};")
            else:
                conds.append(f"{tgt} <= {src};")
            for n in range(1, len(conds)):
                conds[n] = f"else {conds[n]}"
            for cond in conds:
                self.line(cond)
            self.line()

    def allow_unused(self, name):
        """
        Set module signal/s as used.

        Args:
            name([clock, list, str]): name/s for signals to set used

        Returns:
            None
        """
        self._assert_type(name, [clock, list, str])
        if self._exists():
            return
        self._set_used(name, allow=True)

    def allow_undriven(self, name):
        """
        Set module signal as driven.

        Args:
            name([clock, list, str]): name/s for signals to set undriven

        Returns:
            None
        """
        self._assert_type(name, [clock, list, str])
        if self._exists():
            return
        self._set_driven(name, allow=True)

    def verilog_module(self, modname, params=None):
        """
        Instantiate Verilog module (pre-existing source file).

        Args:
            modname(str): Verilog module name
            params(dict): Verilog module parameters

        Returns:
            success
        """
        if params is None:
            params = {}
        self._assert_type(modname, str)
        self._assert_type(params, dict)
        if self._exists():
            self._assert(modname not in self._outfiles, f"module previosuly created with verilog module name {modname}", fatal=True)
            self._cache["conn"][modname]._parent = self
            return self._cache["conn"][modname]
        ports = self._get_verilog_ports(modname, params=params)
        if self._args.lint:
            self._write_empty_module(modname)
        return self._get_connects(parent=self, modname=modname, signals=ports, params=params)

    def assert_never(self, clk, condition, message, params=None, fatal=True):
        """
        Assertion on Verilog signals with clock (ignores condition during async reset if present).

        Args:
            condition(str): Error occurs when condition is True
            message(str): Error message
            params([str, list]): parameters for Verilog % format string
            fatal(bool): stop on error

        Returns:
            NA
        """
        if params is None:
            params = []
        self._assert_type(condition, str)
        self._assert_type(message, str)
        self._assert_type(params, [str, list])
        self._assert_type(fatal, bool)
        if not self._exists():
            name = misc._make_name_legal(message)
            wire = f"assert_never__{name}"
            self.logic(wire, assign=condition)
            self._set_used([clk, wire])
            full_messgae = f'"{message}"'
            if isinstance(params, str):
                params = [params]
            for param in params:
                full_messgae += f", {param}"
            if isinstance(clk, str):
                self._check_declared(clk)
                self.line(f"""always @({clk})
                                  if ({wire})
                                      {misc.cond(fatal, f'$fatal(0, {full_messgae});', f'$error({full_messgae});')}
                            """)
            else:
                self._assert_type(clk, clock)
                self.line(f"""always @(posedge {clk})
                                  if ({misc.cond(clk.rst_n is not None, f'{clk.rst_n} & ')}{wire})
                                      {misc.cond(fatal, f'$fatal(0, {full_messgae});', f'$error({full_messgae});')}
                            """)

    def assert_always(self, clk, condition, message, params=None, fatal=True):
        """
        Assertion on Verilog signals with clock (ignores condition during async reset if present).

        Args:
            condition(str): Error occurs when condition is False
            message(str): Error message
            params([str, list]): parameters for Verilog % format string
            fatal(bool): stop on error

        Returns:
            NA
        """
        if params is None:
            params = []
        self._assert_type(condition, str)
        self._assert_type(message, str)
        self._assert_type(params, [str, list])
        self._assert_type(fatal, bool)
        if not self._exists():
            self.assert_never(clk, condition=f"~({condition})", message=message, params=params, fatal=fatal)

    def check_never(self, condition, message, params=None, fatal=True):
        """
        Assertion on Verilog signals with no clock.

        Args:
            condition(str): Error occurs when condition is True
            message(str): Error message
            params([str, list]): parameters for Verilog % format string
            fatal(bool): stop on error

        Returns:
            Verilog assertion string
        """
        if params is None:
            params = []
        self._assert_type(condition, str)
        self._assert_type(message, str)
        self._assert_type(params, [str, list])
        self._assert_type(fatal, bool)
        if self._exists():
            return ""
        full_messgae = f'"{message}"'
        for param in params:
            full_messgae += f", {param}"
        return f"""if ({condition}) {misc.cond(fatal, f'$fatal(0, {full_messgae});', f'$error("{full_messgae}");')}"""

    def check_always(self, condition, message, params=None, fatal=True):
        """
        Assertion on Verilog signals with no clock.

        Args:
            condition(str): Error occurs when condition is False
            message(str): Error message
            params([str, list]): parameters for Verilog % format string
            fatal(bool): stop on error

        Returns:
            Verilog assertion string
        """
        if params is None:
            params = []
        self._assert_type(condition, str)
        self._assert_type(message, str)
        self._assert_type(params, [str, list])
        self._assert_type(fatal, bool)
        if self._exists():
            return ""
        return self.check_never(condition=f"~({condition})", params=params, message=message, fatal=fatal)

    def assert_static(self, condition, message, warning=False, fatal=True):
        """
        Assertion on Python varibales.

        Args:
            condition(bool): Error occurs when condition is False
            message(str): Error message
            warning(bool): issue warning instead of error
            fatal(bool): stop on error

        Returns:
            success
        """
        self._assert_type(condition, bool)
        self._assert_type(message, str)
        self._assert_type(warning, bool)
        self._assert_type(fatal, bool)
        return self._assert(condition, message, warning=warning, fatal=fatal and not warning)

    def write(self, lint=True):
        """
        Write the Verilog file.

        Args:
            lint(bool): don't run lint on this module

        Returns:
            p2v_connects struct with connectivity information
        """
        if self._exists():
            self._cache["conn"][self._modname]._parent = self._parent
            return self._cache["conn"][self._modname]
        self._assert(self._modname is not None, "module name was not set (set_modname() was not called)", fatal=True)
        self._assert(self._modname not in self._bbox, f"module {self._modname} previosuly used as verilog module", fatal=True)
        self._check_signals()
        self._check_mod_loop()
        lines = self._get_modlines(lint=lint)
        outfile = self._get_outfile()
        self._update_outhash(self._modname, outfile, lines)
        self._write_lines(outfile, lines)
        self._logger.debug("created: %s", os.path.basename(outfile))
        if self._parent is not None:
            self._parent._err_num += self._err_num
        return self._get_connects(parent=self._parent, modname=self._modname, signals=self._signals, params={})


# top constructor
if __name__ != "__main__" and os.path.basename(sys.argv[0]) != "pydoc.py":
    p2v()
