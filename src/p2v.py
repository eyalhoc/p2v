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
import linecache
import argparse
import csv
from types import SimpleNamespace as p2v_enum
import pyslang # pylint: disable=syntax-error

import p2v_misc as misc
from p2v_clock import clk_0rst, clk_arst, clk_srst, clk_2rst # needed for clock loading from gen csv file # # pylint: disable=unused-import
from p2v_clock import p2v_clock as clock
from p2v_clock import default_clk
from p2v_signal import p2v_signal, p2v_kind
from p2v_connect import p2v_connect
from p2v_fsm import p2v_fsm
from p2v_tb import p2v_tb, PASS_STATUS
from p2v_struct import FIELD_SEP
import p2v_tools

MAX_MODNAME = 150
MAX_DEPTH = 16
MAX_VAR_STR = 64
MAX_SEED = 64 * 1024
MAX_LOOP = 5
MAX_BITS = 8 * 1024

SIGNAL_TYPES = [clock, dict, int, float, list, str, tuple, p2v_enum]

class p2v():
    """
    This is the main p2v class. All p2v modules inherit this class.
    """

    def __init__(self, parent=None, modname=None, parse=True, register=True):
        self._parent = parent
        self._modname = modname
        self._register = register
        self._signals = {}
        self._lines = []
        self._params = {}
        self._sons = []

        if parent is None:
            self._outfiles = {}
            self._modules = {}
            self._bbox = {}
            self._libs = []
            self._processes = []
            self._cache = {"files":{}, "modules":{}, "ports":{}, "conn":{}, "src":[]}
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
            self._libs =  parent._libs
            self._processes = parent._processes
            self._cache = parent._cache
            self._errors = parent._errors
            self._err_num = parent._err_num
            self._depth = parent._depth + 1
            self._search = parent._search

        srcfile = __import__(self._get_clsname()).__file__
        if srcfile not in self._cache["src"]:
            self._cache["src"].append(srcfile)
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
                raise RuntimeError(message)
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
        search = [os.getcwd()]
        incdirs = [os.path.dirname(self._get_top_filename())] + self._args.I
        for incdir in self._args.Im:
            if os.path.isdir(incdir):
                incdirs.append(incdir)
        for incdir in incdirs:
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
            if self._assert(p2v_tools.check(self._args.lint_bin), f"cannot perform lint, {self._args.lint_bin} is not installed", warning=True):
                if self._modname is None:
                    top_filename = None
                else:
                    top_filename = self._get_filename()
                logfile, success = p2v_tools.lint(self._args.lint_bin, dirname=self._get_rtldir(), outdir=self._args.outdir, filename=top_filename)
                if self._assert(success, f"lint completed with errors:\n{misc._read_file(logfile)}"):
                    self._logger.info("verilog lint completed successfully")
                    return True
        return False

    def _comp(self):
        if self._args.sim:
            if self._assert(p2v_tools.check(self._args.comp_bin), f"cannot perform verilog compile, {self._args.comp_bin} is not installed", warning=True):
                logfile, success = p2v_tools.comp(self._args.comp_bin, dirname=self._get_rtldir(), outdir=self._args.outdir, modname=self._modname, search=self._search, libs=self._libs)
                comp_str = misc._read_file(logfile)
                if self._assert(success and comp_str=="", f"verilog compilation completed with errors:\n{comp_str}"):
                    self._logger.info("verilog compilation completed successfully")
                    return True
        return False

    def _sim(self):
        if self._args.sim:
            if self._assert(p2v_tools.check(self._args.sim_bin), f"cannot perform verilog simulation, {self._args.sim_bin} is not installed", warning=True):
                if self._comp():
                    logfile, success = p2v_tools.sim(self._args.sim_bin, dirname=self._args.outdir, outdir=self._args.outdir, pass_str=PASS_STATUS)
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
        if self._args.sim or self._args.gen_num is not None:
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
                self.__init__(None, modname=misc.cond(not gen_loop, None, f"_tb{i}"), parse=False) # pylint: disable=unnecessary-dunder-call
                top_connect = top_class.module(self, **self._args.params)

                for process in self._processes:
                    process.wait()

                self._logger.info(f"verilog generation completed {misc.cond(self._err_num == 0, 'successfully', 'with errors')} ({misc.ceil(time.time() - _start_time)} sec)")
                if self._err_num == 0:
                    self._lint()
                    if top_connect:
                        if not self._sim():
                            break
            else:
                self.__init__(None, parse=False) # pylint: disable=unnecessary-dunder-call
                if isinstance(self._args.params, list):
                    args = self._args.params[i]
                else:
                    args = self._get_gen_args(top_class, params=self._args.params)
                top_class.module(self, **args)
                self._lint()

        self._write_srcfiles()
        rtrn = int(self._err_num > 0)
        self._logger.info(f"completed {misc.cond(rtrn==0, 'successfully', 'with errors')}")
        return rtrn

    def _write_srcfiles(self):
        srcfiles = self._cache["src"] + list(self._cache["modules"].values())
        misc._write_file(os.path.join(self._args.outdir, "src.list"), "\n".join(srcfiles), append=True)

        if not self._args.sim: # directories might be used for Verilog files
            dirnames = []
            for srcfile in srcfiles:
                dirname = os.path.dirname(srcfile)
                if dirname not in dirnames:
                    dirnames.append(dirname)

            incdirs = self._args.I
            for incdir in self._args.Im:
                if os.path.isdir(incdir):
                    incdirs.append(incdir)
            for incdir in incdirs:
                incdir = os.path.abspath(incdir)
                self._assert(incdir in dirnames, f"include directory {incdir} never used", warning=True)

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
        parser.add_argument("-log", default="INFO", choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"], help="logging level")
        parser.add_argument("-seed", type=int, default=1, help="simulation seed (0 is random)")
        parser.add_argument("-gen_num", type=int, help="generate random permutations")
        parser.add_argument("-header", type=str, help="copyright header for generated files")
        parser.add_argument("-help", action="store_true", default=False, help="print module top parameters")
        parser.add_argument("-debug", action="store_true", default=False, help=argparse.SUPPRESS)


        # external tools
        parser.add_argument("-indent", action="store_true", default=True, help="enable indent")
        parser.add_argument("--indent", action="store_false", default=False, help="supress indent")
        parser.add_argument("-lint", action="store_true", default=True, help="enable lint")
        parser.add_argument("--lint", action="store_false", default=False, help="supress lint")
        parser.add_argument("-sim", action="store_true", default=False, help="enable verilog simulation")
        parser.add_argument("--sim", action="store_false", default=True, help="supress verilog simulation")

        parser.add_argument("-indent_bin", default="verible-verilog-format", choices=["verible-verilog-format"], help="Verilog indentation")
        parser.add_argument("-lint_bin", default="verilator", choices=["verilator", "verible-verilog-lint"], help="Verilog lint")
        parser.add_argument("-comp_bin", default="iverilog", choices=["iverilog"], help="Verilog compiler")
        parser.add_argument("-sim_bin", default="vvp", choices=["vvp"], help="Verilog simulator")
        parser.add_argument("-sim_args", type=ast.literal_eval, default={}, help="simulation override arguments")

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

    def _add_strct_attr(self, signal, names, fields):
        for key, value in names.items():
            if isinstance(value, dict):
                nested = p2v_enum()
                self._add_strct_attr(nested, value, fields=fields)
                setattr(signal, key, nested)
            else:
                if value in fields: # field must be missing due to having 0 bits
                    setattr(signal, key, p2v_signal(None, value, bits=fields[value]))

    def _add_signal(self, signal):
        if self._exists(): # is called from p2v_connect
            return self._signals[signal._name]
        self._assert(self._modname is not None, "module name was not set (set_modname() was not called)", fatal=True)
        if self._assert(signal._name not in self._signals, f"{signal._name} was previously defined"):
            if isinstance(signal._bits, int):
                self._assert(abs(signal._bits) <= MAX_BITS, f"{signal._name} uses {abs(signal._bits)} bits which exceeds maximum of {MAX_BITS}", warning=True)
            self._signals[signal._name] = signal
        if signal._strct is not None:
            self._add_strct_attr(signal, names=signal._strct.names, fields=signal._strct.fields)
        return signal

    def _get_signals(self, kinds=None):
        if kinds is None:
            kinds = []
        if isinstance(kinds, p2v_kind):
            kinds = [kinds]
        signals = []
        for name in self._signals:
            signal = self._signals[name]
            if signal._kind in kinds:
                signals.append(signal)
        return signals

    def _get_module_header(self):
        lines = []
        lines.append(f"module {self._modname}")
        parameters = self._get_signals(p2v_kind.PARAMETER)
        if len(parameters) > 0:
            lines.append("#(")
            for signal in parameters:
                lines.append(signal.declare(delimiter=","))
            lines[-1] = lines[-1].replace(",", "", 1)
            lines.append(")")
        lines.append("(")
        for port in self._get_signals([p2v_kind.INPUT, p2v_kind.OUTPUT, p2v_kind.INOUT]):
            if port._bits != 0:
                lines.append(port.declare(delimiter=","))
        lines[-1] = lines[-1].replace(",", "", 1)
        lines.append(");")
        lines.append("")
        return lines

    def _get_module_footer(self):
        lines = []
        lines.append("")
        lines.append(f"endmodule // {self._modname}")
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
            lines += [p2v_tools.lint_off(self._args.lint_bin)]
        lines += self._lines
        if not lint:
            lines += [p2v_tools.lint_on(self._args.lint_bin)]
        lines += self._get_module_footer()
        return lines

    def _write_lines(self, outfile, lines, indent=True):
        misc._write_file(outfile, "\n".join(lines))
        if indent and self._args.indent:
            if self._assert(p2v_tools.check(self._args.indent_bin), f"cannot perform verilog indentation, {self._args.indent_bin} is not installed", warning=True):
                self._processes.append(p2v_tools.indent(self._args.indent_bin, outfile))

    def _exists(self):
        return self._modname in self._cache["conn"]

    def _get_connects(self, parent, modname, signals, params, verilog=False):
        connects = p2v_connect(parent, modname, signals, params=params, verilog=verilog)
        for name, val in connects._signals.items():
            setattr(connects, name, val)
            # support access with dict
            if FIELD_SEP in name:
                d = misc._path_to_dict(name, value=val)
                key = list(d.keys())[0]
                if hasattr(connects, key):
                    prev = getattr(connects, key)
                    if isinstance(prev, dict):
                        d[key] = misc._merge_dict(d[key], prev)
                d[key]["_NAME"] = key
                setattr(connects, key, d[key])

        self._cache["conn"][modname] = connects
        return connects

    def _get_caller(self, depth):
        # Get the previous frame
        prev_frame = inspect.currentframe().f_back.f_back
        while depth > 1:
            prev_frame = prev_frame.f_back
            depth -= 1
        return prev_frame

    def _get_current_line(self, depth=2, caller=None):
        if caller is None:
            caller = self._get_caller(depth)
        filename = caller.f_code.co_filename
        lineno = caller.f_lineno
        return linecache.getline(filename, lineno).strip()

    def _get_remark(self, line=None, depth=1):
        if line is None:
            line = self._get_current_line(depth=depth)
        if "#" in line:
            return line.split("#")[-1]
        return None

    def _get_names(self, wire):
        wire = str(wire)
        self._assert_type(wire, str)
        self._check_line_balanced(wire)
        return misc._get_names(wire)

    def _check_declared(self, wire, allow=False):
        for name in self._get_names(wire):
            if allow and name not in self._signals:
                return False
            self._assert(name in self._signals, f"{name} was not declared", fatal=True)
        return True

    def _set_used(self, wire, allow=False, drive=True):
        if wire is None:
            return
        if isinstance(wire, p2v_signal):
            wire = str(wire)

        if isinstance(wire, clock):
            for net in wire.get_nets():
                self._set_used(net, allow=allow)
        elif isinstance(wire, list):
            for name in wire:
                self._set_used(name, allow=allow)
        elif isinstance(wire, str) and wire in self._signals and (self._signals[wire]._strct is not None):
            fields = self._signals[wire]._strct.fields
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
                if self._check_declared(name, allow=allow):
                    self._signals[name]._used = True

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
            if name in arrays or self._get_signal_bits(wire) == self._signals[name]._bits:
                if self._assert(not self._signals[name]._driven or allow or name in arrays, \
                                f"{name} was previously driven"): # multiple dimentional arrays are often multiple driven (2 write port)
                    self._signals[name]._driven = True
            else:
                msb, lsb = misc._get_bit_range(wire)
                if self._assert(msb < self._signals[name]._bits, f"trying to drive {wire} when {name} has only {self._signals[name]._bits} bits"):
                    for i in range(lsb, msb+1):
                        if self._assert(not self._signals[name]._driven_bits[i] or allow, f"{name}[{i}] was previously driven"):
                            self._signals[name]._driven_bits[i] = True

    def _set_driven(self, wire, allow=False):
        if self._exists(): # is called from p2v_connect
            return
        if wire is None:
            return
        if isinstance(wire, p2v_signal):
            wire = str(wire)

        if isinstance(wire, clock):
            for net in wire.get_nets():
                self._set_driven(net, allow=allow)
        elif isinstance(wire, list):
            for name in wire:
                self._set_driven(name, allow=allow)
        elif isinstance(wire, str) and wire in self._signals and self._signals[wire]._strct is not None:
            fields = self._signals[wire]._strct.fields
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
            self._assert(signal.check_used(), f"{signal._kind} {name} is unused", warning=True)
            if not signal.check_driven():
                if signal.check_partial_driven():
                    undriven_ranges = signal.get_undriven_ranges()
                    self._assert(signal.check_driven(), f"{signal._kind} {name} is partially undriven, bits: {undriven_ranges}")
                else:
                    self._assert(signal.check_driven(), f"{signal._kind} {name} is undriven")

    def _check_mod_loop(self):
        count = {}
        for name in self._sons:
            if name in count:
                count[name] = count[name] + 1
            else:
                count[name] = 1
        for name, val in count.items():
            self._assert(val < MAX_LOOP, f"{name} was created {val} times in module (performance loss)")

    def _check_line_balanced(self, line):
        line = str(line)
        for (open_char, close_char) in [("(", ")"), ("[", "]"), ("{", "}")]:
            for c in line:
                if c in [open_char, close_char]:
                    self._assert(misc._is_paren_balanced(line, open_char=open_char, close_char=close_char), f"unbalanced parentheses in: {line}", fatal=True)
                    break
        for q in ['"']:
            for c in line:
                if c == q:
                    self._assert(misc._is_quote_closed(line, q=q), f"unbalanced quote in : {line}", fatal=True)
                    break

    def _get_signal_bits(self, name):
        name = str(name)
        array_name = name.split("[", maxsplit=1)[0] # support arrays
        is_array = array_name in self._signals and len(self._signals[array_name]._dim) > 1
        if misc._is_legal_name(name) or is_array:
            return self._signals[array_name]._dim[-1]
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
        if isinstance(name, str) and name == "":
            name = self._get_receive_name(kind, depth=3)
        self._assert(type(bits) in SIGNAL_TYPES, f"unknown type {bits} for port", fatal=True)
        if isinstance(bits, p2v_enum):
            enum = vars(bits)
            bits = bits.BITS
        else:
            enum = None

        if isinstance(name, clock):
            self._assert(bits == 1, f"{kind} clock {name} must be declared with bits = 1")
            for net in name.get_nets():
                self._port(kind, str(net), used=used, driven=driven)
        elif isinstance(name, list):
            signals = []
            for n in name:
                signals.append(self._port(kind, n, bits=bits, used=used, driven=driven))
            return signals
        elif isinstance(bits, dict):
            self._assert(kind in [p2v_kind.INPUT, p2v_kind.OUTPUT], f"struct {name} is of illegal kind {kind}")
            signal = self._add_signal(p2v_signal(kind, name, bits=0, strct=bits, used=True, driven=True, remark=self._get_remark(depth=3)))
            fields = signal._strct.fields
            for field_name in fields:
                field_bits = fields[field_name]
                input_port = misc.cond(field_bits > 0, kind == p2v_kind.INPUT, kind == p2v_kind.OUTPUT)
                if input_port:
                    self.input(field_name, abs(field_bits), _allow_str=True)
                else:
                    self.output(field_name, abs(field_bits), _allow_str=True)
            return signal
        else:
            self._assert(misc._is_legal_name(str(name)), f"{kind} port {name} has an illegal name")
            if isinstance(bits, str):
                for bits_str in self._get_names(bits):
                    self._set_used(bits_str)
            signal = self._add_signal(p2v_signal(kind, name, bits, used=used, driven=driven, remark=self._get_remark(depth=3)))
            if enum is not None:
                for _name, _val in enum.items():
                    setattr(signal, _name, p2v_signal(None, f"({name} == {_val})", bits=bits))
            return signal
        return None

    def _find_file(self, filename, allow_dir=False, allow=False):
        if filename in self._cache["files"]:
            return self._cache["files"][filename]
        found = None
        for dirname in self._search:
            fullname = os.path.join(dirname, filename)
            if os.path.isfile(fullname):
                if found is None:
                    found = fullname
                else:
                    self._assert(misc._compare_files(found, fullname), f"found different versions of file in srarch path: {found} {fullname}")
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
        if modname in self._cache["modules"]:
            return self._cache["modules"][modname]
        if ext is None:
            ext = [".v", ".sv"]
        if isinstance(ext, str):
            ext = [ext]
        for e in ext:
            filename = self._find_file(modname + e, allow=True)
            if filename is not None:
                if self._grep(rf"\Wmodule *{modname}\W", filename) == 0:
                    self._assert(self._grep(rf"\Wmodule *{modname.upper()}\W", filename) == 0, \
                                 f"could not find {modname} in {filename} but found the module there in uppercase {modname.upper()}", fatal=True)
                    self._assert(self._grep(rf"\Wmodule *{modname.lower()}\W", filename) == 0, \
                                 f"could not find {modname} in {filename} but found the module there in lowercase {modname.lower()}", fatal=True)
                if self._grep(r"\Wmodule ", filename) > 1: # file has multiple modules
                    self._libs.append(filename)
                self._cache["modules"][modname] = filename
                return filename
        # coudln't find file maybe it is in library
        for dirname in self._search:
            for e in ext:
                for filename in glob.glob(f"{dirname}/*{e}"): # look for module in all verilog files in path
                    if self._grep(rf"\Wmodule *{modname}\W", filename): # found module in file that does not match module name
                        self._libs.append(filename)
                        self._cache["modules"][modname] = filename
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
        if p2v_tools.check(self._args.lint_bin):
            logfile, success = p2v_tools.lint(self._args.lint_bin, dirname=self._get_rtldir(), outdir=self._args.outdir, filename=filename)
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

    def _get_ports(self, filename, modname):
        signals = {}
        tree = pyslang.SyntaxTree.fromFile(filename)
        comp = pyslang.Compilation()
        comp.addSyntaxTree(tree)
        root = comp.getRoot()
        for inst in root.topInstances:
            if inst.name == modname:
                for port in inst.body.portList:
                    if hasattr(port.type, "scalarKind"):
                        bits = 1
                    else:
                        left = port.type.range.left
                        right = port.type.range.right
                        bits = abs(left - right) + 1

                    if port.direction.name == "In":
                        kind = p2v_kind.INPUT
                    elif port.direction.name == "Out":
                        kind = p2v_kind.OUTPUT
                    else:
                        kind = p2v_kind.INOUT
                    signals[port.name] = p2v_signal(kind, port.name, bits=bits)
                for param in inst.body.parameters:
                    bits = misc._to_int(str(param.value), allow=True)
                    signals[param.name] = p2v_signal(p2v_kind.PARAMETER, param.name, bits=bits)
        return signals

    def _get_verilog_ports(self, modname):
        self._assert_type(modname, str)
        if modname in self._cache["ports"]:
            return self._cache["ports"][modname]
        filename = self._find_module(modname)
        ports =  self._get_ports(filename, modname)
        self._cache["ports"][modname] = ports
        return ports

    def _assign_clocks(self, tgt, src):
        self._assert_type(tgt, clock)
        self._assert_type(src, clock)
        self.line()
        if str(tgt.name) in self._signals and self._signals[str(tgt.name)]._driven:
            pass
        else:
            self.assign(tgt.name, src.name)
        if tgt.rst_n is not None and src.rst_n is not None:
            if str(tgt.rst_n) in self._signals and self._signals[str(tgt.rst_n)]._driven:
                pass
            else:
                self.assign(tgt.rst_n, src.rst_n)
        if tgt.reset is not None and src.reset is not None:
            if str(tgt.reset) in self._signals and self._signals[str(tgt.reset)]._driven:
                pass
            else:
                self.assign(tgt.reset, src.reset)

    def _get_strct_signals(self, strct, data_only=True, ctrl_only=False, fields=None):
        signals = []
        for name, signal in strct.items():
            if fields is not None and name not in fields:
                continue
            signal = strct[name]
            if signal._ctrl and data_only:
                continue
            if not signal._ctrl and ctrl_only:
                continue
            signals.append(signal)
        return signals

    def _check_structs(self, tgt, src):
        self._assert_type(tgt, p2v_signal)
        self._assert_type(src, [p2v_signal, int, None])
        self._check_declared(tgt._name)
        if not isinstance(src, int) and src is not None:
            self._check_declared(src._name)
            self._assert(tgt._strct is not None, f"trying to assign struct {src} to a non struct signal {tgt}", fatal=True)
            self._assert(src._strct is not None, f"trying to assign a non struct signal {src} to struct {tgt}", fatal=True)

    def _sample_structs(self, clk, tgt, src, ext_valid=None):
        self._assert_type(tgt, p2v_signal)
        self._assert_type(src, [p2v_signal, int])
        self._check_structs(tgt, src)
        self.line()
        tgt_strct = tgt._strct
        src_strct = src._strct

        # control
        if tgt_strct.valid is None:
            valid = ext_valid
            ready = None
        else:
            self._assert(ext_valid is None, f"external valid {ext_valid} cannot be used with struct {tgt} that has an internal qualifier")
            if tgt_strct.ready is None:
                self._assert(src.valid is not None, f"struct {tgt} has valid while {src} does not", fatal=True)
                valid = tgt.valid
                ready = None
            else:
                self._assert(src.valid is not None, f"struct {tgt} has valid while {src} does not", fatal=True)
                self._assert(src.ready is not None, f"struct {tgt} has ready while {src} does not", fatal=True)
                valid = src.valid & src.ready
                ready = src.ready

        if ready is not None:
            if src_strct.ready in self._signals and self._signals[src_strct.ready]._driven:
                pass
            else:
                self.assign(self._signals[src_strct.ready], self._signals[tgt_strct.ready])
        if valid is not None:
            qual_valid = ~tgt.valid
            if src.ready is not None:
                qual_valid |= ~src.ready
            self.sample(clk, self._signals[tgt_strct.valid], self._signals[src_strct.valid], valid=qual_valid)
        self.line()

        # data
        self.line()
        tgt_fields = tgt._strct.fields
        for tgt_field_name in tgt_fields:
            field_bits = tgt_fields[tgt_field_name]
            if field_bits == 0 or isinstance(field_bits, float):
                continue
            src_field_name = src._strct.update_field_name(src._name, tgt_field_name.replace(tgt._name, "", 1))
            if src_field_name not in src_strct.fields: # support casting (best effort)
                continue
            if field_bits > 0 and not self._signals[tgt_field_name]._driven:
                self.sample(clk, self._signals[tgt_field_name], self._signals[src_field_name], valid=valid)
            if field_bits < 0 and not self._signals[src_field_name]._driven:
                self.sample(clk, self._signals[src_field_name], self._signals[tgt_field_name], valid=valid)
        self.line()

    def _assign_structs(self, tgt, src, keyword="assign"):
        self._assert_type(tgt, p2v_signal)
        self._assert_type(src, [p2v_signal, int])
        if isinstance(src, int):
            self._check_structs(tgt, None)
            self._assert(src == 0, "struct {src} can only be assigned to 0 when assigned to int", fatal=True)
        else:
            self._check_structs(tgt, src)
            self._assert(src._strct is not None, f"trying to assign a non struct signal {src} to struct {tgt}", fatal=True)
        self.line()
        tgt_fields = tgt._strct.fields
        for tgt_field_name in tgt_fields:
            field_bits = tgt_fields[tgt_field_name]
            if field_bits == 0:
                continue
            if isinstance(src, int):
                if field_bits > 0 and not self._signals[tgt_field_name]._driven:
                    self.assign(self._signals[tgt_field_name], 0, keyword=keyword)
            else:
                src_fields = src._strct.fields
                src_field_name = src._strct.update_field_name(src._name, tgt_field_name.replace(tgt._name, "", 1))
                if src_field_name not in src_fields: # support casting (best effort)
                    continue
                if field_bits > 0 and not self._signals[tgt_field_name]._driven:
                    self.assign(self._signals[tgt_field_name], self._signals[src_field_name], keyword=keyword)
                if field_bits < 0 and not self._signals[src_field_name]._driven:
                    self.assign(self._signals[src_field_name], self._signals[tgt_field_name], keyword=keyword)
        self.line()

    def _get_param_str(self, val):
        if isinstance(val, clock):
            val_str = val._declare()
        elif isinstance(val, str):
            val_str = f'"{val}"'
        elif isinstance(val, list):
            list_str = []
            for next_val in val:
                list_str.append(self._get_param_str(next_val))
            val_str = "[" + ", ".join(list_str) + "]"
        else:
            val_str = str(val)
        if len(val_str) > MAX_VAR_STR:
            val_str = val_str[:MAX_VAR_STR] + "..."
        return val_str

    def _get_module_params(self, module_locals, suffix=True):
        simple_types = (int, bool, str, clock)

        comments = [f"{self._get_clsname()} module parameters:"]
        suf = []
        if len(module_locals) > 0:
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
                    pass # param_remark += " (no effect on module name)"
                elif param_suffix != "":
                    suf.append(str(param_suffix))
                else:
                    if suffix and not param_loose:
                        self._assert(isinstance(val, simple_types), f"module name should be explicitly set when using parameter '{name}' of type {type_str}", fatal=True)
                    if isinstance(val, str):
                        val = misc._fix_legal_name(val)
                    if isinstance(val, simple_types):
                        suf.append(f"{name}{val}")

                comments.append(f" * {name} = {val_str} ({type_str}){param_remark}")

        if self._args.help:
            for comment in comments:
                print(comment)
            sys.exit(0)

        for comment in comments:
            self.remark(comment)
        self.line()
        return suf

    def _is_implicit_declare(self, name):
        if isinstance(name, list):
            return len(name)==1 and isinstance(name[0], int)
        if isinstance(name, p2v_signal):
            return not name.is_clock()
        return not isinstance(name, (str, list, clock))

    def _get_receive_name(self, cmd, depth=2):
        cmd = str(cmd)
        caller = self._get_caller(depth=depth)
        current_line = self._get_current_line(caller=caller)
        line = current_line.replace(" ", "").split("#")[0]
        name = line.split(f"{cmd}(")[0].split("=")[0]

        if "[" in name:
            caller_locals = caller.f_locals
            for var, val in caller_locals.items(): # variable keys
                name = name.replace(f"[{var}]", f"{FIELD_SEP}{val}")
            name = name.replace('["', FIELD_SEP).replace('"]', "") # string keys

        self._assert(misc._is_legal_name(name), f"missing receive variable for {cmd}", fatal=True)
        return name

    def _assert_property(self, clk, condition, message, name=None, fatal=True, property_type="assert"):
        self._assert_type(clk, [clock, None])
        self._assert_type(condition, p2v_signal)
        self._assert_type(message, str)
        self._assert_type(name, [None, str])
        self._assert_type(fatal, bool)
        self._assert_type(property_type, str)
        self._assert(property_type in ["assert", "assume", "cover"], f"unknown assertion property {property_type}")
        self._check_line_balanced(condition)

        if not self._exists():
            if name is None:
                name = misc._make_name_legal(message)
            else:
                self._assert(misc._is_legal_name(name), f"assertion name '{name}' is illegal", fatal=True)
            if message[0] != '"':
                full_messgae = f'"{message}"'
            else:
                full_messgae = message

            if property_type == "cover":
                err_str = f"$info({full_messgae})"
            elif fatal:
                err_str = f"$fatal(1, {full_messgae})"
            else:
                err_str = f"$error({full_messgae})"

            self._set_used(condition)
            if clk is None:
                self._assert(property_type == "assert", f"non clocked assertions only supports assert type while received {property_type}")
                self.line(f"""{name}_{property_type}: {property_type} property {misc._add_paren(condition)} else {err_str};
                          """)
            else:
                self._set_used(clk)
                disable_str = misc.cond(clk.rst_n is not None, f" disable iff (!{clk.rst_n})")
                self.line(f"""{name}_{property_type}: {property_type} property (@(posedge {clk}){disable_str} {condition})
                                         {misc.cond(property_type != "cover", "else")} {err_str};
                          """)

                if self._args.sim and self._args.sim_bin in ["vvp"] and property_type != "cover":
                    self.remark(f"CODE ADDED TO SUPPORT LEGACY SIMULATOR {self._args.sim_bin} THAT DOES NOT SUPPORT CONCURRENT ASSERTIONS")
                    assert_never = {}
                    assert_never[name] = self.logic(assign=misc._invert(condition), _allow_str=True)
                    self.allow_unused(assert_never[name])
                    self.line(f"""always @(posedge {clk})
                                      if ({misc.cond(clk.rst_n is not None, f'{clk.rst_n} & ')}{assert_never[name]})
                                          {err_str};
                                """)


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
        self._assert(self._modname is None, "set_modname() was previously called", fatal=True)

        # create a new dictionary and remove self since it is illegal to delete items from locals
        module_locals = {}
        frame = inspect.currentframe()
        for name, value in frame.f_back.f_locals.items():
            if name != "self":
                module_locals[name] = value

        if self._register and self._parent.__class__.__name__ != self.__class__.__name__: # ignore nested recursions
            self.tb.register_test(module_locals)

        suf = self._get_module_params(module_locals, suffix=modname is None and suffix)
        if modname == "": # just a wrapper - no Verilog module
            return False
        if self._modname is None:
            self._modname = self._args.prefix
            if modname:
                self._modname += modname
            else:
                self._modname += self._get_clsname()
                if suffix and len(suf) > 0:
                    self._modname += FIELD_SEP + "_".join(suf)
                    self._assert(len(self._modname) <= MAX_MODNAME, \
                    f"module name should be explicitly set generated name {self._modname} of {len(self._modname)} characters exceeds max od {MAX_MODNAME}", fatal=True)
        exists = self._exists()
        if exists:
            self._signals = self._cache["conn"][self._modname]._signals
            if module_locals != self._modules[self._modname]:
                for name, val in module_locals.items():
                    if not name.startswith("_"):
                        self._assert(val == self._modules[self._modname][name], \
                        f"module {self._modname} was recreated with different content (variable {name} does not affect module name)", fatal=True)
        else:
            clsname = self._get_clsname()
            if clsname != "_test":
                self._find_file(f"{clsname}.py")
            self._modules[self._modname] = module_locals
        if self._parent is not None:
            self._parent._sons.append(self._modname)
        return exists

    def set_param(self, var, kind, condition=None, suffix="", default=None, remark=None):
        """
        Declare module parameter and set assertions.

        Args:
            var: module parameter
            kind([type, list of type]): type of var
            condition([None, bool]): parameter constraints
            suffix([None, str]): explicitly define parameter suffix
            default: if value matches default the parameter will not affect module name
            remark: legacy parameter - use Python remarks instead

        Returns:
            None
        """
        self._assert_type(condition, [None, bool])
        self._assert_type(suffix, [None, str])

        self._assert(remark is None, "don't use legacy parameter remark, use Python remarks they will be transfered to Verilog", warning=True)

        auto_suffix = suffix == ""
        current_line = self._get_current_line()
        line = current_line.replace(" ", "").split("#")[0]
        self._check_line_balanced(line)
        name = line.split("set_param(")[1].split(",")[0]
        remark = self._get_remark(current_line)

        if default is not None and var == default:
            suffix = None
        elif kind is clock and auto_suffix:
            if var != default_clk:
                suffix = str(var)
            else:
                suffix = None
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

    def get_fields(self, strct, fields=None):
        """
        Get struct fields.

        Args:
            strct(dict): p2v struct
            fields(list): list of specific fields to extract

        Returns:
            list of field names (or other attribute)
        """
        if isinstance(strct, p2v_enum):
            strct = vars(strct)
        self._assert_type(strct, dict)
        return self._get_strct_signals(strct, fields=fields)

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
            comment([str, dict, list]): string comment or one comment like per dictionary pair

        Returns:
            None
        """
        self._assert_type(comment, [str, dict, list])
        if isinstance(comment, dict):
            for key in comment:
                self.remark(f"{key} = {comment[key]}")
            self.line()
        elif isinstance(comment, list):
            line = self._get_current_line().replace(" ", "").split("#")[0]
            self._check_line_balanced(line)
            remark_val = line.split("remark(")[1][:-1]
            if self._assert(len(remark_val) > 2 and remark_val[0] == "[" and remark_val[-1] == "]", f"unepxected reamrk {remark_val}"):
                for n, name in enumerate(remark_val[1:-1].split(",")):
                    self.remark(f"{name} = {comment[n]}")
            self.line()
        else:
            self.line("", remark=comment)

    def parameter(self, name, val="", local=False):
        """
        Declare a Verilog parameter.

        Args:
            name([str, clock]): parameter name
            val([int, str]): parameter value
            local(book): local parameter (localparam)

        Returns:
            None
        """
        if isinstance(val, str) and val == "":
            val = str(name)
            name = ""
        if isinstance(name, str) and name == "":
            name = self._get_receive_name("parameter")
        if isinstance(val, p2v_signal):
            val = str(val)

        self._assert_type(name, str)
        self._assert_type(val, [int, str])
        self._assert_type(local, bool)
        if self._exists():
            return None
        signal = self._add_signal(p2v_signal(misc.cond(local, p2v_kind.LOCALPARAM, p2v_kind.PARAMETER), name.upper(), val, driven=True))
        if local:
            self.line(signal.declare())
        return signal

    def enum(self, names):
        """
        Declare an enumerated type.

        Args:
            names([list, dict]): enum names

        Returns:
            The enum dictionary
        """
        self._assert_type(names, [list, dict])
        if self._exists():
            return None

        if isinstance(names, list):
            enum_names = {}
            for n, name in enumerate(names):
                enum_names[name] = n
        else:
            enum_names = names
        self._assert(len(enum_names) > 0, "enumerated type cannot be empty", fatal=True)
        max_val = 0
        for name, val in enum_names.items():
            self._assert(misc._is_legal_name(name), f"enumerated type {name} does not use a legal name", fatal=True)
            self._assert(name not in ["NAME", "BITS"], f"enum cannot use reserevd name {name}", fatal=True)
            self._assert(isinstance(val, int), f"enumerated type {name} is of type {type(val)} while expecting type int", fatal=True)
            max_val = max(max_val, val)
        max_val_bin = misc.bin(max_val, add_sep=0, prefix=None)
        enum_bits = len(str(max_val_bin))

        enum_vals = {}
        for name, val in enum_names.items():
            self.parameter(name, misc.dec(val, enum_bits), local=True)
            enum_vals[name] = p2v_signal(p2v_kind.ENUM, name, bits=enum_bits)
        self.line()
        enum_vals["NAME"] = p2v_signal(p2v_kind.ENUM, self._get_receive_name("enum"), bits=enum_bits)
        enum_vals["BITS"] = enum_bits
        return p2v_enum(**enum_vals)

    def input(self, name="", bits=1, _allow_str=False):
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
            p2v signal
        """
        if self._is_implicit_declare(name):
            bits = name
            name = ""
        elif isinstance(name, str):
            if not _allow_str:
                self._assert(name == "", "port name should not use string type")
        if isinstance(bits, p2v_signal):
            bits = str(bits)

        self._assert_type(name, [str, list ,clock])
        self._assert_type(bits, SIGNAL_TYPES)
        return self._port(p2v_kind.INPUT, name, bits, driven=True)

    def output(self, name="", bits=1, _allow_str=False):
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
            p2v signal
        """
        if self._is_implicit_declare(name):
            bits = name
            name = ""
        elif isinstance(name, str):
            if not _allow_str:
                self._assert(name == "", "port name should not use string type")
        if isinstance(bits, p2v_signal):
            bits = str(bits)

        self._assert_type(name, [str, list, clock])
        self._assert_type(bits, SIGNAL_TYPES)
        return self._port(p2v_kind.OUTPUT, name, bits, used=True)

    def inout(self, name="", _allow_str=False):
        """
        Create an inout port.

        Args:
            name(str): port name

        Returns:
            p2v signal
        """
        if isinstance(name, str):
            if not _allow_str:
                self._assert(name == "", "port name should not use string type")

        self._assert_type(name, [str])
        self._port(p2v_kind.INOUT, name, bits=1, used=True, driven=True)

    def logic(self, name="", bits=1, assign=None, initial=None, _allow_str=False):
        """
        Declare a Verilog signal.

        Args:
            name([clock, p2v_signal, list, str]): signal name
            bits([clock, int, float, dict, tuple]): clock is used for p2v clock.\n\
                                             int is used fot number of bits.\n\
                                             float is used to mark struct control signals. \n\
                                             list is used to prevent a scalar signal (input x[0:0]; instead of input x;). \n\
                                             tuple is used for multi-dimentional Verilog arrays. \n\
                                             dict is used as a struct.
            assign([int, str, dict, None]): assignment value to signal using an assign statement
            initial([int, str, dict, None]): assignment value to signal using an initial statement

        Returns:
            p2v signal
        """
        if self._is_implicit_declare(name):
            bits = name
            name = ""
        elif isinstance(name, str):
            if not _allow_str:
                self._assert(name == "", "logic name should not use string type")
        if isinstance(name, str) and name == "":
            name = self._get_receive_name("logic")
        if isinstance(bits, p2v_signal):
            bits = str(bits)

        self._assert_type(name, [clock, p2v_signal, str, list])
        self._assert_type(bits, SIGNAL_TYPES)
        self._assert_type(assign, [p2v_signal, int, str, dict, None])
        self._assert_type(initial, [p2v_signal, int, str, dict, None])

        if isinstance(name, p2v_signal):
            name = str(name)

        if isinstance(bits, p2v_enum):
            enum = vars(bits)
            bits = bits.BITS
        else:
            enum = None

        remark = self._get_remark(depth=2)

        rtrn = None
        if isinstance(name, clock):
            for net in name.get_nets():
                self.logic(net, _allow_str=True)
        elif isinstance(name, list):
            signals = []
            for n in name:
                signals.append(self.logic(n, bits=bits, assign=assign, initial=initial))
            rtrn = signals
        elif isinstance(bits, dict):
            if remark is not None:
                self.remark(remark)
            signal = self._add_signal(p2v_signal(p2v_kind.LOGIC, name, bits=0, strct=bits, used=True, driven=True))
            fields = signal._strct.fields
            for field_name in fields:
                self.logic(field_name, abs(fields[field_name]), _allow_str=True)
            rtrn = signal
        else:
            for bits_str in self._get_names(str(bits)):
                self._set_used(bits_str)
            signal = self._add_signal(p2v_signal(p2v_kind.LOGIC, name, bits, remark=remark))
            if enum is not None:
                for _name, _val in enum.items():
                    setattr(signal, _name, p2v_signal(None, f"({name} == {_val})", bits=bits))
            self.line(signal.declare())
            rtrn = signal
        if assign is not None:
            self.assign(signal, assign, keyword="assign", remark=remark, _allow_str=_allow_str)
            self.line()
        elif initial is not None:
            self.assign(signal, initial, keyword="initial", remark=remark, _allow_str=_allow_str)
            self.line()
        return rtrn

    def assign(self, tgt, src, keyword="assign", remark=None, _allow_str=False):
        """
        Signal assignment.

        Args:
            tgt([clock, p2v_signal]): target signal
            src([clock, p2v_signal, int]): source Verilog expression
            keyword(str): prefix to assignment

        Returns:
            None
        """
        self._assert_type(tgt, [clock, p2v_signal])
        self._assert_type(src, [clock, p2v_signal, int] + int(_allow_str) * [str])
        self._assert_type(keyword, str)
        if self._exists():
            return
        if isinstance(tgt, clock) or isinstance(src, clock):
            self._assign_clocks(tgt, src)
        else:
            tgt_is_strct = isinstance(tgt, p2v_signal) and tgt._strct is not None
            if tgt_is_strct:
                self._assign_structs(tgt, src, keyword=keyword)
            else:
                if keyword != "":
                    self._set_driven(tgt)
                if isinstance(src, int):
                    bits = self._get_signal_bits(tgt)
                    if isinstance(tgt._bits, str): # Verilog parameter width
                        src = f"'{src}"
                    else:
                        self._assert(bits > 0, f"illegal assignment to signal {tgt} of 0 bits")
                        src = misc.dec(src, bits)
                self._set_used(src, drive=False)
                if remark is None:
                    remark = self._get_remark(depth=2)
                self.line(f"{keyword} {tgt} = {src};", remark=remark)

    def sample(self, clk, tgt, src, valid=None, reset=None, reset_val=0, bits=None, bypass=False, _allow_str=False):
        """
        Sample signal using FFs.

        Args:
            clk(clock): p2v clock (including optional reset/s)
            tgt(str): target signal
            src(str): source signal
            valid([str, None]): qualifier signal
            reset([str, None]): sync reset
            reset_val([int, str]): reset values
            bits([int, None]): explicitly specify number of bits
            bypass(bool): replace ff with async assignment

        Returns:
            None
        """
        if self._exists():
            return
        if _allow_str:
            if isinstance(src, str):
                src = p2v_signal(None, src, bits=0)
            if isinstance(tgt, str):
                tgt = p2v_signal(None, tgt, bits=0)
            if isinstance(valid, str):
                valid = p2v_signal(None, valid, bits=1)
            if isinstance(reset, str):
                reset = p2v_signal(None, reset, bits=1)

        self._assert_type(clk, clock)
        self._assert_type(src, [p2v_signal])
        self._assert_type(tgt, [p2v_signal])
        self._assert_type(valid, [p2v_signal, None])
        self._assert_type(reset, [p2v_signal, None])
        self._assert_type(reset_val, [p2v_signal, int, str])
        self._assert_type(bits, [int, None])
        self._assert_type(bypass, bool)

        self._set_used(src, drive=False)
        if valid is not None:
            self.allow_unused(valid)
        if reset is not None:
            self.allow_unused(reset)

        if bypass:
            if str(clk.name) in self._signals:
                self.allow_unused(clk)
            self.assign(tgt, src)
            return

        if (tgt._name in self._signals and (self._signals[tgt._name]._strct is not None)) or (src._name in self._signals and (self._signals[src._name]._strct is not None)):
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

            self.line(f"always_ff @(posedge {clk.name}{misc.cond(clk.rst_n is not None, f' or negedge {clk.rst_n}')})", remark=self._get_remark(depth=2))
            conds = []
            if clk.rst_n is not None:
                conds.append(f"if (!{clk.rst_n}) {tgt} <= {reset_val};")
            sync_reset = []
            if clk.reset is not None:
                sync_reset.append(str(clk.reset))
            if reset is not None:
                sync_reset.append(str(reset))
            if len(sync_reset) > 0:
                conds.append(f"if {misc._add_paren(' | '.join(sync_reset))} {tgt} <= {reset_val};")
            if valid is not None:
                self._check_declared(valid)
                self._set_used(valid)
                conds.append(f"if {misc._add_paren(valid)} {tgt} <= {src};")
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
        self._assert_type(name, [clock, p2v_signal, list])
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
        self._assert_type(name, [clock, p2v_signal, list, str])
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
        ports = self._get_verilog_ports(modname)
        if self._args.lint is not None:
            self._write_empty_module(modname)
        return self._get_connects(parent=self, modname=modname, signals=ports, params=params, verilog=True)

    def assert_property(self, clk=None, condition=None, message=None, name=None, fatal=True):
        """
        Assertion on Verilog signals with clock.

        Args:
            clk(clock): triggering clock
            condition(p2v_signal): Error occurs when condition is False
            message(str): Error message
            name([None, str]): Explicit assertion name
            fatal(bool): stop on error

        Returns:
            NA
        """
        self._assert_property(clk, condition, message, name=name, fatal=fatal, property_type="assert")

    def assume_property(self, clk, condition, message, name=None, fatal=True):
        """
        Assumptions on Verilog signals (constrain design).

        Args:
            clk(clock): triggering clock
            condition(p2v_signal): Error occurs when condition is False
            message(str): Error message
            name([None, str]): Explicit assertion name
            fatal(bool): stop on error

        Returns:
            NA
        """
        self._assert_property(clk, condition, message, name=name, fatal=fatal, property_type="assume")

    def cover_property(self, clk, condition, message, name=None, fatal=True):
        """
        Assumptions on Verilog signals (constrain design).

        Args:
            clk(clock): triggering clock
            condition(p2v_signal): Error occurs when condition is False
            message(str): Error message
            name([None, str]): Explicit assertion name
            fatal(bool): stop on error

        Returns:
            NA
        """
        self._assert_property(clk, condition, message, name=name, fatal=fatal, property_type="cover")

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
        if lint:
            self._check_signals()
        self._check_mod_loop()
        lines = self._get_modlines(lint=lint)
        outfile = self._get_outfile()
        self._update_outhash(self._modname, outfile, lines)
        # write Verilog file
        self._write_lines(outfile, lines)
        self._logger.info("created: %s", os.path.basename(outfile))
        if self._parent is not None:
            self._parent._err_num += self._err_num
        return self._get_connects(parent=self._parent, modname=self._modname, signals=self._signals, params={})

    def fsm(self, clk, enum, reset_val=None):
        """
        Creates an FSM class.

        Args:
            clk(clock): state machine clock
            enum(p2v_enum): enumerated type for states
            reset_val([None, enum_state]): reset state

        Returns:
            state machine class
        """
        self._assert_type(clk, clock)
        self._assert_type(enum, p2v_enum)
        self._assert_type(reset_val, [None, p2v_signal])

        if reset_val is None:
            first_key = list(vars(enum).keys())[0]
            reset_val = getattr(enum, first_key)

        return p2v_fsm(self, clk, enum, reset_val=reset_val)

# top constructor
if __name__ != "__main__" and os.path.basename(sys.argv[0]) != "pydoc.py":
    p2v()
