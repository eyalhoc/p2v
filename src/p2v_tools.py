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
p2v_tools module. Responsible for external tools, checking if intalled and operating using system commands.
"""
import os
import subprocess

import p2v_misc as misc


def system(dirname, outdir, cmd, logfile, log_out=True, log_err=True):
    """
    Run system command while logging the command and output.

    Args:
        dirname(str): Directory to run command at
        outdir(str): Directory for output files
        cmd(str): Command to run
        logfile(str): name of log file
        log_out(bool): log output stream
        log_err(bool): log error stream

    Returns:
        full path to log file
    """
    assert os.path.isdir(dirname), f"{dirname} does not exist"
    outdir = os.path.abspath(outdir)
    logfile = os.path.join(outdir, logfile)
    bin_name = cmd.split()[0]
    if log_out and log_err:
        cmd += f" > {logfile}"
    elif log_err:
        cmd += f" > /dev/null 2> {logfile}"
    elif log_out:
        cmd += f" 2> {logfile}"
    pwd = os.getcwd()
    os.chdir(dirname)
    os.system(cmd)
    misc._write_file(os.path.join(outdir, f"{bin_name}.cmd"), cmd)
    os.chdir(pwd)
    return os.path.join(os.path.abspath(dirname), logfile)

def check(tool_bin):
    """
    Check if a binary file exists in path.

    Args:
        tool_bin(str): name of binary file

    Returns:
        True if binary of tool exists
    """
    for path in os.environ["PATH"].split(os.pathsep):
        if os.path.exists(os.path.join(path, tool_bin)):
            return True
    return False

def indent(filename):
    """
    Indent Verilog file in background.

    Args:
        filename(str): name of Verilog file to indent

    Returns:
        subprocess process for the parent process to poll on
    """
    assert os.path.isfile(filename), f"{filename} does not exist"
    cmd = f"{INDENT_BIN} --indentation_spaces=4 --inplace {filename}"
    with subprocess.Popen(cmd.split(), start_new_session=True) as process: # Runs in the background
        pass
    return process

def lint(dirname, outdir, filename):
    """
    Run lint on Verilog file.

    Args:
        dirname(str): directory of Verilog file
        outdir(str): directory for log file
        filename(str): name of Verilog file

    Returns:
        full path of logfile and a boolean if lint completed successfully
    """
    logfile = "p2v_lint.log"
    if filename is None:
        topmodule = "*.* -Wno-MULTITOP"
    else:
        topmodule = os.path.basename(filename)
        if filename == topmodule:
            filename = os.path.join(dirname, topmodule)
        assert os.path.isfile(filename), f"{filename} does not exist"
    cmd = f"{LINT_BIN} --lint-only {topmodule} -y {os.path.join(os.path.abspath(outdir), 'bbox')} --timing"
    full_logfile = system(dirname, outdir, cmd, logfile, log_out=False, log_err=True)
    success = misc._read_file(full_logfile) == ""
    return full_logfile, success

def comp(dirname, outdir, modname=None, search=None, libs=None):
    """
    Run compile on Verilog file.

    Args:
        dirname(str): directory of Verilog file
        outdir(str): directory for log file
        modname(str): name of top module
        search(list): list of directories to search Verilog files
        libs(list): explicit list of Verilog files to compile

    Returns:
        full path of logfile and a boolean if compile completed successfully
    """
    if search is None:
        search = []
    if libs is None:
        libs = []
    logfile = "p2v_comp.log"
    flags = "-g2005-sv -gsupported-assertions"
    if len(search) > 0:
        flags += " -Y .v -Y .sv"
        flags += " -y " + " -y ".join(search)
        flags += " -I " + " -I ".join(search)
    topmodule = misc.cond(modname is not None, f"-s {modname}")
    ofile = os.path.join(os.path.abspath(outdir), f'{COMP_BIN}.o')
    full_logfile = system(dirname, outdir, f"{COMP_BIN} {flags} {topmodule} {' '.join(libs)} *.* -o {ofile} {flags}", logfile, log_out=False, log_err=True)
    success = os.path.isfile(ofile)
    return full_logfile, success

def sim(dirname, outdir, pass_str, err_str=None):
    """
    Run simulation on Verilog file.

    Args:
        dirname(str): directory of Verilog file
        outdir(str): directory for log file
        pass_str(str): string that marks a successful simulation
        err_str(list): string that count as error if detected in log file

    Returns:
        full path of logfile and a boolean if simulation completed successfully
    """
    if err_str is None:
        err_str = ["error", "failed"]
    success = False
    logfile = "p2v_sim.log"
    full_logfile = system(dirname, outdir, f"{SIM_BIN} {COMP_BIN}.o -fst", logfile, log_out=True, log_err=True)
    for line in misc._read_file(full_logfile).split("\n"):
        if pass_str in line:
            success = True
        for err_s in err_str:
            if err_s in line.lower():
                success = False
    return full_logfile, success

def lint_off():
    """
    Marks the beginning of a code block not to run lint on.

    Args:
        NA

    Returns:
        Verilog ifdef statement
    """
    return f"`ifndef {LINT_BIN.upper()}"

def lint_on():
    """
    Marks the end of a code block not to run lint on.

    Args:
        NA

    Returns:
        Verilog endif statement
    """
    return f"`endif // {LINT_BIN.upper()}"


# External tools being used for each function
INDENT_BIN = "verible-verilog-format"
LINT_BIN = "verilator"
COMP_BIN = "iverilog"
SIM_BIN = "vvp"

tools = {}
tools[INDENT_BIN] = "indentation"
tools[LINT_BIN] = "lint"
tools[COMP_BIN] = "compilation"
tools[SIM_BIN] = "simulation"

en = {}
for tool_bin in tools:
    en[tool_bin] = check(tool_bin)
