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

import os
import sys
import subprocess

import p2v_misc as misc
import p2v_tb as tb


def system(dirname, outdir, cmd, logfile, log_out=True, log_err=True):
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
    for path in os.environ["PATH"].split(os.pathsep):
        if os.path.exists(os.path.join(path, tool_bin)):
            return True
    return False
            
def indent(filename):
    assert os.path.isfile(filename), f"{filename} does not exist"
    cmd = f"{indent_bin} --indentation_spaces=4 --inplace {filename}"
    process = subprocess.Popen(cmd.split())  # Runs in the background
    return process

def lint(dirname, outdir, filename):
    logfile = "p2v_lint.log"
    if filename is None:
        topmodule = "*.* -Wno-MULTITOP"
    else:
        topmodule = os.path.basename(filename)
        if filename == topmodule:
            filename = os.path.join(dirname, topmodule)
        assert os.path.isfile(filename), f"{filename} does not exist"
    cmd = f"{lint_bin} --lint-only {topmodule} -y {os.path.join(os.path.abspath(outdir), 'bbox')} --timing"
    full_logfile = system(dirname, outdir, cmd, logfile, log_out=False, log_err=True)
    success = misc._read_file(full_logfile) == ""
    return full_logfile, success

def comp(dirname, outdir, modname=None, search=[], libs=[]):
    logfile = "p2v_comp.log"
    flags = ""
    if len(search) > 0:
        flags += " -Y .v -Y .sv"
        flags += " -y " + " -y ".join(search)
        flags += " -I " + " -I ".join(search)
    topmodule = misc.cond(modname is not None, f"-s {modname}")
    ofile = os.path.join(os.path.abspath(outdir), f'{comp_bin}.o')
    full_logfile = system(dirname, outdir, f"{comp_bin} -g2005-sv {topmodule} {' '.join(libs)} *.* -o {ofile} {flags}", logfile, log_out=False, log_err=True)
    success = os.path.isfile(ofile)
    return full_logfile, success
    
def sim(dirname, outdir, err_str=["error", "failed"], pass_str=tb.pass_status):
    success = False
    logfile = "p2v_sim.log"
    full_logfile = system(dirname, outdir, f"{sim_bin} {comp_bin}.o -fst", logfile, log_out=True, log_err=True)
    for line in misc._read_file(full_logfile).split("\n"):
        if pass_str in line:
            success = True
        for err_s in err_str:
            if err_s in line.lower():
                success = False
    return full_logfile, success


indent_bin = "verible-verilog-format"
lint_bin = "verilator"
comp_bin = "iverilog"
sim_bin = "vvp"

tools = {}
tools[indent_bin] = "indentation"
tools[lint_bin] = "lint"
tools[comp_bin] = "compilation"
tools[sim_bin] = "simulation"

en = {}
for tool_bin in tools:
    en[tool_bin] = check(tool_bin)
