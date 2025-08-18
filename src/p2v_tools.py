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
import glob
import subprocess

import p2v_misc as misc


def system(dirname, outdir, cmd, logfile=None, log_out=True, log_err=True, bin_name=None):
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
    if bin_name is None:
        bin_name = cmd.split()[0]
    if logfile is not None:
        logfile = os.path.join(outdir, logfile)
        if log_out and log_err:
            cmd += f" > {logfile}"
        elif log_err:
            cmd += f" > /dev/null 2> {logfile}"
        elif log_out:
            cmd += f" 2> {logfile}"
    pwd = os.getcwd()
    os.chdir(dirname)
    os.system(cmd)
    if logfile is not None:
        misc._write_file(os.path.join(outdir, f"{bin_name}.cmd"), cmd)
    os.chdir(pwd)
    if logfile is not None:
        return os.path.join(os.path.abspath(dirname), logfile)
    return None

def check(tool_bin):
    """
    Check if a binary file exists in path.

    Args:
        tool_bin(str): name of binary file

    Returns:
        True if binary of tool exists
    """
    if tool_bin is not None:
        for path in os.environ["PATH"].split(os.pathsep):
            if os.path.exists(os.path.join(path, tool_bin)):
                return True
    return False

def indent(tool_bin, filename):
    """
    Indent Verilog file in background.

    Args:
        tool_bin(str): name of binary file
        filename(str): name of Verilog file to indent

    Returns:
        subprocess process for the parent process to poll on
    """
    assert os.path.isfile(filename), f"{filename} does not exist"

    if tool_bin.startswith("verible"):
        cmd = f"{tool_bin} --indentation_spaces=4 --inplace {filename}"
    else:
        raise RuntimeError(f"unknown Verilog indentation {tool_bin}")

    with subprocess.Popen(cmd.split(), start_new_session=True) as process: # Runs in the background
        pass
    return process

def lint(tool_bin, dirname, outdir, filename):
    """
    Run lint on Verilog file.

    Args:
        tool_bin(str): name of binary file
        dirname(str): directory of Verilog file
        outdir(str): directory for log file
        filename(str): name of Verilog file

    Returns:
        full path of logfile and a boolean if lint completed successfully
    """
    logfile = "p2v_lint.log"

    if tool_bin.startswith("verilator"):
        if filename is None:
            topmodule = "*.* -Wno-MULTITOP"
        else:
            topmodule = os.path.basename(filename)
            if filename == topmodule:
                filename = os.path.join(dirname, topmodule)
            assert os.path.isfile(filename), f"{filename} does not exist"
        cmd = f"{tool_bin} --lint-only {topmodule} -y {os.path.join(os.path.abspath(outdir), 'bbox')} --timing"
    elif tool_bin.startswith("verible"):
        if filename is None or os.path.dirname(filename) == "":
            cmd = f"{tool_bin} *.*"
        else:
            cmd = f"{tool_bin} {filename}"
        cmd += " --rules -line-length" # ignore long lines
    else:
        raise RuntimeError(f"unknown Verilog lint tool {tool_bin}")

    full_logfile = system(dirname, outdir, cmd, logfile, log_out=False, log_err=True)
    success = misc._read_file(full_logfile) == ""
    return full_logfile, success

def _get_iverilog_flags(search=None):
    if search is None:
        search = []
    flags = "-g2005-sv -gsupported-assertions"
    if len(search) > 0:
        flags += " -Y .v -Y .sv"
        flags += " -y " + " -y ".join(search)
        flags += " -I " + " -I ".join(search)
    return flags


def comp(tool_bin, dirname, outdir, modname=None, search=None, libs=None):
    """
    Run compile on Verilog file.

    Args:
        tool_bin(str): name of binary file
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

    if tool_bin.startswith("iverilog"):
        flags = _get_iverilog_flags(search)
        topmodule = misc.cond(modname is not None, f"-s {modname}")
        ofile = os.path.join(os.path.abspath(outdir), "iverilog.o")
        cmd = f"{tool_bin} {flags} {topmodule} {' '.join(libs)} *.* -o {ofile} {flags}"
    else:
        raise RuntimeError(f"unknown Verilog compilation tool {tool_bin}")

    full_logfile = system(dirname, outdir, cmd, logfile, log_out=False, log_err=True)
    success = os.path.isfile(ofile)
    return full_logfile, success

def sim(tool_bin, dirname, outdir, pass_str, err_str=None):
    """
    Run simulation on Verilog file.

    Args:
        tool_bin(str): name of binary file
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

    if tool_bin.startswith("vvp"):
        cmd = f"{tool_bin} iverilog.o -fst"
    else:
        raise RuntimeError(f"unknown Verilog simulation tool {tool_bin}")

    full_logfile = system(dirname, outdir, cmd, logfile, log_out=True, log_err=True)
    for line in misc._read_file(full_logfile).split("\n"):
        if pass_str in line:
            success = True
        for err_s in err_str:
            if err_s in line.lower():
                success = False
    return full_logfile, success

def cocotb_sim(rtldir, outdir, cocotb_filename, modname, search=None, libs=None, exports=None):
    """
    Run cocotb simulation.

    Args:
        rtldir(str): directory of Verilog file
        outdir(str): directory for log file
        cocotb_filename(str): cocotb testbench file name
        modname(str): top verilog module name
        search(list): list of search paths
        libs(list): list of verilog library files
        exports(dict): environment variables for test

    Returns:
        full path of logfile and a boolean if simulation completed successfully
    """

    pass_str="PASS "
    err_str="FAIL "

    rtldir = os.path.abspath(rtldir)
    outdir = os.path.abspath(outdir)

    # create makefile
    build_dir = "sim_build2"
    makefile = os.path.join(outdir, "cocotb.makefile")
    tb_modname = os.path.basename(cocotb_filename).split(".")[0]
    makefile_lines = cocotb_makefile(tb_modname=tb_modname, top_modname=modname, rtldir=rtldir, search=search, libs=libs, exports=exports, build_dir=build_dir)
    misc._write_file(makefile, makefile_lines)

    success = False
    logfile = "p2v_sim.log"

    cmd = f"make -f {makefile}"
    system(outdir, outdir, f"rm -rf {build_dir}")
    full_logfile = system(outdir, outdir, cmd, logfile, log_out=True, log_err=True, bin_name="cocotb")
    misc._unlink(os.path.join(outdir, "dump.fst"))
    for src_path in glob.glob(f"{outdir}/{build_dir}/*.fst"):
        system(outdir, outdir, f"ln -s {src_path} dump.fst")
        break
    for line in misc._read_file(full_logfile).split("\n"):
        if pass_str in line:
            success = True
        if err_str in line.lower():
            success = False
    return full_logfile, success

def lint_off(tool_bin):
    """
    Marks the beginning of a code block not to run lint on.

    Args:
        tool_bin(str): name of binary file

    Returns:
        Verilog ifdef statement
    """
    if tool_bin.startswith("verilator"):
        return "`ifndef VERILATOR"
    return ""

def lint_on(tool_bin):
    """
    Marks the end of a code block not to run lint on.

    Args:
        tool_bin(str): name of binary file

    Returns:
        Verilog endif statement
    """
    if tool_bin.startswith("verilator"):
        return "`endif // VERILATOR"
    return ""

def cocotb_makefile(tb_modname, top_modname, rtldir, search=None, libs=None, exports=None, sim_name="icarus", build_dir="sim_build"):
    """
    Builds a cocotb make file.

    Args:
        tb_modname(str): name of cocotb testbench file
        top_modname(str): verilog wrapper module
        rtldir(str): verilog files directory
        search(list): list of search paths
        libs(list): list of library files
        exports(dict): environment variables for test
        sim_name(str): simulator name
        build_dir(str): directory for coctb simulation files

    Returns:
        coco tb make file as string
    """
    if search is None:
        search = []
    if libs is None:
        libs = []
    if exports is None:
        exports = []

    line = ""
    for name, val in exports.items():
        line += f"export {name}={val}\n"

    search_full = []
    for path in search:
        search_full.append(os.path.abspath(path))

    libs_full = []
    for path in libs:
        libs_full.append(os.path.abspath(path))

    line += f"""
            # Makefile

            # defaults
            SIM ?= {sim_name}
            WAVES=1
            TOPLEVEL_LANG ?= verilog
            PLUSARGS += -fst
            COMPILE_ARGS += {_get_iverilog_flags()}

            SIM_BUILD = {build_dir}
            VERILOG_SOURCES += {rtldir}/*.*v {" ".join(libs_full)}

            TOPLEVEL = {top_modname}

            export PYTHONPATH := $(PYTHONPATH):{":".join(search_full)}
            MODULE = {tb_modname}

            # include cocotb's make rules to take care of the simulator setup
            include $(shell cocotb-config --makefiles)/Makefile.sim

    """
    return line
