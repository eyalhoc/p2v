# p2v
Python to Verilog compiler

# What is P2V?
P2V is a python library used to generate synthesizable RTL. The RTL modules written in Python are converted to Verilog.

# Who is P2V meant for?
P2V is meant for chip designers familiar with Verilog and Python.


# INSTALLATION
P2V is a native Python3 library, it needs no special installations for its basic function.
Pip install TBD
Beyond basic functionality P2V does take advantage of the following open-source tools, and their absence will shut off their corresponding features:
1.	Verible – used for Verilog indentation
https://github.com/chipsalliance/verible
2.	Slang – used for Verilog module instantiations
https://github.com/MikePopoloski/slang
3.	Verilator – Verilog linter
https://verilator.org/guide/latest/install.html
4.	Iverilog – Verilog simulator
https://steveicarus.github.io/iverilog/usage/installation.html

# Using partially installed P2V	
P2V can run without all its dependencies, but in order to do that the -allow_missing_tools should be added to the command line, that will allow, for example, running without indenting files if the indentation tool is not installed.


# HELLO WORLD
python3 p2v/tutorial/example0_hello_world/hello_world.py
p2v-INFO: starting with seed 1
p2v-DEBUG: created: hello_world.sv
p2v-INFO: verilog generation completed successfully (1 sec)
p2v-INFO: verilog lint completed successfully
p2v-INFO: completed successfully
