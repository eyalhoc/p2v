
from setuptools import setup, find_packages

setup(
    name='p2v-compiler',
    version='0.1.0',
    packages=find_packages(where="src"),
    package_dir={"": "src"},

    install_requires=[
        # List your dependencies here
    ],
    
    py_modules=["p2v", "p2v_connect", "p2v_signal", "p2v_struct", "p2v_tools", "p2v_clock", "p2v_misc", "p2v_slang", "p2v_tb"],
    
    author='Eyal Hochberg',  
    author_email='eyalhoc@gmail.com',
    description="A Python library for converting Python to synthesizable Verilog code",
    long_description=open("README.md").read(),
    long_description_content_type="text/markdown",
    license="GPL-3.0-or-later",
    url="https://github.com/eyalhoc/p2v",
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: GNU General Public License v3 (GPLv3)",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.6',

)
