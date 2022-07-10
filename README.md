TG-nonlin
========

Maximizing Branch Coverage with Constrained Horn Clauses
for Solidity Language 

Installation
============

Assumes preinstalled Boost (e.g., 1.75.0) and Gmp (e.g. 10.4.0) packages. 

* `git clone https://github.com/izlatkin/aeval`
* `cd aeval`
* `git checkout tg-nonlin`
* `mkdir build ; cd build`
* `cmake ../`
* `cmake --build .  && cmake {PATH_TO_REPO}/aeval`
* `make` (again) to build TG

The binary of TG-nonlin can be found at `build/tools/nonlin/tgnonlin`.
Note that TG-nonlin comes with its own version of Z3

HowTo
==========
`./tools/nonlin/tgnonlin <options> file.smt2`
generated raw tests dumped to `testgen.txt` file 

Benchmarks
==========

Collection of the Solidity files
https://github.com/leonardoalt/cav_2022_artifact/tree/main/regression
sol files should be encoded to smt2 format (see: https://github.com/izlatkin/solidity_testgen)

