About
=====

Fold/unfold transformation tool for MuArith, a first-order fixpoint logic with integers.

Installation
============

Compiles with gcc-5 (on Linux) and clang-700 (on Mac). Assumes preinstalled Gmp and Boost (libboost-system1.55-dev) packages.

* `cd mufolder ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3 and LLVM)
* `make` to build mufolder

If the build of Z3 and LLVM fails in the second step, try using g++-5 as c++ compiler.
The binary of mufolder can be found in `build/tools/mu/`.

Benchmarks
==========

