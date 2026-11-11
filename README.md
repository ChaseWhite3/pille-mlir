# Pille: Extensible Low-Level Programming
Pille is a project that seeks to extend the [Rhombus][1] language family with first-class support for low-level and high-performance programming, leveraging a systems-programming discipline and an [LLVM][2]-powered backend to generate competitive machine code.

## Status
Pille is a work-in-progress research prototype, with documentation that is very incomplete and sometimes outdated. Nonetheless, it is already a sizeable (by some definition) example of using Rhombus to build a new language.

In the future, we hope to provide a stable(ish) API surface along with some all-important "getting started" documentation.

## Installation
1. Install Racket from Git, or from a recent snapshot release. Development of Pille sometimes closely tracks changes to Racket and Rhombus, which means that the most recent releases aren't always recent enough. Consider [rackup][3] for managing simultaneous Racket installations.
2. Install the Racket packages in this repository (they are not yet on the package index):
   ```sh
   raco pkg install pille-llvm-lib/ pille-mlir-lib/ pille-lib/ pille-spmd-lib/ pille/
   ```
3. Set the `PILLE_LLVM_PREFIX` environment variable to the root of an LLVM 23.1 installation:
   - LLVM is _not_ currently provided by any of Pille's Racket packages.
   - On macOS with Homebrew, `brew install llvm@23`, then set `PILLE_LLVM_PREFIX=$(brew --prefix llvm@23)`.
   - On Linux, the official LLVM builds will not work (because they do not include the LLVM shared library). If your package manager does not supply a compatible version, you may need to build LLVM from source.

### Platform Support
Most development and testing of Pille occurs on aarch64 macOS and x86_64 Linux systems; your mileage may vary on other host platforms.

## MLIR and IRDL

The `pille/mlir` Rhombus library supports verified MLIR modules, runtime dialect
registration from IRDL, pass pipelines, LLVM IR/bitcode output, and SMT-LIB
export. It uses the MLIR tools from LLVM 23.1; set `PILLE_MLIR_PREFIX` to their
installation prefix, or reuse `PILLE_LLVM_PREFIX`.

`pille/mlir/dialect` adds Rhombus declaration and constraint spaces that generate
IRDL through macro expansion. Imported convenience macros can contribute to a
dialect using the same declarations. See the
[declaration guide](pille-mlir-lib/DECLARATIONS.md).

This is a separate entry point for Rhombus language implementations that generate
MLIR and IRDL. Pille's existing language frontend still emits LLVM directly.
IRDL specifies operation/type/attribute constraints; custom executable semantics
and lowering require passes. See the [MLIR guide](pille-mlir-lib/README.md) for
the API, examples, tool setup, and integration tests.

## Repository Structure
The code is organized into subdirectories that are each Racket packages:

- `pille`: Umbrella package with tests and Scribble documentation.

- `pille-lib`: The actual implementation of Pille.

- `pille-spmd-lib`: The (WIP) implementation of `#lang pille/spmd`.

- `pille-llvm-lib`: Bespoke Rhombus bindings to the LLVM C API, used by `pille-lib`.

- `pille-mlir-lib`: Rhombus interface to MLIR tools, including IRDL registration,
  passes, and LLVM/SMT-LIB export. Can be installed independently of Pille's LLVM
  bindings.

[1]: https://rhombus-lang.org
[2]: https://llvm.org
[3]: https://samth.github.io/rackup
