# Pille finds LLVM itself, and says what is wrong (2026-11-20)

Using Pille needed PILLE_LLVM_PREFIX set by hand, and a missing or wrong piece showed as a bare or misleading error
("environment variable PILLE_LLVM_PREFIX is not set", "unsupported LLVM version", or, on a Racket too old for the
Git `ffi2` it is paired with, "function call: not a function, given: #false" on every callback into Rhombus). Now:

## LLVM is found

- `pille-llvm-lib/pille/private/llvm/paths.rhm`: `llvm_prefix()` is PILLE_LLVM_PREFIX where it is set, and otherwise
  the first usual place holding LLVM 23 with its shared library: on macOS `/opt/homebrew/opt/llvm@23`,
  `/opt/homebrew/opt/llvm`, `/usr/local/opt/llvm@23`, `/usr/local/opt/llvm`; on Linux `/usr/lib/llvm-23`,
  `/usr/lib64/llvm23`, `/usr/local/llvm-23`, `/opt/llvm-23`. A place is taken when its shared library exists and its
  `llvm-config.h`, where it has one, says major version 23. The list is the parameter `llvm_search_prefixes`.
- A PILLE_LLVM_PREFIX with no shared library under it, no LLVM found, and a wrong version each say what was looked
  for, what was found, what is needed and how to fix it.
- `pille/lowering`'s disassembly (`Compiler.format_obj`) uses the same installation for `llvm-objdump`.
- `pille/mlir` looks in the same places, after PILLE_MLIR_PREFIX and PILLE_LLVM_PREFIX and before PATH
  (`pille-mlir-lib/pille/private/mlir/tools.rkt`, parameter `llvm-search-prefixes`); its "cannot find" message lists
  them. Its tests that prove no tool is needed now also empty that list.

## A callback failure says why

`pille-lib/pille/private/runtime/rhombus_interop.rhm`: where a call into Pille fails with "not a function" and a
self-test (`callbacks_work`: make a callback, call it through a foreign call) fails too, Pille says that this
Racket's FFI cannot call back into Rhombus, with the Racket version and the fix. A body's own "not a function"
error, on a Racket where callbacks work, is passed on unchanged.

## `raco pille doctor`

`pille/pille/doctor.rhm`, registered as the raco command `pille` in `pille/pille/info.rkt`. It checks, in order: the
Racket version, LLVM (version, where, and whether found or set), a JIT compile and run, a callback into Rhombus, and,
as optional, the MLIR tools and Z3. Each line is ok, FAILED, missing or skipped, with a fix where one is needed.
It exits 1 when something Pille needs is not there. The JIT and callback checks are in
`pille/pille/private/doctor_jit.rhm`, loaded only when the doctor gets to them. CI runs it before the tests.

## For the manual and README

- PILLE_LLVM_PREFIX and PILLE_MLIR_PREFIX are no longer required where LLVM 23 is in one of the usual places; the
  README's installation step 3 says to set PILLE_LLVM_PREFIX, and `pille-mlir-lib/README.md` gives the tool
  selection order without the usual places (between PILLE_LLVM_PREFIX and PATH now).
- `raco pille doctor` is new: a first thing to run after installing, and when something does not work.
- `pille/mlir`'s internal `toolchain_bin` accessor is new (used by the doctor; not exported from `pille/mlir`).
