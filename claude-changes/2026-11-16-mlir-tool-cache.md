# The MLIR tools' answers are kept (2026-11-16)

`pille/mlir` runs `mlir-opt`, `mlir-translate` and `llvm-as` as processes. It now keeps each answer by what was
asked, and answers the same request again without starting the tool.

## What changed

- `pille-mlir-lib/pille/private/mlir/tools.rkt`: `run-tool` looks in a cache before it starts a process. The key is
  a digest of the executable (path, size, modification time), each dialect and pass plugin the same way, the
  arguments, the working directory, the IRDL definitions and the input. Only a successful answer is kept; a
  failure runs the tool and reports its diagnostics as before.
- No function of `pille/mlir` changed its arguments or its result.

## What a user can set

- `PILLE_MLIR_CACHE`: the folder the answers are kept in. Unset, it is `pille-mlir` in the system's cache folder
  (`(find-system-path 'cache-dir)`). `off` keeps nothing on disk and starts the tool every time a process has not
  asked the same thing before.
- An entry not asked for in 30 days is removed, once per process, when the cache is first used. Within a process
  the last 4096 answers are also held in memory.

## Why

One strength question starts the tools about three times (parse and verify, print in generic form, export to
SMT-LIB), and a lowering asks the same things of the same module many times. Measured on Closer's
`closer_exports/mlir/check.rhm`: 4,524 tool starts in one run, about 124 s of its 185 s. With the answers kept, a
second run takes 113 s where the first takes 199 s. Pille's own `pille/mlir/tests` take 31 s where they took 72 s.

## For the manual

`pille/pille/scribblings/` does not mention `PILLE_MLIR_CACHE`. It belongs beside `PILLE_MLIR_PREFIX`, wherever the
MLIR tools are described.
