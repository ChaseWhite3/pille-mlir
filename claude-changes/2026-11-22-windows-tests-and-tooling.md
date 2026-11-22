# Tests and tooling that work on Windows (2026-11-22)

From a Windows run at 8d6ddfc: 18 tests failed because they wrote a stand-in solver as a script and marked it
executable (`#o755`), which Windows refuses; `raco make` given a folder's files by name passed the command-line
limit and built nothing; `raco pille doctor` is not a raco command where Pille is used through `PLTCOLLECTS`; and
the doctor's "Callbacks" line read as a failure of Pille.

None of this was run on Windows from here. The Mac runs the same code paths, and what is Windows' own is said
below.

## Stand-in solvers are run as `python SCRIPT`

`pille-mlir-lib/pille/mlir/tests/fakes.rkt` (new): the Python interpreter, a script writer, and whether a process
is alive (`kill -0`, or on Windows `tasklist`). A stand-in is a Python script, and the tests give the solver API
the interpreter as its executable and the script as the first of its arguments. Nothing is marked executable.

- `solver.rkt`: its stand-ins were `/bin/sh` scripts; they are Python now, the same behaviour line for line.
- `sessions.rkt`, `smt-synthesis.rkt` (the solver that pads every core, for the core-shrinking test),
  `smt-integration.rkt` (a solver reached through a path with spaces): launched this way.
- Where a test is about which executable is chosen (`PILLE_Z3`), the interpreter is what is chosen and the script
  follows as an argument.
- One check is not made on Windows, and says so where it stands: that a program named `z3` on `PATH` is the
  last resort. It needs a program of that name, made on other systems by a link to the interpreter.
- Windows' own, untested here: `tasklist.exe` for liveness; `python3` or `python` on `PATH`; a stand-in's lines
  ending in a carriage return (the readers already take z3.exe's).

These tests now need Python 3 on every platform (`sessions.rkt` already did).

## `pille/pille/make.rkt`

`racket pille/pille/make.rkt [-j N] PATH ...` (or `racket -l- pille/make ...`): compiles every `.rhm` and `.rkt`
file under the folders and files given, as `raco make` does for files named one by one, and exits 1 where one
fails. A few folder names stay within a command line's length.

## The doctor

- From a checkout: `racket -l pille/doctor.rhm` (with every package's folder in `PLTCOLLECTS`); its usage line
  and the README say so.
- "Callbacks" is no longer a failure of Pille. It reports `missing`, says that only Pille code that calls a Rhombus
  function needs it and that `pille/mlir` does not, and the doctor ends "Pille can run here." The Racket 9.3
  release cannot make such calls on the Mac either; a snapshot can.

## Documentation

`pille-mlir-lib/README.md`, "Checks and examples". The repository's root `README.md` (human-written, not edited)
would be the place to say `racket -l pille/doctor.rhm` and `racket pille/pille/make.rkt` for a checkout.

## Addendum: the Windows run at 57f45b0, and a file that is no program

Reported from Windows: the build script, the doctor and the stand-in solvers work (no `chmod` and no
`sessions.rkt` failures; 3 of 3,571 fail, two of them that machine's missing `llvm-as.exe`). Objectives in a scope
on the 98-step page, least and greatest of each duration: 1.8 to 3.4 s a duration, where it was about 20 s.

The third failure was Pille's: a solver path naming a file that is not a program was reported `nonzero_exit` on
Windows, not `missing_executable`. Windows gives every file the execute permission, which was the whole check.
There, a file is now a solver if it is a program or a command script by its extension (`.exe`, `.com`, `.bat`,
`.cmd`), or a program by its first two bytes (`private/mlir/solver.rkt` `windows-program?`). The rule is tested on
every system; that it gives `missing_executable` on Windows is for the Windows run to confirm.
