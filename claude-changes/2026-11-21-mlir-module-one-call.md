# pille/mlir: a module is verified with one run of mlir-opt (2026-11-21)

Making a module ran `mlir-opt` to verify it and print it in the custom form, and the first SMT query over it ran
`mlir-opt` again to print the generic form the lowering reads: about 20 ms each. A module is now verified and kept
in the generic form, by one run (`private/mlir/tools.rkt`). Passes, translation to LLVM IR and SMT-LIB, and the
lowering are given that text; MLIR's tools read either form and print the same from each (checked: the generic
text made from a source and from its custom print are the same bytes, and so are the LLVM IR and the custom text
made from each).

- `Module.to_ir()` (`module_ir`) prints the custom form with `mlir-opt` when it is first asked for, and keeps it.
  It was a stored text before; its text is unchanged. This is the one behaviour a caller can see: the first
  `to_ir()` of a module starts a process (or reads the cache).
- `run_passes` gives a module kept the same way.
- No binding changed.

The first query over a new module of the 12-step fixture takes 10.7 ms where it took 28.5, cache off. With the
cache on, a module seen before costs no process either way.

The frozen lowering record (digests of each lowered module's custom text and SMT-LIB) passes unchanged, as do
`pille/pille/tests/mlir*.rhm`, which go through passes to LLVM.

Documentation: `pille-mlir-lib/README.md`, the API table's `to_ir()` row and the paragraph after it. The Scribble
manual has nothing on `pille/mlir`.
