# SPMD under the check policy: pointer arithmetic on varying values (2026-11-20)

Slice C of `CLOSER_TIMED_MACHINE_WORK_ORDER.md`. No binding was added or renamed.

## What was wrong

The order said an overflow check on varying integer arithmetic gave a vector of booleans where one was wanted. The
arithmetic was not at fault: `+`, `-`, `*`, `/` and `%` on `Varying(Int(N))` already check under `check`, counting
active lanes only (`pille/pille/tests/spmd/checked-integers.rhm`, which was there before this). The failure was in
indexing a pointer by a varying offset, `p[i]` with `i` varying, which is how a gang gathers and scatters. In
`pille-lib/pille/private/simd.rhm`, under `check`:

- `sparse_add` of a pointer and a signed offset joined its two lane-wise tests with `&&`, which wants one
  `Boolean`: "required type: Boolean, actual type: Simd(Boolean, n)". It now uses `∧`.
- The same method, and the unsigned one, compared `Simd(RawPtr, n)` values with `≤`, `≥` and `<`, which pointers
  in a `Simd` do not have. They now use the unsigned comparison primitives, as `sparse_lt` and its siblings do.

Two more faults on the same path, under every policy:

- `sparse_sub` of a pointer and a varying amount called `sparse_neg`, which did not exist. It does now: `0 - x`
  through `sparse_sub`, so negating the least integer is checked like any subtraction.
- `sparse_sub` of a typed pointer and a constant declared the result `SparseSimd(RawPtr, n)` while returning the
  typed pointer, so `varying_pointer - 1` did not concretize. It declares the pointer's own type.

Only active lanes count, as before: the overflow flags pass through `mask.select(flags, #false)` before `any()`.

## Test

`pille/pille/tests/spmd/checked-pointers.rhm`: a pointer read at signed and unsigned varying offsets, written at
signed ones, a varying amount and a constant subtracted from a pointer, under all three policies; under `check`, an
offset that carries the pointer past the address space panics in an active lane and does nothing (no read, no
write, no panic) in a masked-off one.

## For Closer

`closer_exports/pille_jit.rhm` configures the JIT with `suppress` because of this. With the policy changed to
`check` there, `closer_exports/frame/flat.rhm`'s tests (4) and the reader's checks that run the chart in Pille (62)
pass against this Pille. The change itself is Closer's to make and was not made.
