# Public `log` and `tanh`, and `pille/buffer` (2026-11-14)

Notes on API added by Claude, kept apart from the human-written manual. The
Scribble docs and README do not cover any of this yet.

Source: the Closer performance investigation of 2026-11-14. Its patch, measurements and
reproduction script are under `performance/2026-11-14-closer/`.

## `log(x)` and `tanh(x)`

Natural logarithm and hyperbolic tangent, available wherever `sqrt` and `exp`
already are (`pille`, `pille/hosted`).

- Work on `Float`, `Double` and `Simd` of either; the result has the type of
  the argument.
- Overloadable through `$log` and `$tanh`, like the other unary math ops.
- IEEE behaviour: `log(0.0)` is `-inf`, `log` of a negative is NaN,
  `tanh(±inf)` is `±1.0`, NaN in gives NaN out.

```rhombus
pille.fun squash(x :: Float) :: Float:
  tanh(x * 0.5) * 0.5 + 0.5
```

Defined in `pille-lib/pille/private/float.rhm` and
`pille-lib/pille/private/generic_ops.rhm`. Tests: `pille/pille/tests/public_math.rhm`.

**Naming:** code that opens `pille` or `pille/hosted` and defines its own `log`
or `tanh` will now clash with these.

## `pille/buffer`: `transpose_copy`

```rhombus
import: pille/buffer open

transpose_copy(source :: SliceOf(α), target :: SliceMut(α), rows :: USize, cols :: USize)
```

Copies a row-major `rows × cols` matrix in `source` to its row-major
`cols × rows` transpose in `target`.

- The caller owns both buffers and their lifetimes.
- Both slices must hold exactly `rows * cols` elements, and their byte ranges
  must not overlap.
- Panics, under every UB policy, on a length mismatch, an overlap, or a shape
  or address range that overflows. Nothing is written before the checks pass.
- Zero-sized matrices are fine. The element type needs a positive byte stride.
- It copies values; it does not promise to preserve struct padding.

**Cost:** about 5× faster than an element-by-element Rhombus loop once
compiled, but the first call pays roughly 109 ms of JIT compilation. Worth it
for repeated use, not for a single transpose at start-up.

Defined in `pille-lib/pille/buffer.rhm`. Tests: `pille/pille/tests/buffer.rhm`.

## Also added

`pille/pille/tests/spmd/checked-integers.rhm`: regression tests for integer
arithmetic on varying values under the `check` UB policy. No implementation
changed; the reported overflow-check problem did not reproduce.
