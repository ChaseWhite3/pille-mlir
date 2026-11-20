# SMT queries: orderings, choices, several results, overflow guards, named preconditions, objectives (2026-11-20)

Slice A of `CLOSER_TIMED_MACHINE_WORK_ORDER.md`. Everything is in `pille/mlir/smt` and `pille/mlir/dialect`; nothing
knows of alarms or phases. A query that could be written before means what it meant, and its exported SMT-LIB is
the same text.

## New bindings in `pille/mlir/smt`

- `ult`, `ule`, `ugt`, `uge`, `slt`, `sle`, `sgt`, `sge` (`(lhs, rhs) :: Formula`): orderings of two terms of equal
  width. The predicate says the signedness; a term has none.
- `ite(test :: Formula, chosen, otherwise) :: Term`: a choice between two terms of equal width.
- `result(index, ~width: w)`: one of the values a function with several results returns, from 0.
  `result(~width: w)` is unchanged and still means the result of a one-result function.
- `no_overflow_add`, `no_overflow_sub`, `no_overflow_mul` (`(lhs, rhs, ~signed: #false) :: Formula`): that the
  operation, on the unsigned or two's complement numbers the terms stand for, does not wrap. `add`, `sub`, `mul`
  still wrap.
- `precondition(formula, ~named: name) :: Precondition`, accepted wherever a list of preconditions is. A name is a
  nonempty string without bars, backslashes or line breaks, distinct within a query.
- `Infeasible(core :: List.of(String))`, a new `Outcome`: the query's named preconditions cannot hold together.
  `Query.feasibility_smtlib()` is the question asked first (or `#false` where no precondition is named).
- `ObjectiveQuery` and the outcome `Optimum(value :: Int, values :: List.of(Assignment))`.

## New binding in `pille/mlir/dialect`

- `Dialect.smt_objective(module, ~function:, ~inputs:, ~minimize: term` or `~maximize: term, ~signed: #false,
  ~preconditions: [])`, returning an `ObjectiveQuery` whose `check(~solver:, ~timeout:, ~arguments:)` gives
  `Optimum`, `Infeasible`, `Unknown`, `Timeout` or `Failure`.

## What the lowering reads that it did not

`arith.cmpi` (every predicate), `arith.select`, and a `func.return` of several scalars. The refusal for any other
operation lists these. Manifest forms added: `["cmp", predicate, a, b]`, `["ite", f, a, b]`, `["result_at", i]`,
`["no_overflow", op, signed, a, b]`, `result_widths`, and the mode `"objective"`.

## Things worth knowing

- **Cores.** `produce-unsat-cores` and `smt.core.minimize` are set before the first assertion. A core has no name
  that could be left out, but is not necessarily the smallest. Unnamed preconditions are asserted and never named,
  so a core can be empty where they alone conflict. A session or batch resets its solver around the feasibility
  question and puts its own options back.
- **Unnamed queries are unchanged.** Inconsistent unnamed preconditions still give `Proved`, vacuously.
- **Objectives.** Z3 orders bitvectors as unsigned. A signed objective is bound with its sign bit flipped, and
  `Optimum.value` is flipped back and read as two's complement. The optimum is over inputs that keep every
  operation within its model's requirements. A bitvector objective always has a bound: there is no `Unbounded`.
  Objectives run a standalone solver; they are not yet a `Session` method.
- **Overflow guards.** The SMT dialect has no extend operation. A guard does the operation one bit wider (twice as
  wide for a product), built with concat, extract and repeat.
- **`Counterexample.values`** is still one assignment per function argument. Results are not reported in it; a
  property that names `result(index, …)` shows as `result[index]` in the outcome's text.

## The record of the removed plugin

`tests/fixtures/smt-lowering/plugin-recorded.json.gz` pins what the removed native plugin made of 774 requests.
Nine of its refusals are reworded: six list the supported operations (now more), and three said exactly one result
is supported. The same requests are refused. Each new wording is recorded beside the plugin's with a
`differs_because`, as the record's three earlier differences are; the plugin's answers are untouched, and
`smt-lowering.rkt` lists all twelve. Nothing the plugin lowered lowers differently (645 lowered, 129 refused, as
before). The indexed result has its own manifest tag so that `["result", x]` stays malformed, as the plugin had it.

## Tests

`tests/smt-synthesis.rkt` (15 cases, about 3 s): each `cmpi` predicate against an evaluator written apart from the
lowering; guards against exact arithmetic on 864 edge pairs; cores, with the feasibility script run through `z3` by
hand; signed and unsigned objectives; and the order's acceptance fixture, a small timed machine written in the test
and unrolled for six messages, first held to the same machine written on numbers over 60 random message sequences.
Its acceptance points pass: R is least 13 and greatest 25; the unguarded maximum is a wrapped value; two named
expectations that conflict are named. `tests/smt-api.rhm` covers the same through the public API.

## For the manual and README

`pille-mlir-lib/README.md`'s "Verifying properties" section and its API table do not mention any of the bindings
above, nor `Infeasible` and `Optimum` among the outcomes. Its statement that the lowering accepts only
`arith.constant`, `func.return` and declared operations is now short by `arith.cmpi`, `arith.select` and several
results.
