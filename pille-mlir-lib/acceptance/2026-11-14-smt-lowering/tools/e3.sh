#!/bin/zsh
S=/private/tmp/claude-501/-Users-chasewhite-gitStuff-pille/2772c4d8-e90c-5125-8d07-a525e58d75dc/scratchpad
P=/Users/chasewhite/gitStuff/pille
C=/Users/chasewhite/Documents/gitStuff/anote-java-clojure
export PLTCOLLECTS="$C/closer-exports:$P/pille-llvm-lib:$P/pille-lib:$P/pille-spmd-lib:$P/pille:$P/pille-mlir-lib:" PILLE_LLVM_PREFIX=/opt/homebrew/opt/llvm PILLE_MLIR_PREFIX=/opt/homebrew/opt/llvm
export PILLE_MLIR_SMT_PLUGIN=$S/smt/plugin/PilleSmtQuery.so CLOSER_ORACLE=goldens
unset PILLE_MLIR_SMT_COMPARE
cd $P
raco make pille-mlir-lib/pille/mlir/examples/bench-batch.rhm $S/smt/tools/closer-e3.rhm
for round in 1 2 3; do
  for mode in plugin rhombus; do
    if [[ $mode == plugin ]]; then export PILLE_MLIR_SMT_LOWERING=plugin; else unset PILLE_MLIR_SMT_LOWERING; fi
    [[ $round == 1 ]] && unset PILLE_SMT_BENCH_SKIP_SINGLE || export PILLE_SMT_BENCH_SKIP_SINGLE=1
    echo "== bench-batch $mode round $round"
    racket pille-mlir-lib/pille/mlir/examples/bench-batch.rhm 2>&1
    echo "== closer safetynet $mode round $round"
    (cd $C && racket $S/smt/tools/closer-e3.rhm 2>&1 | tail -3)
  done
done
