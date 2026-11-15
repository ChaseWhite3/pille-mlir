#!/bin/zsh
# E2: Closer's checks with each lowering in turn, then with both compared on every question.
S=/private/tmp/claude-501/-Users-chasewhite-gitStuff-pille/2772c4d8-e90c-5125-8d07-a525e58d75dc/scratchpad
cd /Users/chasewhite/Documents/gitStuff/anote-java-clojure
P=/Users/chasewhite/gitStuff/pille
export PLTCOLLECTS="$PWD/closer-exports:$P/pille-llvm-lib:$P/pille-lib:$P/pille-spmd-lib:$P/pille:$P/pille-mlir-lib:" PILLE_LLVM_PREFIX=/opt/homebrew/opt/llvm PILLE_MLIR_PREFIX=/opt/homebrew/opt/llvm
export PILLE_MLIR_SMT_PLUGIN=$S/smt/plugin/PilleSmtQuery.so CLOSER_ORACLE=goldens
C=closer-exports/closer_exports
CHECKS=($C/mlir/check.rhm $C/mlir/assumptions_check.rhm $C/checked_check.rhm $C/requirement_rules_check.rhm $C/semantics_check.rhm $C/run/try_check.rhm $C/refinement/check.rhm $C/role_identity_check.rhm $C/editor_check.rhm $C/neighborhood_check.rhm)
raco make $CHECKS < /dev/null > $S/smt/e2-make.txt 2>&1
for mode in plugin rhombus compare; do
  unset PILLE_MLIR_SMT_LOWERING PILLE_MLIR_SMT_COMPARE
  [[ $mode == plugin ]] && export PILLE_MLIR_SMT_LOWERING=plugin
  [[ $mode == compare ]] && rm -rf $S/smt/cmp-closer && export PILLE_MLIR_SMT_COMPARE=$S/smt/cmp-closer
  for check in $CHECKS; do
    start=$(python3 -c 'import time; print(time.time())')
    raco test $check < /dev/null > $S/smt/e2-$mode-${check:t:r}-${check:h:t}.txt 2>&1
    end=$(python3 -c 'import time; print(time.time())')
    echo "$mode\t$check\t$(tail -1 $S/smt/e2-$mode-${check:t:r}-${check:h:t}.txt)\t$(python3 -c "print(round($end-$start,1))")s"
  done
done
