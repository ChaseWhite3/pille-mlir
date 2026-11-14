#!/bin/sh
set -eu
benchmark_base=/tmp/pille-perf-bw1z4aif
export PLTCOLLECTS="$benchmark_base/closer/closer-exports:$benchmark_base/pille/pille-lib:$benchmark_base/pille/pille-llvm-lib:$benchmark_base/pille/pille-spmd-lib:$benchmark_base/pille/pille-mlir-lib:$benchmark_base/pille/pille:"
export PILLE_LLVM_PREFIX=/opt/homebrew/opt/llvm
export CLOSER_PARSER_MODEL=/Users/chasewhite/.cache/closer/parser
exec /opt/homebrew/bin/racket -R "$benchmark_base/artifacts/parser-baseline/compiled:" -y "$benchmark_base/artifacts/parser-baseline/run.rkt"
