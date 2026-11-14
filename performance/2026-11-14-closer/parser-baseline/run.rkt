#lang racket/base
(require json)
(write-json (hash 'stage "process_started" 'monotonic_ms (current-inexact-monotonic-milliseconds)))
(newline)
(flush-output)
(dynamic-require (string->path "/tmp/pille-perf-bw1z4aif/artifacts/parser-baseline/bench.rhm") #f)
