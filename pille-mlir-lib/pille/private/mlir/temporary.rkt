#lang racket/base

(require racket/file)

(provide current-temporary-base
         make-work-directory)

;; Every subprocess works in its own private directory, removed afterwards.
;; The base directory defaults to the system's; it is a parameter so that
;; callers and tests can redirect it, for example to a path containing spaces.
(define current-temporary-base (make-parameter #f))

(define (make-work-directory template)
  (make-temporary-file template 'directory (current-temporary-base)))
