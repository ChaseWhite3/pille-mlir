#lang info

(define raco-commands
  '(("pille" (submod (lib "pille/doctor.rhm") main) "check that Pille can run here: `raco pille doctor`" #f)))
