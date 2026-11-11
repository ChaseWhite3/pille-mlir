// A deliberately contradictory boolean query. Exporting it does not run a solver.
module {
  smt.solver () : () -> () {
    smt.set_logic "QF_UF"
    %condition = smt.declare_fun "condition" : !smt.bool
    %negated = smt.not %condition
    smt.assert %condition
    smt.assert %negated
    smt.check sat {} unknown {} unsat {}
  }
}
