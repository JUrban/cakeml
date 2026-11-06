(******************************************************************************
 * Dependency-light composition of proved fast evaluators.                   *
 *                                                                            *
 * This generic theory deliberately depends only on the compute contract.     *
 * Concrete registered evaluators can therefore prepend a branch without     *
 * importing older case-specific callback theories into their edit loop.      *
 ******************************************************************************)
Theory compute_fastPrepend
Ancestors
  computeProof
Libs
  bossLib preamble

Definition compute_fast_eval_prepend_def:
  compute_fast_eval_prepend evaluator fallback ceqs cexp =
    case evaluator ceqs cexp of
    | SOME result => SOME result
    | NONE => fallback ceqs cexp
End

Theorem compute_fast_eval_prepend_ok:
  compute_fast_eval_ok evaluator /\
  compute_fast_eval_ok fallback ==>
  compute_fast_eval_ok (compute_fast_eval_prepend evaluator fallback)
Proof
  rw
    [computeTheory.compute_fast_eval_ok_def,
     compute_fast_eval_prepend_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

val _ = export_theory ();
