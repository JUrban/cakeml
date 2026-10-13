(*****************************************************************************
 * General fast evaluator based on the proved first-order compute evaluator.
 *
 * Unlike an exact-result registration, this executes the supplied equations
 * and expression.  A bounded fuel value makes failure explicit; compute_with
 * then falls back to the existing verified evaluator.  Every successful fast
 * result is related to compute_eval by compute_eval_pure_refines.
 *****************************************************************************)
Theory compute_pureFast
Ancestors
  computeProof compute_evalPure
Libs
  bossLib preamble

Definition compute_exp_to_cv_def:
  compute_exp_to_cv (Num n : compute_exp) = SOME (Num n : cv) /\
  compute_exp_to_cv (Pair p q : compute_exp) =
    (case compute_exp_to_cv p of
     | NONE => NONE
     | SOME x =>
       case compute_exp_to_cv q of
       | NONE => NONE
       | SOME y => SOME (Pair x y)) /\
  compute_exp_to_cv _ = NONE
Termination
  wf_rel_tac `measure compute_exp_size` >> rw []
End

Theorem compute_exp_to_cv_sound:
  !expression result.
    compute_exp_to_cv expression = SOME result ==>
    from_cv result = expression
Proof
  ho_match_mp_tac compute_exp_to_cv_ind
  >> rw [compute_exp_to_cv_def]
  >> every_case_tac
  >> gvs []
QED

Definition compute_pure_fast_fuel_def:
  compute_pure_fast_fuel = (100000:num)
End

Definition compute_pure_fast_eval_def:
  compute_pure_fast_eval ceqs cexp =
    case compute_eval_pure compute_pure_fast_fuel ceqs cexp of
    | NONE => NONE
    | SOME result => compute_exp_to_cv result
End

Theorem compute_pure_fast_eval_ok:
  compute_fast_eval_ok compute_pure_fast_eval
Proof
  rw [computeTheory.compute_fast_eval_ok_def,
      compute_pure_fast_eval_def]
  >> every_case_tac
  >> gvs []
  >> drule compute_exp_to_cv_sound
  >> strip_tac
  >> irule compute_eval_pure_refines
  >> qexists_tac `compute_pure_fast_fuel`
  >> simp [compute_pure_fast_fuel_def,
           computeTheory.compute_default_clock]
QED

Definition compute_pure_fast_def:
  compute_pure_fast (ths,ceqs) tm =
    compute_with compute_pure_fast_eval (ths,ceqs) tm
End

Theorem compute_pure_fast_thm:
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_pure_fast (ths,ceqs) tm s = (res,s') ==>
    s' = s /\
    (!th. res = M_success th ==> THM ctxt th) /\
    (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_pure_fast_def]
  >> strip_tac
  >> assume_tac compute_pure_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac `compute_pure_fast_eval`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

val _ = export_theory ();
