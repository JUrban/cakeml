(*****************************************************************************
 * Three-payload fast-evaluator seam.
 *
 * The production historical nonlinear checker is called with the exact
 * source program, encoded jobs, and encoded root records as three arguments.
 * This extension of compute_payloadFast extracts only literal cv arguments,
 * authenticates the complete equation environment and entry point, and
 * delegates the one semantic obligation to compute_payload3_call_refines.
 *****************************************************************************)
Theory compute_payload3Fast
Ancestors
  compute_payloadFast
Libs
  bossLib preamble

Definition compute_literal_call_payload3_def:
  compute_literal_call_payload3 (entry:mlstring) (expression:compute_exp) =
    case expression of
    | App function_name expressions =>
        (if function_name <> entry \/ LENGTH expressions <> 3 then NONE
         else
           case compute_exp_to_cv (EL 0 expressions) of
           | NONE => NONE
           | SOME payload1 =>
               case compute_exp_to_cv (EL 1 expressions) of
               | NONE => NONE
               | SOME payload2 =>
                   case compute_exp_to_cv (EL 2 expressions) of
                   | NONE => NONE
                   | SOME payload3 => SOME (payload1,payload2,payload3))
    | _ => NONE
End

Definition compute_payload3_call_fast_eval_def:
  compute_payload3_call_fast_eval
      (approved_ceqs:(mlstring # (mlstring list # compute_exp)) list)
      (entry:mlstring) (checker:cv -> cv -> cv -> bool) ceqs expression =
    if ceqs <> approved_ceqs then NONE
    else
      case compute_literal_call_payload3 entry expression of
      | NONE => NONE
      | SOME (payload1,payload2,payload3) =>
          if checker payload1 payload2 payload3 then SOME (Num 1) else NONE
End

Definition compute_payload3_call_refines_def:
  compute_payload3_call_refines approved_ceqs entry checker <=>
    !first_expression second_expression third_expression payload1 payload2
     payload3
     state.
      compute_exp_to_cv first_expression = SOME payload1 /\
      compute_exp_to_cv second_expression = SOME payload2 /\
      compute_exp_to_cv third_expression = SOME payload3 /\
      checker payload1 payload2 payload3 ==>
      compute_eval compute_default_clock approved_ceqs
        (App entry
          [first_expression;second_expression;third_expression]) state =
        (M_success (from_cv (Num 1)),state)
End

Theorem compute_literal_call_payload3_sound:
  compute_literal_call_payload3 entry expression =
      SOME (payload1,payload2,payload3) ==>
  expression =
    App entry [from_cv payload1;from_cv payload2;from_cv payload3]
Proof
  Cases_on `expression`
  >> rw [compute_literal_call_payload3_def,
         listTheory.LENGTH_EQ_NUM_compute]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_pureFastTheory.compute_exp_to_cv_sound
  >> gvs []
QED

Theorem compute_payload3_call_fast_eval_ok:
  compute_payload3_call_refines approved_ceqs entry checker ==>
  compute_fast_eval_ok
    (compute_payload3_call_fast_eval approved_ceqs entry checker)
Proof
  rw [computeTheory.compute_fast_eval_ok_def,
      compute_payload3_call_fast_eval_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_literal_call_payload3_sound
  >> gvs [compute_payload3_call_refines_def]
QED

Definition compute_payload3_call_fast_def:
  compute_payload3_call_fast approved_ceqs entry checker (ths,ceqs) tm =
    compute_with
      (compute_payload3_call_fast_eval approved_ceqs entry checker)
      (ths,ceqs) tm
End

Theorem compute_payload3_call_fast_thm:
  compute_payload3_call_refines approved_ceqs entry checker /\
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_payload3_call_fast approved_ceqs entry checker (ths,ceqs) tm s =
    (res,s') ==>
  s' = s /\
  (!th. res = M_success th ==> THM ctxt th) /\
  (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_payload3_call_fast_def]
  >> strip_tac
  >> assume_tac compute_payload3_call_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac
       `compute_payload3_call_fast_eval approved_ceqs entry checker`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

Theorem compute_literal_call_payload3_from_cv[simp]:
  compute_literal_call_payload3 entry
    (App entry [from_cv payload1;from_cv payload2;from_cv payload3]) =
      SOME (payload1,payload2,payload3)
Proof
  simp [compute_literal_call_payload3_def]
QED

Theorem compute_payload3_call_fast_eval_hit[simp]:
  checker payload1 payload2 payload3 ==>
  compute_payload3_call_fast_eval approved_ceqs entry checker approved_ceqs
    (App entry [from_cv payload1;from_cv payload2;from_cv payload3]) =
      SOME (Num 1)
Proof
  simp [compute_payload3_call_fast_eval_def]
QED

Theorem compute_payload3_call_fast_eval_rejects_alternate_ceqs[simp]:
  ceqs <> approved_ceqs ==>
  compute_payload3_call_fast_eval approved_ceqs entry checker ceqs
    expression = NONE
Proof
  simp [compute_payload3_call_fast_eval_def]
QED

Theorem compute_payload3_call_fast_eval_rejects_checker_miss[simp]:
  ~checker payload1 payload2 payload3 ==>
  compute_payload3_call_fast_eval approved_ceqs entry checker approved_ceqs
    (App entry [from_cv payload1;from_cv payload2;from_cv payload3]) = NONE
Proof
  simp [compute_payload3_call_fast_eval_def]
QED

Theorem compute_literal_call_payload3_rejects_wrong_entry[simp]:
  wrong_entry <> entry ==>
  compute_literal_call_payload3 entry
    (App wrong_entry
      [first_expression;second_expression;third_expression]) = NONE
Proof
  simp [compute_literal_call_payload3_def]
QED

Theorem compute_literal_call_payload3_rejects_short_call[simp]:
  compute_literal_call_payload3 entry
    (App entry [first_expression;second_expression]) = NONE
Proof
  simp [compute_literal_call_payload3_def]
QED

Theorem compute_literal_call_payload3_rejects_extra_argument[simp]:
  compute_literal_call_payload3 entry
    (App entry
      [first_expression;second_expression;third_expression;extra]) = NONE
Proof
  simp [compute_literal_call_payload3_def]
QED

Theorem compute_literal_call_payload3_rejects_variable[simp]:
  compute_literal_call_payload3 entry
    (App entry [first_expression;Var variable;third_expression]) = NONE
Proof
  simp [compute_literal_call_payload3_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
  >> every_case_tac
  >> simp []
QED

val _ = export_theory ();
