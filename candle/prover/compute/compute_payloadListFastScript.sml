(*****************************************************************************
 * Arity-generic literal-payload fast-evaluator seam.
 *
 * The existing three-payload seam is intentionally not copied for the
 * five-argument packed-object entry.  Literal extraction is defined once for
 * an arbitrary argument list; exact arity remains a fail-closed property of
 * the checker adapter.
 *****************************************************************************)
Theory compute_payloadListFast
Ancestors
  compute_payloadFast
Libs
  bossLib preamble

Definition compute_literal_payloads_def:
  compute_literal_payloads [] = SOME [] /\
  compute_literal_payloads (expression::expressions) =
    case compute_exp_to_cv expression of
    | NONE => NONE
    | SOME payload =>
        case compute_literal_payloads expressions of
        | NONE => NONE
        | SOME payloads => SOME (payload::payloads)
End

Definition compute_literal_call_payloads_def:
  compute_literal_call_payloads (entry:mlstring) (expression:compute_exp) =
    case expression of
    | App function_name expressions =>
        if function_name <> entry then NONE
        else compute_literal_payloads expressions
    | _ => NONE
End

Definition compute_payloads_call_fast_eval_def:
  compute_payloads_call_fast_eval
      (approved_ceqs:(mlstring # (mlstring list # compute_exp)) list)
      (entry:mlstring) (checker:cv list -> bool) ceqs expression =
    if ceqs <> approved_ceqs then NONE
    else
      case compute_literal_call_payloads entry expression of
      | NONE => NONE
      | SOME payloads =>
          if checker payloads then SOME (Num 1) else NONE
End

Definition compute_payloads_call_refines_def:
  compute_payloads_call_refines approved_ceqs entry checker <=>
    !expression payloads state.
      compute_literal_call_payloads entry expression = SOME payloads /\
      checker payloads ==>
      compute_eval compute_default_clock approved_ceqs
        expression state =
        (M_success (from_cv (Num 1)),state)
End

Definition compute_payload5_list_checker_def:
  compute_payload5_list_checker checker payloads =
    case payloads of
    | [payload1;payload2;payload3;payload4;payload5] =>
        checker payload1 payload2 payload3 payload4 payload5
    | _ => F
End

Theorem compute_literal_payloads_sound:
  compute_literal_payloads expressions = SOME payloads ==>
  expressions = MAP from_cv payloads
Proof
  qspec_tac (`payloads`,`payloads`)
  >>
  Induct_on `expressions`
  >> rpt gen_tac
  >> rw [compute_literal_payloads_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [compute_pureFastTheory.compute_exp_to_cv_sound]
QED

Theorem compute_literal_call_payloads_sound:
  compute_literal_call_payloads entry expression = SOME payloads ==>
  expression = App entry (MAP from_cv payloads)
Proof
  Cases_on `expression`
  >> rw [compute_literal_call_payloads_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_literal_payloads_sound
  >> gvs []
QED

Theorem compute_payloads_call_fast_eval_ok:
  compute_payloads_call_refines approved_ceqs entry checker ==>
  compute_fast_eval_ok
    (compute_payloads_call_fast_eval approved_ceqs entry checker)
Proof
  rw [computeTheory.compute_fast_eval_ok_def,
      compute_payloads_call_fast_eval_def]
  >> every_case_tac
  >> gvs []
  >> gvs [compute_payloads_call_refines_def]
QED

Definition compute_payloads_call_fast_def:
  compute_payloads_call_fast approved_ceqs entry checker (ths,ceqs) tm =
    compute_with
      (compute_payloads_call_fast_eval approved_ceqs entry checker)
      (ths,ceqs) tm
End

Theorem compute_payloads_call_fast_thm:
  compute_payloads_call_refines approved_ceqs entry checker /\
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_payloads_call_fast approved_ceqs entry checker (ths,ceqs) tm s =
    (res,s') ==>
  s' = s /\
  (!th. res = M_success th ==> THM ctxt th) /\
  (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_payloads_call_fast_def]
  >> strip_tac
  >> assume_tac compute_payloads_call_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac
       `compute_payloads_call_fast_eval approved_ceqs entry checker`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

Theorem compute_literal_payloads_from_cv[simp]:
  compute_literal_payloads (MAP from_cv payloads) = SOME payloads
Proof
  Induct_on `payloads`
  >> simp [compute_literal_payloads_def]
QED

Theorem compute_literal_call_payloads_from_cv[simp]:
  compute_literal_call_payloads entry
    (App entry (MAP from_cv payloads)) = SOME payloads
Proof
  simp [compute_literal_call_payloads_def]
QED

Theorem compute_payloads_call_fast_eval_hit[simp]:
  checker payloads ==>
  compute_payloads_call_fast_eval approved_ceqs entry checker approved_ceqs
    (App entry (MAP from_cv payloads)) = SOME (Num 1)
Proof
  simp [compute_payloads_call_fast_eval_def]
QED

Theorem compute_payloads_call_fast_eval_rejects_alternate_ceqs[simp]:
  ceqs <> approved_ceqs ==>
  compute_payloads_call_fast_eval approved_ceqs entry checker ceqs
    expression = NONE
Proof
  simp [compute_payloads_call_fast_eval_def]
QED

Theorem compute_payloads_call_fast_eval_rejects_checker_miss[simp]:
  ~checker payloads ==>
  compute_payloads_call_fast_eval approved_ceqs entry checker approved_ceqs
    (App entry (MAP from_cv payloads)) = NONE
Proof
  simp [compute_payloads_call_fast_eval_def]
QED

Theorem compute_literal_call_payloads_rejects_wrong_entry[simp]:
  wrong_entry <> entry ==>
  compute_literal_call_payloads entry
    (App wrong_entry expressions) = NONE
Proof
  simp [compute_literal_call_payloads_def]
QED

Theorem compute_literal_payloads_rejects_nonliteral[simp]:
  compute_literal_payloads (Var variable::expressions) = NONE
Proof
  simp [compute_literal_payloads_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
QED

Theorem compute_payload5_list_checker_exact[simp]:
  compute_payload5_list_checker checker
    [payload1;payload2;payload3;payload4;payload5] =
  checker payload1 payload2 payload3 payload4 payload5
Proof
  simp [compute_payload5_list_checker_def]
QED

Theorem compute_payload5_list_checker_rejects_short[simp]:
  ~compute_payload5_list_checker checker
    [payload1;payload2;payload3;payload4]
Proof
  simp [compute_payload5_list_checker_def]
QED

Theorem compute_payload5_list_checker_rejects_extra[simp]:
  ~compute_payload5_list_checker checker
    [payload1;payload2;payload3;payload4;payload5;payload6]
Proof
  simp [compute_payload5_list_checker_def]
QED

val _ = export_theory ();
