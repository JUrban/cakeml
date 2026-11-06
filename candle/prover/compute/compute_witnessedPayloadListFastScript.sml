(*****************************************************************************
 * Arity-generic witnessed literal-payload fast-evaluator seam.
 *
 * The witness is bound by an otherwise unused Let, so ordinary compute
 * semantics remains the unchanged literal call.  A fast evaluator may inspect
 * the witness and every literal call argument, but it can return success only
 * through a proved refinement to that ordinary call.
 *****************************************************************************)
Theory compute_witnessedPayloadListFast
Ancestors
  compute_payloadListFast
Libs
  bossLib preamble

Definition compute_literal_witnessed_payloads_def:
  compute_literal_witnessed_payloads
      (witness_name:mlstring) (entry:mlstring) (expression:compute_exp) =
    case expression of
    | Let bound_name witness_expression body =>
        (if bound_name <> witness_name then NONE
         else
           case compute_exp_to_cv witness_expression of
           | NONE => NONE
           | SOME witness =>
               case compute_literal_call_payloads entry body of
               | NONE => NONE
               | SOME payloads => SOME (witness,payloads))
    | _ => NONE
End

Definition compute_witnessed_payloads_fast_eval_def:
  compute_witnessed_payloads_fast_eval
      (approved_ceqs:(mlstring # (mlstring list # compute_exp)) list)
      (witness_name:mlstring) (entry:mlstring)
      (checker:cv -> cv list -> bool) ceqs expression =
    if ceqs <> approved_ceqs then NONE
    else
      case compute_literal_witnessed_payloads witness_name entry expression of
      | NONE => NONE
      | SOME (witness,payloads) =>
          if checker witness payloads then SOME (Num 1) else NONE
End

Definition compute_witnessed_payloads_refines_def:
  compute_witnessed_payloads_refines approved_ceqs entry checker <=>
    !expression witness payloads state.
      compute_literal_call_payloads entry expression = SOME payloads /\
      checker witness payloads ==>
      compute_eval (compute_default_clock - 1) approved_ceqs expression state =
        (M_success (from_cv (Num 1)),state)
End

Definition compute_witnessed_payload4_list_checker_def:
  compute_witnessed_payload4_list_checker checker witness payloads =
    case payloads of
    | [payload1;payload2;payload3;payload4] =>
        checker witness payload1 payload2 payload3 payload4
    | _ => F
End

Theorem compute_literal_witnessed_payloads_sound:
  compute_literal_witnessed_payloads witness_name entry expression =
      SOME (witness,payloads) ==>
  expression =
    Let witness_name (from_cv witness)
      (App entry (MAP from_cv payloads))
Proof
  Cases_on `expression`
  >> fs [compute_literal_witnessed_payloads_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_pureFastTheory.compute_exp_to_cv_sound
  >> imp_res_tac
       compute_payloadListFastTheory.compute_literal_call_payloads_sound
  >> gvs []
QED

Theorem compute_witnessed_payloads_fast_eval_ok:
  compute_witnessed_payloads_refines approved_ceqs entry checker ==>
  compute_fast_eval_ok
    (compute_witnessed_payloads_fast_eval
      approved_ceqs witness_name entry checker)
Proof
  rw [computeTheory.compute_fast_eval_ok_def,
      compute_witnessed_payloads_fast_eval_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_literal_witnessed_payloads_sound
  >> gvs [compute_witnessed_payloads_refines_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        computeTheory.compute_default_clock,
        compute_execProofTheory.compute_eval_from_cv,
        compute_execProofTheory.subst_from_cv,
        compute_evalTheory.subst_def,
        listTheory.MAP_MAP_o,
        combinTheory.o_DEF,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> qmatch_assum_rename_tac `checker witness payloads`
  >> qpat_x_assum
       `!expression witness payloads state. _`
       (qspecl_then
         [`App entry (MAP from_cv payloads)`,`witness`,`payloads`,`s`]
         mp_tac)
  >> CONV_TAC (DEPTH_CONV ETA_CONV)
  >> simp [computeTheory.compute_default_clock]
QED

Definition compute_witnessed_payloads_fast_def:
  compute_witnessed_payloads_fast approved_ceqs witness_name entry checker
      (ths,ceqs) tm =
    compute_with
      (compute_witnessed_payloads_fast_eval
        approved_ceqs witness_name entry checker)
      (ths,ceqs) tm
End

Theorem compute_witnessed_payloads_fast_thm:
  compute_witnessed_payloads_refines approved_ceqs entry checker /\
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_witnessed_payloads_fast approved_ceqs witness_name entry checker
      (ths,ceqs) tm s = (res,s') ==>
  s' = s /\
  (!th. res = M_success th ==> THM ctxt th) /\
  (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_witnessed_payloads_fast_def]
  >> strip_tac
  >> assume_tac compute_witnessed_payloads_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac
       `compute_witnessed_payloads_fast_eval
          approved_ceqs witness_name entry checker`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

Theorem compute_literal_witnessed_payloads_from_cv[simp]:
  compute_literal_witnessed_payloads witness_name entry
    (Let witness_name (from_cv witness)
      (App entry (MAP from_cv payloads))) =
    SOME (witness,payloads)
Proof
  simp [compute_literal_witnessed_payloads_def]
QED

Theorem compute_witnessed_payloads_fast_eval_hit[simp]:
  checker witness payloads ==>
  compute_witnessed_payloads_fast_eval
      approved_ceqs witness_name entry checker approved_ceqs
      (Let witness_name (from_cv witness)
        (App entry (MAP from_cv payloads))) =
    SOME (Num 1)
Proof
  simp [compute_witnessed_payloads_fast_eval_def]
QED

Theorem compute_witnessed_payloads_fast_eval_rejects_alternate_ceqs[simp]:
  ceqs <> approved_ceqs ==>
  compute_witnessed_payloads_fast_eval
      approved_ceqs witness_name entry checker ceqs expression = NONE
Proof
  simp [compute_witnessed_payloads_fast_eval_def]
QED

Theorem compute_witnessed_payloads_fast_eval_rejects_checker_miss[simp]:
  ~checker witness payloads ==>
  compute_witnessed_payloads_fast_eval
      approved_ceqs witness_name entry checker approved_ceqs
      (Let witness_name (from_cv witness)
        (App entry (MAP from_cv payloads))) = NONE
Proof
  simp [compute_witnessed_payloads_fast_eval_def]
QED

Theorem compute_literal_witnessed_payloads_rejects_wrong_name[simp]:
  wrong_name <> witness_name ==>
  compute_literal_witnessed_payloads witness_name entry
    (Let wrong_name witness_expression body) = NONE
Proof
  simp [compute_literal_witnessed_payloads_def]
QED

Theorem compute_literal_witnessed_payloads_rejects_wrong_entry[simp]:
  wrong_entry <> entry ==>
  compute_literal_witnessed_payloads witness_name entry
    (Let witness_name (from_cv witness)
      (App wrong_entry expressions)) = NONE
Proof
  simp [compute_literal_witnessed_payloads_def,
        compute_payloadListFastTheory.compute_literal_call_payloads_def]
QED

Theorem compute_literal_witnessed_payloads_rejects_nonliteral_witness[simp]:
  compute_literal_witnessed_payloads witness_name entry
    (Let witness_name (Var variable)
      (App entry expressions)) = NONE
Proof
  simp [compute_literal_witnessed_payloads_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
QED

Theorem compute_witnessed_payload4_list_checker_exact[simp]:
  compute_witnessed_payload4_list_checker checker witness
    [payload1;payload2;payload3;payload4] =
  checker witness payload1 payload2 payload3 payload4
Proof
  simp [compute_witnessed_payload4_list_checker_def]
QED

Theorem compute_witnessed_payload4_list_checker_rejects_short[simp]:
  ~compute_witnessed_payload4_list_checker checker witness
    [payload1;payload2;payload3]
Proof
  simp [compute_witnessed_payload4_list_checker_def]
QED

Theorem compute_witnessed_payload4_list_checker_rejects_extra[simp]:
  ~compute_witnessed_payload4_list_checker checker witness
    [payload1;payload2;payload3;payload4;payload5]
Proof
  simp [compute_witnessed_payload4_list_checker_def]
QED

val _ = export_theory ();
