(*****************************************************************************
 * Data-driven certificate witness around an unchanged three-argument call.
 *
 * The certificate is a literal value bound by an otherwise unused Let.  The
 * ordinary compute semantics evaluates that literal and then the original
 * three-argument call.  A registered fast evaluator may inspect and check all
 * four literal values without adding a case-specific function or constant to
 * the ordinary equation environment.
 *****************************************************************************)
Theory compute_witnessedPayload3Fast
Ancestors
  compute_payload3Fast
Libs
  bossLib preamble

Definition compute_literal_witnessed_payload3_def:
  compute_literal_witnessed_payload3
      (witness_name:mlstring) (entry:mlstring) (expression:compute_exp) =
    case expression of
    | Let bound_name witness_expression body =>
        (if bound_name <> witness_name then NONE
         else
           case compute_exp_to_cv witness_expression of
           | NONE => NONE
           | SOME witness =>
               case compute_literal_call_payload3 entry body of
               | NONE => NONE
               | SOME (payload1,payload2,payload3) =>
                   SOME (witness,payload1,payload2,payload3))
    | _ => NONE
End

Definition compute_witnessed_payload3_fast_eval_def:
  compute_witnessed_payload3_fast_eval
      (approved_ceqs:(mlstring # (mlstring list # compute_exp)) list)
      (witness_name:mlstring) (entry:mlstring)
      (checker:cv -> cv -> cv -> cv -> bool) ceqs expression =
    if ceqs <> approved_ceqs then NONE
    else
      case compute_literal_witnessed_payload3 witness_name entry expression of
      | NONE => NONE
      | SOME (witness,payload1,payload2,payload3) =>
          if checker witness payload1 payload2 payload3 then SOME (Num 1)
          else NONE
End

Definition compute_witnessed_payload3_refines_def:
  compute_witnessed_payload3_refines approved_ceqs entry checker <=>
    !first_expression second_expression third_expression witness payload1
     payload2 payload3 state.
      compute_exp_to_cv first_expression = SOME payload1 /\
      compute_exp_to_cv second_expression = SOME payload2 /\
      compute_exp_to_cv third_expression = SOME payload3 /\
      checker witness payload1 payload2 payload3 ==>
      compute_eval (compute_default_clock - 1) approved_ceqs
        (App entry
          [first_expression;second_expression;third_expression]) state =
        (M_success (from_cv (Num 1)),state)
End

Theorem compute_literal_witnessed_payload3_sound:
  compute_literal_witnessed_payload3 witness_name entry expression =
      SOME (witness,payload1,payload2,payload3) ==>
  expression =
    Let witness_name (from_cv witness)
      (App entry [from_cv payload1;from_cv payload2;from_cv payload3])
Proof
  Cases_on `expression`
  >> fs [compute_literal_witnessed_payload3_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_pureFastTheory.compute_exp_to_cv_sound
  >> imp_res_tac compute_payload3FastTheory.compute_literal_call_payload3_sound
  >> gvs []
QED

Theorem compute_witnessed_payload3_fast_eval_ok:
  compute_witnessed_payload3_refines approved_ceqs entry checker ==>
  compute_fast_eval_ok
    (compute_witnessed_payload3_fast_eval
      approved_ceqs witness_name entry checker)
Proof
  rw [computeTheory.compute_fast_eval_ok_def,
      compute_witnessed_payload3_fast_eval_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_literal_witnessed_payload3_sound
  >> gvs [compute_witnessed_payload3_refines_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        computeTheory.compute_default_clock,
        compute_execProofTheory.compute_eval_from_cv,
        compute_execProofTheory.subst_from_cv,
        compute_evalTheory.subst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> qmatch_assum_rename_tac
       ‘checker witness payload1 payload2 payload3’
  >> qpat_x_assum
       ‘∀first_expression second_expression third_expression witness payload1
          payload2 payload3 state. _’
       (qspecl_then
         [‘from_cv payload1’,‘from_cv payload2’,‘from_cv payload3’,‘witness’,
          ‘payload1’,‘payload2’,‘payload3’,‘s’]
         mp_tac)
  >> simp [computeTheory.compute_default_clock]
QED

Definition compute_witnessed_payload3_fast_def:
  compute_witnessed_payload3_fast approved_ceqs witness_name entry checker
      (ths,ceqs) tm =
    compute_with
      (compute_witnessed_payload3_fast_eval
        approved_ceqs witness_name entry checker)
      (ths,ceqs) tm
End

Theorem compute_witnessed_payload3_fast_thm:
  compute_witnessed_payload3_refines approved_ceqs entry checker /\
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_witnessed_payload3_fast approved_ceqs witness_name entry checker
      (ths,ceqs) tm s = (res,s') ==>
  s' = s /\
  (!th. res = M_success th ==> THM ctxt th) /\
  (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_witnessed_payload3_fast_def]
  >> strip_tac
  >> assume_tac compute_witnessed_payload3_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac
       `compute_witnessed_payload3_fast_eval
          approved_ceqs witness_name entry checker`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

Theorem compute_literal_witnessed_payload3_from_cv[simp]:
  compute_literal_witnessed_payload3 witness_name entry
    (Let witness_name (from_cv witness)
      (App entry [from_cv payload1;from_cv payload2;from_cv payload3])) =
    SOME (witness,payload1,payload2,payload3)
Proof
  simp [compute_literal_witnessed_payload3_def]
QED

Theorem compute_witnessed_payload3_fast_eval_hit[simp]:
  checker witness payload1 payload2 payload3 ==>
  compute_witnessed_payload3_fast_eval
      approved_ceqs witness_name entry checker approved_ceqs
      (Let witness_name (from_cv witness)
        (App entry [from_cv payload1;from_cv payload2;from_cv payload3])) =
    SOME (Num 1)
Proof
  simp [compute_witnessed_payload3_fast_eval_def]
QED

Theorem compute_witnessed_payload3_fast_eval_rejects_alternate_ceqs[simp]:
  ceqs <> approved_ceqs ==>
  compute_witnessed_payload3_fast_eval
      approved_ceqs witness_name entry checker ceqs expression = NONE
Proof
  simp [compute_witnessed_payload3_fast_eval_def]
QED

Theorem compute_witnessed_payload3_fast_eval_rejects_checker_miss[simp]:
  ~checker witness payload1 payload2 payload3 ==>
  compute_witnessed_payload3_fast_eval
      approved_ceqs witness_name entry checker approved_ceqs
      (Let witness_name (from_cv witness)
        (App entry [from_cv payload1;from_cv payload2;from_cv payload3])) = NONE
Proof
  simp [compute_witnessed_payload3_fast_eval_def]
QED

Theorem compute_literal_witnessed_payload3_rejects_wrong_name[simp]:
  wrong_name <> witness_name ==>
  compute_literal_witnessed_payload3 witness_name entry
    (Let wrong_name witness_expression body) = NONE
Proof
  simp [compute_literal_witnessed_payload3_def]
QED

Theorem compute_literal_witnessed_payload3_rejects_wrong_entry[simp]:
  wrong_entry <> entry ==>
  compute_literal_witnessed_payload3 witness_name entry
    (Let witness_name (from_cv witness)
      (App wrong_entry [from_cv payload1;from_cv payload2;from_cv payload3])) =
    NONE
Proof
  simp [compute_literal_witnessed_payload3_def,
        compute_payload3FastTheory.compute_literal_call_payload3_def]
QED

Theorem compute_literal_witnessed_payload3_rejects_nonliteral_witness[simp]:
  compute_literal_witnessed_payload3 witness_name entry
    (Let witness_name (Var variable)
      (App entry [from_cv payload1;from_cv payload2;from_cv payload3])) = NONE
Proof
  simp [compute_literal_witnessed_payload3_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
QED

Theorem compute_literal_witnessed_payload3_rejects_short_call[simp]:
  compute_literal_witnessed_payload3 witness_name entry
    (Let witness_name (from_cv witness)
      (App entry [from_cv payload1;from_cv payload2])) = NONE
Proof
  simp [compute_literal_witnessed_payload3_def,
        compute_payload3FastTheory.compute_literal_call_payload3_def]
QED

val _ = export_theory ();
