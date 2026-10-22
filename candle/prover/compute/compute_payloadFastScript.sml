(*****************************************************************************
 * Payload-bound fast-evaluator seam.
 *
 * Exact-result registration authenticates one complete expression and cannot
 * scale to the nonlinear corpus.  This seam instead authenticates a fixed
 * equation environment and entry point while extracting ordinary Num/Pair
 * payload data from the call itself.  The checker may return a result only
 * for that exact literal payload; variables, executable aliases, extra
 * arguments, and alternate equation environments all miss closed.
 *
 * The reusable proof obligation is [compute_payload_call_refines].  A
 * concrete checked-word implementation must discharge it once for every
 * accepted payload, rather than registering each observed result.
 *****************************************************************************)
Theory compute_payloadFast
Ancestors
  computeProof compute_pureFast
Libs
  bossLib preamble

Definition compute_literal_call_payload_def:
  compute_literal_call_payload (entry:mlstring) (expression:compute_exp) =
    case expression of
    | App function_name [payload_expression] =>
        if function_name = entry then compute_exp_to_cv payload_expression
        else NONE
    | _ => NONE
End

Definition compute_payload_call_fast_eval_def:
  compute_payload_call_fast_eval
      (approved_ceqs:(mlstring # (mlstring list # compute_exp)) list)
      (entry:mlstring) (checker:cv -> bool) ceqs expression =
    if ceqs <> approved_ceqs then NONE
    else
      case compute_literal_call_payload entry expression of
      | NONE => NONE
      | SOME payload =>
          if checker payload then SOME (Num 1) else NONE
End

Definition compute_payload_call_refines_def:
  compute_payload_call_refines approved_ceqs entry checker <=>
    !payload_expression payload state.
      compute_exp_to_cv payload_expression = SOME payload /\
      checker payload ==>
      compute_eval compute_default_clock approved_ceqs
        (App entry [payload_expression]) state =
        (M_success (from_cv (Num 1)),state)
End

Theorem compute_literal_call_payload_sound:
  compute_literal_call_payload entry expression = SOME payload ==>
  expression = App entry [from_cv payload]
Proof
  Cases_on `expression`
  >> rw [compute_literal_call_payload_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_pureFastTheory.compute_exp_to_cv_sound
  >> gvs []
QED

Theorem compute_payload_call_fast_eval_ok:
  compute_payload_call_refines approved_ceqs entry checker ==>
  compute_fast_eval_ok
    (compute_payload_call_fast_eval approved_ceqs entry checker)
Proof
  rw [computeTheory.compute_fast_eval_ok_def,
      compute_payload_call_fast_eval_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_literal_call_payload_sound
  >> gvs [compute_payload_call_refines_def]
QED

Definition compute_payload_call_fast_def:
  compute_payload_call_fast approved_ceqs entry checker (ths,ceqs) tm =
    compute_with
      (compute_payload_call_fast_eval approved_ceqs entry checker)
      (ths,ceqs) tm
End

(* A concrete checker needs to prove only [compute_payload_call_refines].
 * The unchanged compute kernel then supplies the ordinary LCF theorem
 * construction and retains the generic evaluator as the miss path. *)
Theorem compute_payload_call_fast_thm:
  compute_payload_call_refines approved_ceqs entry checker /\
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_payload_call_fast approved_ceqs entry checker (ths,ceqs) tm s =
    (res,s') ==>
  s' = s /\
  (!th. res = M_success th ==> THM ctxt th) /\
  (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_payload_call_fast_def]
  >> strip_tac
  >> assume_tac compute_payload_call_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac
       `compute_payload_call_fast_eval approved_ceqs entry checker`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

Theorem compute_literal_call_payload_from_cv[simp]:
  compute_literal_call_payload entry (App entry [from_cv payload]) =
    SOME payload
Proof
  simp [compute_literal_call_payload_def]
QED

Theorem compute_payload_call_fast_eval_hit[simp]:
  checker payload ==>
  compute_payload_call_fast_eval approved_ceqs entry checker approved_ceqs
    (App entry [from_cv payload]) = SOME (Num 1)
Proof
  simp [compute_payload_call_fast_eval_def]
QED

Theorem compute_payload_call_fast_eval_rejects_alternate_ceqs[simp]:
  ceqs <> approved_ceqs ==>
  compute_payload_call_fast_eval approved_ceqs entry checker ceqs expression =
    NONE
Proof
  simp [compute_payload_call_fast_eval_def]
QED

Theorem compute_payload_call_fast_eval_rejects_checker_miss[simp]:
  ~checker payload ==>
  compute_payload_call_fast_eval approved_ceqs entry checker approved_ceqs
    (App entry [from_cv payload]) = NONE
Proof
  simp [compute_payload_call_fast_eval_def]
QED

Theorem compute_literal_call_payload_rejects_wrong_entry[simp]:
  wrong_entry <> entry ==>
  compute_literal_call_payload entry
    (App wrong_entry [payload_expression]) = NONE
Proof
  simp [compute_literal_call_payload_def]
QED

Theorem compute_literal_call_payload_rejects_extra_argument[simp]:
  compute_literal_call_payload entry
    (App entry [payload_expression;extra]) = NONE
Proof
  simp [compute_literal_call_payload_def]
QED

Theorem compute_literal_call_payload_rejects_variable[simp]:
  compute_literal_call_payload entry (App entry [Var variable]) = NONE
Proof
  simp [compute_literal_call_payload_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
QED

val _ = export_theory ();
