(*****************************************************************************
 * Refinement of the mechanically exported packed-object entry.
 *****************************************************************************)
Theory compute_boundedPackedObjectEntryRefinement
Ancestors
  compute_boundedPackedObjectFinishEval
  compute_payloadListFast
Libs
  bossLib preamble

Definition bounded_packed_object_source_accept6_def:
  bounded_packed_object_source_accept6 radii center_value
      center_gradient hessian <=>
    EVERY bounded_object_q_encoded radii /\
    LENGTH radii = 6 /\
    bounded_packed_q_interval_encoded center_value /\
    EVERY bounded_packed_q_interval_encoded center_gradient /\
    LENGTH center_gradient = 6 /\
    EVERY bounded_packed_q_interval_encoded hessian /\
    LENGTH hessian = 21 /\
    bounded_object_q_strict_negative_cv
      (bounded_packed_q_source_interval_upper_cv
        (bounded_packed_q_source_value_bound6_cv
          radii center_value center_gradient hessian))
End

Definition bounded_packed_object_source_payload5_checker_def:
  bounded_packed_object_source_payload5_checker
      domain_payload radii_payload center_value center_gradient_payload
      hessian_payload =
    if domain_payload <> Num 1 then F
    else
      case bounded_object_q_cv_list_decode radii_payload of
      | NONE => F
      | SOME radii =>
        case bounded_object_q_cv_list_decode center_gradient_payload of
        | NONE => F
        | SOME center_gradient =>
          case bounded_object_q_cv_list_decode hessian_payload of
          | NONE => F
          | SOME hessian =>
              bounded_packed_object_source_accept6 radii center_value
                center_gradient hessian
End

Theorem bounded_packed_object_source_payload5_checker_canonical[simp]:
  bounded_packed_object_source_payload5_checker
      (Num 1) (bounded_object_q_cv_list radii) center_value
      (bounded_object_q_cv_list center_gradient)
      (bounded_object_q_cv_list hessian) <=>
    bounded_packed_object_source_accept6 radii center_value
      center_gradient hessian
Proof
  simp [bounded_packed_object_source_payload5_checker_def]
QED

Theorem bounded_object_q_cv_list_encode_decode:
  !items payload.
    bounded_object_q_cv_list_decode payload = SOME items ==>
    bounded_object_q_cv_list items = payload
Proof
  Induct_on `items`
  >> Cases_on `payload`
  >> TRY (Cases_on `n`)
  >> simp
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_decode_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> every_case_tac
  >> gvs []
QED

Theorem compute_payload5_list_checker_components:
  compute_payload5_list_checker checker payloads ==>
  ?payload1 payload2 payload3 payload4 payload5.
    payloads = [payload1;payload2;payload3;payload4;payload5] /\
    checker payload1 payload2 payload3 payload4 payload5
Proof
  rw [compute_payload5_list_checker_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_packed_object_entry_canonical_eval:
  bounded_packed_object_source_accept6 radii center_value
      center_gradient hessian ==>
  compute_eval compute_default_clock bounded_packed_object_entry_ceqs
    (App «candle_cv_q_packed_object_accept6»
      [from_cv (Num 1);
       from_cv (bounded_object_q_cv_list radii);
       from_cv center_value;
       from_cv (bounded_object_q_cv_list center_gradient);
       from_cv (bounded_object_q_cv_list hessian)]) (refs:hol_refs) =
    (M_success (from_cv (Num 1)),refs)
Proof
  rw [bounded_packed_object_source_accept6_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_boundedPackedObjectFinishEvalTheory.bounded_packed_q_accept6_eval)
  >> simp [computeTheory.compute_default_clock]
QED

Theorem bounded_packed_object_entry_refines_exact_checker:
  compute_payloads_call_refines
    bounded_packed_object_entry_ceqs
    «candle_cv_q_packed_object_accept6»
    (compute_payload5_list_checker
      bounded_packed_object_source_payload5_checker)
Proof
  rw [compute_payloads_call_refines_def]
  >> imp_res_tac compute_literal_call_payloads_sound
  >> imp_res_tac compute_payload5_list_checker_components
  >> gvs []
  >> fs [bounded_packed_object_source_payload5_checker_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_q_cv_list_encode_decode
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_object_entry_canonical_eval)
  >> simp []
QED

val _ = export_theory ();
