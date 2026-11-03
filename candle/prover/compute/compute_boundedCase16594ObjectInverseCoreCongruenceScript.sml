(*****************************************************************************
 * Transfer the proved exact-object inverse/interval arithmetic core into the
 * complete case-16594 dispatcher.  Agreement is authenticated on the whole
 * closed 13-function production call graph, so individual evaluator proofs
 * need not be
 * duplicated for the larger equation environment.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseCoreCongruence
Ancestors
  compute_boundedCase16594ObjectCoreCongruence
  compute_boundedObjectIntervalInverseWitnessFast
Libs
  bossLib preamble

Definition bounded_case16594_object_inverse_core_def:
  bounded_case16594_object_inverse_core : mlstring list =
    TL (MAP FST bounded_object_interval_inverse_witness_ceqs)
End

Theorem bounded_case16594_object_inverse_core_count:
  LENGTH bounded_case16594_object_inverse_core = 13
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_inverse_core_old_closed:
  compute_ceqs_closed_on bounded_case16594_object_inverse_core
    bounded_object_interval_inverse_witness_ceqs
Proof
  irule compute_evalRestrictedCongruenceTheory.compute_ceqs_closed_on_from_every
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_inverse_core_agree:
  compute_ceqs_agree_on bounded_case16594_object_inverse_core
    bounded_object_interval_inverse_witness_ceqs
    bounded_case16594_object_dispatch_cell0_ceqs
Proof
  irule compute_evalRestrictedCongruenceTheory.compute_ceqs_agree_on_from_every
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_inverse_core_current_closed:
  compute_ceqs_closed_on bounded_case16594_object_inverse_core
    bounded_case16594_object_dispatch_cell0_ceqs
Proof
  irule
    compute_boundedCase16594ObjectCoreCongruenceTheory.compute_ceqs_closed_on_agree_right
  >> metis_tac
       [bounded_case16594_object_inverse_core_old_closed,
        bounded_case16594_object_inverse_core_agree]
QED

Theorem bounded_case16594_object_inverse_core_eval_cong:
  compute_exp_uses_only bounded_case16594_object_inverse_core expression ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs expression
      (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs expression
      refs
Proof
  strip_tac
  >> irule
       (CONJUNCT1
         compute_evalRestrictedCongruenceTheory.compute_eval_restricted_cong)
  >> metis_tac
       [bounded_case16594_object_inverse_core_old_closed,
        bounded_case16594_object_inverse_core_current_closed,
        bounded_case16594_object_inverse_core_agree]
QED

Theorem bounded_case16594_object_inverse_core_literal_app_eval_from_old:
  MEM (function_name:mlstring) bounded_case16594_object_inverse_core /\
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App function_name (MAP from_cv payloads)) (refs:hol_refs) = outcome ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App function_name (MAP from_cv payloads)) refs = outcome
Proof
  strip_tac
  >> `compute_exp_uses_only bounded_case16594_object_inverse_core
        (App function_name (MAP from_cv payloads))` by
       simp
         [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
          EVERY_MAP,
          compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_uses_only_from_cv]
  >> metis_tac [bounded_case16594_object_inverse_core_eval_cong]
QED

Theorem bounded_case16594_object_q_interval_mul_eval:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right /\
  8 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_mul» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_mul_cv left right)),refs)
Proof
  strip_tac
  >> `compute_exp_uses_only bounded_case16594_object_inverse_core
        (App «candle_cv_q_interval_mul» [from_cv left;from_cv right])` by
       (simp
          [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
           bounded_case16594_object_inverse_core_def,
           compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_uses_only_from_cv]
        >> EVAL_TAC)
  >> `compute_eval clock bounded_object_interval_inverse_witness_ceqs
        (App «candle_cv_q_interval_mul» [from_cv left;from_cv right])
        (refs:hol_refs) =
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_mul» [from_cv left;from_cv right]) refs` by
       metis_tac [bounded_case16594_object_inverse_core_eval_cong]
  >> `compute_eval clock bounded_object_interval_inverse_witness_ceqs
        (App «candle_cv_q_interval_mul» [from_cv left;from_cv right])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_object_q_interval_mul_cv left right)),refs)` by
       metis_tac
         [compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_q_interval_mul_eval]
  >> metis_tac []
QED

val _ = export_theory ();
