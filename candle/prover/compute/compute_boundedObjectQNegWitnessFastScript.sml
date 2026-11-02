(*****************************************************************************
 * Small vertical gate for the object-rational witnessed fast-evaluator seam.
 *
 * This deliberately covers one production representation operation only.
 * A checked candidate may replace ordinary evaluation exactly when it is the
 * object-rational negation of an authenticated encoded rational.  The seam
 * fails closed for malformed payloads and changed candidates.
 *****************************************************************************)
Theory compute_boundedObjectQNegWitnessFast
Ancestors
  compute_payloadListFast
  compute_boundedPackedObjectPrimitiveEval
Libs
  bossLib preamble

Definition bounded_object_q_neg_witness_ceqs_def:
  bounded_object_q_neg_witness_ceqs :
      (mlstring # (mlstring list # compute_exp)) list =
    [(«candle_cv_q_packed_object_neg_witness»,
       ([«value»;«candidate»],
        Binop Eq
          (App «candle_cv_q_neg» [Var «value»])
          (Var «candidate»)));
     («candle_cv_q_neg»,
       ([«x»],
        Pair
          (Pair (Uop Snd (Uop Fst (Var «x»)))
            (Uop Fst (Uop Fst (Var «x»))))
          (Uop Snd (Var «x»))))]
End

Definition bounded_object_q_neg_witness_checker_def:
  bounded_object_q_neg_witness_checker payloads =
    case payloads of
    | [value;candidate] =>
        bounded_object_q_encoded value /\
        candidate = bounded_object_q_neg_cv value
    | _ => F
End

Theorem bounded_object_q_neg_witness_entry_eval:
  bounded_object_q_encoded value /\
  candidate = bounded_object_q_neg_cv value ==>
  compute_eval compute_default_clock bounded_object_q_neg_witness_ceqs
    (App «candle_cv_q_packed_object_neg_witness»
      [from_cv value;from_cv candidate]) (refs:hol_refs) =
    (M_success (from_cv (Num 1)),refs)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_object_q_neg_witness_ceqs_def,
        computeTheory.compute_default_clock,
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_object_q_neg_witness_fast_refines:
  compute_payloads_call_refines bounded_object_q_neg_witness_ceqs
    «candle_cv_q_packed_object_neg_witness»
    bounded_object_q_neg_witness_checker
Proof
  rw [compute_payloadListFastTheory.compute_payloads_call_refines_def]
  >> imp_res_tac
       compute_payloadListFastTheory.compute_literal_call_payloads_sound
  >> gvs []
  >> fs [bounded_object_q_neg_witness_checker_def]
  >> every_case_tac
  >> gvs []
  >> irule
       (SIMP_RULE bool_ss [compute_execTheory.from_cv_def]
          bounded_object_q_neg_witness_entry_eval)
  >> simp []
QED

Definition bounded_object_q_neg_witness_fast_eval_def:
  bounded_object_q_neg_witness_fast_eval =
    compute_payloads_call_fast_eval bounded_object_q_neg_witness_ceqs
      «candle_cv_q_packed_object_neg_witness»
      bounded_object_q_neg_witness_checker
End

Theorem bounded_object_q_neg_witness_fast_eval_ok:
  compute_fast_eval_ok bounded_object_q_neg_witness_fast_eval
Proof
  rw [bounded_object_q_neg_witness_fast_eval_def]
  >> irule compute_payloadListFastTheory.compute_payloads_call_fast_eval_ok
  >> ACCEPT_TAC bounded_object_q_neg_witness_fast_refines
QED

Theorem bounded_object_q_neg_witness_fast_eval_hit:
  bounded_object_q_encoded value ==>
  bounded_object_q_neg_witness_fast_eval
    bounded_object_q_neg_witness_ceqs
    (App «candle_cv_q_packed_object_neg_witness»
      [from_cv value;from_cv (bounded_object_q_neg_cv value)]) =
    SOME (Num 1)
Proof
  simp
    [bounded_object_q_neg_witness_fast_eval_def,
     compute_payloadListFastTheory.compute_payloads_call_fast_eval_def,
     bounded_object_q_neg_witness_checker_def,
     compute_payloadListFastTheory.compute_literal_call_payloads_def,
     compute_payloadListFastTheory.compute_literal_payloads_def,
     compute_pureFastTheory.compute_exp_to_cv_def]
QED

Theorem bounded_object_q_neg_witness_fast_eval_rejects_changed_candidate:
  changed_candidate <> bounded_object_q_neg_cv value ==>
  bounded_object_q_neg_witness_fast_eval
    bounded_object_q_neg_witness_ceqs
    (App «candle_cv_q_packed_object_neg_witness»
      [from_cv value;from_cv changed_candidate]) = NONE
Proof
  simp
    [bounded_object_q_neg_witness_fast_eval_def,
     compute_payloadListFastTheory.compute_payloads_call_fast_eval_def,
     bounded_object_q_neg_witness_checker_def,
     compute_payloadListFastTheory.compute_literal_call_payloads_def,
     compute_payloadListFastTheory.compute_literal_payloads_def,
     compute_pureFastTheory.compute_exp_to_cv_def]
QED

val _ = export_theory ();
