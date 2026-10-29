(*****************************************************************************
 * Primitive evaluator semantics for the mechanically exported packed entry.
 *
 * The exported source operations are partial at the compute-exp layer: FST
 * and SND on malformed payloads fail.  The fast checker must therefore hit
 * only on explicit encoded-rational and encoded-interval inputs.
 *****************************************************************************)
Theory compute_boundedPackedObjectPrimitiveEval
Ancestors
  compute_boundedPackedObjectEntryData
  compute_boundedPackedObjectEntryContract
Libs
  bossLib preamble

Definition bounded_packed_q_interval_encoded_def:
  bounded_packed_q_interval_encoded interval <=>
    ?lower upper.
      interval = Pair lower upper /\
      bounded_object_q_encoded lower /\
      bounded_object_q_encoded upper
End

Definition bounded_packed_q_interval_list_encoded_def:
  bounded_packed_q_interval_list_encoded intervals <=>
    EVERY bounded_packed_q_interval_encoded intervals
End

Theorem bounded_packed_q_neg_eval:
  bounded_object_q_encoded value /\
  1 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_neg» [from_cv value]) (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_neg_cv value)),refs)
Proof
  rw
    [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> Cases_on `clock`
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_boundedPackedObjectEntryDataTheory.bounded_packed_object_entry_ceqs_def,
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
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_add_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_add_cv left right)),refs)
Proof
  rw
    [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> PairCases_on `fraction'`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> Cases_on `clock`
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_boundedPackedObjectEntryDataTheory.bounded_packed_object_entry_ceqs_def,
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_def,
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
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [arithmeticTheory.ADD1,
        arithmeticTheory.LEFT_ADD_DISTRIB,
        arithmeticTheory.RIGHT_ADD_DISTRIB,
        AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

val _ = export_theory ();
