(*****************************************************************************
 * Source-faithful exact-rational maximum for the exported packed entry.
 *****************************************************************************)
Theory compute_boundedPackedObjectPrimitiveMaxEval
Ancestors
  compute_boundedPackedObjectPrimitiveCompareEval
Libs
  bossLib preamble intLib

Definition bounded_packed_q_max_body_def:
  bounded_packed_q_max_body =
    If (App «candle_cv_q_le» [Var «x»;Var «y»])
      (Var «y») (Var «x»)
End

Theorem bounded_packed_q_max_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_q_max» =
    SOME ([«x»;«y»],bounded_packed_q_max_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_max_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_max» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_max_cv left right)),refs)
Proof
  strip_tac
  >> imp_res_tac bounded_packed_q_encoded_components
  >> gvs []
  >> Cases_on `clock`
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_q_max_lookup,
        bounded_packed_q_max_body_def,
        bounded_packed_q_le_lookup,
        bounded_packed_q_le_body_def,
        bounded_packed_q_den_lookup,
        bounded_packed_q_den_body_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max_cv_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_def,
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
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on
       `positive' * SUC denominator_minus_one +
           negative * SUC denominator_minus_one' <=
         positive * SUC denominator_minus_one' +
           negative' * SUC denominator_minus_one`
  >> fs [arithmeticTheory.ADD1,compute_execTheory.from_cv_def]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
