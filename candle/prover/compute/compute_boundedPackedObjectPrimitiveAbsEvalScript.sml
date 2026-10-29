(*****************************************************************************
 * Source-faithful interval absolute upper bound for the exported entry.
 *
 * This deliberately models max (-lower) upper.  Equality with the more
 * symmetric max (abs lower) (abs upper) contract is proved only after the
 * interval-order invariant is available.
 *****************************************************************************)
Theory compute_boundedPackedObjectPrimitiveAbsEval
Ancestors
  compute_boundedPackedObjectPrimitiveMaxEval
  compute_boundedPackedObjectPrimitiveEval
  compute_boundedPackedObjectPrimitiveCompareEval
Libs
  bossLib preamble intLib

Definition bounded_packed_q_neg_body_def:
  bounded_packed_q_neg_body =
    Pair
      (Pair (Uop Snd (Uop Fst (Var «x»)))
        (Uop Fst (Uop Fst (Var «x»))))
      (Uop Snd (Var «x»))
End

Definition bounded_packed_q_abs_upper_body_def:
  bounded_packed_q_abs_upper_body =
    App «candle_cv_q_max»
      [App «candle_cv_q_neg» [Uop Fst (Var «i»)];
       Uop Snd (Var «i»)]
End

Definition bounded_packed_q_source_abs_upper_cv_def:
  bounded_packed_q_source_abs_upper_cv (Pair lower upper) =
    bounded_object_q_max_cv (bounded_object_q_neg_cv lower) upper /\
  bounded_packed_q_source_abs_upper_cv _ = Num 0
End

Theorem bounded_packed_q_neg_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_q_neg» =
    SOME ([«x»],bounded_packed_q_neg_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_abs_upper_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_q_abs_upper» =
    SOME ([«i»],bounded_packed_q_abs_upper_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_compute_eval_app1_argument_result:
  0 < clock /\
  compute_eval clock ceqs argument (refs:hol_refs) =
      (M_success (from_cv argument_result),refs) ==>
  compute_eval clock ceqs (App function_name [argument]) refs =
    compute_eval clock ceqs
      (App function_name [from_cv argument_result]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 1`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_compute_eval_app2_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) ==>
  compute_eval clock ceqs
      (App function_name [argument1;argument2]) refs =
    compute_eval clock ceqs
      (App function_name [from_cv result1;from_cv result2]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 2`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_neg_encoded:
  bounded_object_q_encoded value ==>
  bounded_object_q_encoded (bounded_object_q_neg_cv value)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> qexists_tac `(-fraction0,fraction1)`
  >> irule
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_decodes
  >> simp []
QED

Theorem bounded_packed_q_abs_upper_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_abs_upper» [from_cv object_interval])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst [(«i»,from_cv object_interval)]
        bounded_packed_q_abs_upper_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_q_abs_upper_lookup,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_source_abs_upper_nested_eval:
  bounded_object_q_encoded lower /\
  bounded_object_q_encoded upper /\
  5 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_max»
        [App «candle_cv_q_neg»
          [Uop Fst (Pair (from_cv lower) (from_cv upper))];
         Uop Snd (Pair (from_cv lower) (from_cv upper))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_max_cv
          (bounded_object_q_neg_cv lower) upper)),refs)
Proof
  strip_tac
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_neg»
          [Uop Fst (Pair (from_cv lower) (from_cv upper))]) refs =
      (M_success (from_cv (bounded_object_q_neg_cv lower)),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval clock bounded_packed_object_entry_ceqs
                (App «candle_cv_q_neg» [from_cv lower]) refs`
        >> conj_tac
        >- (irule bounded_packed_compute_eval_app1_argument_result
            >> simp
                 [compute_evalTheory.compute_eval_def,
                  compute_execProofTheory.compute_eval_from_cv,
                  compute_evalTheory.do_uop_def,
                  compute_evalTheory.do_fst_def,
                  ml_monadBaseTheory.st_ex_bind_def,
                  ml_monadBaseTheory.st_ex_return_def]
            >> intLib.ARITH_TAC)
        >> irule bounded_packed_q_neg_eval
        >> simp []
        >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_max»
            [from_cv (bounded_object_q_neg_cv lower);from_cv upper]) refs`
  >> conj_tac
  >- (irule bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> intLib.ARITH_TAC)
  >> irule bounded_packed_q_max_eval
  >> simp [bounded_packed_q_neg_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_source_abs_upper_eval:
  bounded_packed_q_interval_encoded object_interval /\
  6 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_abs_upper» [from_cv object_interval])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_packed_q_source_abs_upper_cv object_interval)),refs)
Proof
  rw [bounded_packed_q_interval_encoded_def]
  >> rw [bounded_packed_q_abs_upper_unfold]
  >> simp
       [bounded_packed_q_abs_upper_body_def,
        compute_evalTheory.subst_def,
        bounded_packed_q_source_abs_upper_cv_def]
  >> irule bounded_packed_q_source_abs_upper_nested_eval
  >> simp []
QED

val _ = export_theory ();
