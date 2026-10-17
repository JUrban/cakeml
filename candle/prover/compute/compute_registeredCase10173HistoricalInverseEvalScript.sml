(*****************************************************************************
 * Registered evaluator semantics for the historical positive reciprocal.
 *
 * The historical first- and second-order dihedral routines use this exact
 * reciprocal at several points.  The object checker already exposes the
 * same deterministic floor/ceiling calculation; this theory connects the
 * literal source program to that object operation.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalInverseEval
Ancestors
  compute_registeredCase10173HistoricalListEval
Libs
  bossLib preamble

Definition registered_case10173_fs_hist_positive_inv_body_def:
  registered_case10173_fs_hist_positive_inv_body =
    Let «numerator»
      (Pair (App «candle_cv_fs_scale_squared» []) (Num 0))
      (Pair
        (App «candle_cv_fs_floor_div»
          [Var «numerator»;Uop Fst (Uop Snd (Var «value»))])
        (App «candle_cv_fs_ceil_div»
          [Var «numerator»;Uop Fst (Uop Fst (Var «value»))]))
End

Theorem registered_case10173_fs_hist_positive_inv_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_positive_inv» =
    SOME ([«value»],registered_case10173_fs_hist_positive_inv_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_positive_inv_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv» [from_cv value])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«value»,from_cv value)]
        registered_case10173_fs_hist_positive_inv_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_positive_inv_lookup]
QED

Theorem registered_case10173_fs_hist_positive_inv_object_eval:
  !lower upper result clock refs.
    bounded_object_fs_hist_positive_inv
        (Pair (Pair (Num lower) (Num 0))
          (Pair (Num upper) (Num 0))) = SOME result /\
    0 < lower /\ 0 < upper /\ 7 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_positive_inv»
          [from_cv
            (Pair (Pair (Num lower) (Num 0))
              (Pair (Num upper) (Num 0)))])
        (refs:hol_refs) =
      (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_positive_inv_unfold]
  >> simp
       [registered_case10173_fs_hist_positive_inv_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (Pair (Num 1000000000000000000000000) (Num 0))`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
      >> conj_tac
      >- (simp
           [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_squared_eval,
            compute_execTheory.from_cv_def]
          >> intLib.ARITH_TAC)
      >> simp
           [Once compute_evalTheory.compute_eval_def,
            compute_execTheory.from_cv_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> simp [compute_evalTheory.subst_def,compute_execTheory.from_cv_def]
  >> gvs
       [compute_boundedObjectCertificateDecimalTheory.bounded_object_fs_hist_positive_inv_def]
  >> Cases_on
       `bounded_object_fs_floor_div
          (Pair (Num 1000000000000000000000000) (Num 0)) upper`
  >> gvs []
  >> Cases_on
       `bounded_object_fs_ceil_div
          (Pair (Num 1000000000000000000000000) (Num 0)) lower`
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac
  >- (`compute_eval (clock - 2)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_floor_div»
            [Pair (Num 1000000000000000000000000) (Num 0);
             Uop Fst
               (Uop Snd
                 (Pair (Pair (Num lower) (Num 0))
                   (Pair (Num upper) (Num 0))))]) refs =
        compute_eval (clock - 2)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_floor_div»
            [from_cv
               (Pair (Num 1000000000000000000000000) (Num 0));
             from_cv (Num upper)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_evalTheory.compute_eval_def,
              compute_execTheory.from_cv_def,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_snd_def,
              compute_evalTheory.do_fst_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> intLib.ARITH_TAC)
      >> rw []
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`source` |->
                  `(Pair
                     (Num 1000000000000000000000000)
                     (Num 0):cv)`]
               compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_floor_div_eval))
      >> simp []
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 2)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_ceil_div»
          [Pair (Num 1000000000000000000000000) (Num 0);
           Uop Fst
             (Uop Fst
               (Pair (Pair (Num lower) (Num 0))
                 (Pair (Num upper) (Num 0))))]) refs =
      compute_eval (clock - 2)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_ceil_div»
          [from_cv
             (Pair (Num 1000000000000000000000000) (Num 0));
           from_cv (Num lower)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_evalTheory.compute_eval_def,
              compute_execTheory.from_cv_def,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_snd_def,
              compute_evalTheory.do_fst_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> intLib.ARITH_TAC)
  >> rw []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`source` |->
              `(Pair
                 (Num 1000000000000000000000000)
                 (Num 0):cv)`]
           compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_ceil_div_eval))
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
