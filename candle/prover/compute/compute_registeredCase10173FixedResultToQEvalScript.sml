(*****************************************************************************
 * Generic registered conversion of fixed-scale interval lists and matrices
 * to the exact-rational representation used by the certified Taylor finish.
 *
 * The literal decimal checker returns a typed fixed result.  This layer is
 * deliberately packet-parametric: it proves the two recursive source
 * conversions once, instead of closing one evaluator theorem per certificate
 * job.
 *****************************************************************************)
Theory compute_registeredCase10173FixedResultToQEval
Ancestors
  compute_registeredCase10173CertifiedFinishEval
  compute_registeredCase10173HistoricalNegListEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fixed_q_endpoint_cv_def:
  registered_case10173_fixed_q_endpoint_cv endpoint =
    Pair (bounded_signed64_object_cv endpoint) (Num 999999999999)
End

Definition registered_case10173_fixed_q_interval_cv_def:
  registered_case10173_fixed_q_interval_cv
      (BoundedInterval64 lower upper) =
    Pair
      (registered_case10173_fixed_q_endpoint_cv lower)
      (registered_case10173_fixed_q_endpoint_cv upper)
End

Definition registered_case10173_fixed_q_interval_list_cv_def:
  registered_case10173_fixed_q_interval_list_cv [] = (Num 0 : cv) /\
  registered_case10173_fixed_q_interval_list_cv (value::values) =
    Pair (registered_case10173_fixed_q_interval_cv value)
      (registered_case10173_fixed_q_interval_list_cv values)
End

Definition registered_case10173_fixed_q_interval_matrix_cv_def:
  registered_case10173_fixed_q_interval_matrix_cv [] = (Num 0 : cv) /\
  registered_case10173_fixed_q_interval_matrix_cv (row::rows) =
    Pair (registered_case10173_fixed_q_interval_list_cv row)
      (registered_case10173_fixed_q_interval_matrix_cv rows)
End

Definition registered_case10173_fs_interval_list_to_q_body_def:
  registered_case10173_fs_interval_list_to_q_body =
    If (Uop Ispair (Var «items»))
      (Pair
        (App «candle_cv_fs_interval_to_q» [Uop Fst (Var «items»)])
        (App «candle_cv_fs_interval_list_to_q» [Uop Snd (Var «items»)]))
      (Num 0)
End

Definition registered_case10173_fs_interval_matrix_to_q_body_def:
  registered_case10173_fs_interval_matrix_to_q_body =
    If (Uop Ispair (Var «row_lists»))
      (Pair
        (App «candle_cv_fs_interval_list_to_q»
          [Uop Fst (Var «row_lists»)])
        (App «candle_cv_fs_interval_matrix_to_q»
          [Uop Snd (Var «row_lists»)]))
      (Num 0)
End

Theorem registered_case10173_fs_interval_list_to_q_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_list_to_q» =
    SOME ([«items»],registered_case10173_fs_interval_list_to_q_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_matrix_to_q_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_matrix_to_q» =
    SOME
      ([«row_lists»],registered_case10173_fs_interval_matrix_to_q_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_list_to_q_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_to_q» [from_cv items])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«items»,from_cv items)]
        registered_case10173_fs_interval_list_to_q_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_list_to_q_lookup]
QED

Theorem registered_case10173_fs_interval_matrix_to_q_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_to_q» [from_cv rows])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«row_lists»,from_cv rows)]
        registered_case10173_fs_interval_matrix_to_q_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_matrix_to_q_lookup]
QED

Theorem registered_case10173_fs_interval_to_q_typed_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_to_q»
        [from_cv (bounded_interval64_object_cv value)]) (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_fixed_q_interval_cv value)),refs)
Proof
  Cases_on `value`
  >> PURE_REWRITE_TAC
       [registered_case10173_fixed_q_interval_cv_def,
        registered_case10173_fixed_q_endpoint_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
  >> ACCEPT_TAC
       (Q.INST
         [`lower` |-> `bounded_signed64_object_cv b`,
          `upper` |-> `bounded_signed64_object_cv b0`]
         compute_registeredCase10173SqrtPrimitiveEvalTheory.registered_case10173_fs_interval_to_q_eval)
QED

Theorem registered_case10173_fs_interval_list_to_q_typed_eval:
  !clock refs.
    LENGTH values + 4 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_to_q»
          [from_cv (bounded_interval64_object_cv_list values)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (registered_case10173_fixed_q_interval_list_cv values)),refs)
Proof
  Induct_on `values`
  >- (rpt strip_tac
      >> rw [registered_case10173_fs_interval_list_to_q_unfold]
      >> simp
           [registered_case10173_fs_interval_list_to_q_body_def,
            compute_evalTheory.subst_def,
            compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
            registered_case10173_fixed_q_interval_list_cv_def,
            compute_execTheory.from_cv_def,
            Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> rw [registered_case10173_fs_interval_list_to_q_unfold]
  >> simp
       [registered_case10173_fs_interval_list_to_q_body_def,
        compute_evalTheory.subst_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        registered_case10173_fixed_q_interval_list_cv_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (bounded_interval64_object_cv h)
                 (bounded_interval64_object_cv_list values):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
            [`left_result` |->
              `registered_case10173_fixed_q_interval_cv h`,
             `right_result` |->
              `registered_case10173_fixed_q_interval_list_cv values`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_to_q»
            [Uop Fst
               (Pair (from_cv (bounded_interval64_object_cv h))
                 (from_cv
                   (bounded_interval64_object_cv_list values)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_to_q»
            [from_cv (bounded_interval64_object_cv h)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
      >> rw []
      >> irule registered_case10173_fs_interval_to_q_typed_eval
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_to_q»
          [Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv h))
               (from_cv
                 (bounded_interval64_object_cv_list values)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_to_q»
          [from_cv (bounded_interval64_object_cv_list values)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> rw []
  >> first_x_assum (qspecl_then [`clock - 1`,`refs`] mp_tac)
  >> impl_tac >- fs [arithmeticTheory.LESS_EQ]
  >> simp []
QED

Theorem registered_case10173_fs_interval_matrix_to_q_typed_eval:
  !clock refs.
    SUM (MAP LENGTH rows) + LENGTH rows + 4 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_to_q»
          [from_cv (bounded_interval64_object_cv_matrix rows)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (registered_case10173_fixed_q_interval_matrix_cv rows)),refs)
Proof
  Induct_on `rows`
  >- (rpt strip_tac
      >> rw [registered_case10173_fs_interval_matrix_to_q_unfold]
      >> simp
           [registered_case10173_fs_interval_matrix_to_q_body_def,
            compute_evalTheory.subst_def,
            compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def,
            registered_case10173_fixed_q_interval_matrix_cv_def,
            compute_execTheory.from_cv_def,
            Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> rw [registered_case10173_fs_interval_matrix_to_q_unfold]
  >> simp
       [registered_case10173_fs_interval_matrix_to_q_body_def,
        compute_evalTheory.subst_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def,
        registered_case10173_fixed_q_interval_matrix_cv_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (bounded_interval64_object_cv_list h)
                 (bounded_interval64_object_cv_matrix rows):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |->
              `registered_case10173_fixed_q_interval_list_cv h`,
            `right_result` |->
              `registered_case10173_fixed_q_interval_matrix_cv rows`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_list_to_q»
            [Uop Fst
               (Pair (from_cv (bounded_interval64_object_cv_list h))
                 (from_cv
                   (bounded_interval64_object_cv_matrix rows)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_list_to_q»
            [from_cv (bounded_interval64_object_cv_list h)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
      >> rw []
      >> irule registered_case10173_fs_interval_list_to_q_typed_eval
      >> fs [arithmeticTheory.LESS_EQ])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_to_q»
          [Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv_list h))
               (from_cv
                 (bounded_interval64_object_cv_matrix rows)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_to_q»
          [from_cv (bounded_interval64_object_cv_matrix rows)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> rw []
  >> first_x_assum (qspecl_then [`clock - 1`,`refs`] mp_tac)
  >> impl_tac >- fs [arithmeticTheory.LESS_EQ]
  >> simp []
QED

val _ = export_theory ();
