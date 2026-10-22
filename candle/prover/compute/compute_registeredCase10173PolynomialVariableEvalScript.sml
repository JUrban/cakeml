(*****************************************************************************
 * Registered evaluator semantics for polynomial coordinate leaves.
 *
 * The historical source builds a coordinate gradient recursively from the
 * dimension list.  This file keeps that exact source recursion and relates
 * it to the decimal unit vector consumed by the compact checker.
 *****************************************************************************)
Theory compute_registeredCase10173PolynomialVariableEval
Ancestors
  compute_registeredCase10173PolynomialShapeEval
Libs
  bossLib preamble

Definition registered_case10173_fs_interval_unit_body_def:
  registered_case10173_fs_interval_unit_body =
    If (Uop Ispair (Var «items»))
      (If (Uop Ispair (Var «variable»))
        (App «candle_cv_fs_interval_zeros» [Var «items»])
        (If (Binop Eq (Var «variable») (Num 0))
          (Pair (App «candle_cv_fs_interval_one» [])
            (App «candle_cv_fs_interval_zeros» [Uop Snd (Var «items»)]))
          (Pair (App «candle_cv_fs_interval_zero» [])
            (App «candle_cv_fs_interval_unit»
              [Binop Sub (Var «variable») (Num 1);
               Uop Snd (Var «items»)]))))
      (Num 0)
End

Definition registered_case10173_interval_unit_decimal_def:
  registered_case10173_interval_unit_decimal variable [] = [] /\
  registered_case10173_interval_unit_decimal 0 (item::items) =
    bounded_atan_one_decimal::
      REPLICATE (LENGTH items) bounded_interval64_zero /\
  registered_case10173_interval_unit_decimal (SUC variable) (item::items) =
    bounded_interval64_zero::
      registered_case10173_interval_unit_decimal variable items
End

Theorem registered_case10173_fs_interval_unit_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_unit» =
    SOME
      ([«variable»;«items»],
       registered_case10173_fs_interval_unit_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_unit_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_unit»
        [from_cv variable;from_cv items]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«variable»,from_cv variable);(«items»,from_cv items)]
        registered_case10173_fs_interval_unit_body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        registered_case10173_fs_interval_unit_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_fs_interval_unit_num_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_unit»
        [Num variable;from_cv items]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«variable»,Num variable);(«items»,from_cv items)]
        registered_case10173_fs_interval_unit_body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        registered_case10173_fs_interval_unit_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_fs_interval_unit_zero_cons_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_one» []) (refs:hol_refs) =
    (M_success (from_cv (one_cv:cv)),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zeros» [from_cv items]) refs =
    (M_success (from_cv (zeros_cv:cv)),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_unit»
        [Num 0;from_cv (Pair item items)]) refs =
    (M_success (from_cv (Pair one_cv zeros_cv)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_unit_num_unfold]
  >> simp
       [registered_case10173_fs_interval_unit_body_def,
        compute_evalTheory.subst_def,
        compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST [`argument` |-> `(Num 0:cv)`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Binop Eq (Num 0) (Num 0)) refs =
      (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_eq_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac >- simp []
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_zeros»
          [Uop Snd (Pair (from_cv item) (from_cv items))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_zeros» [from_cv items]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> simp []
QED

Theorem registered_case10173_fs_interval_unit_suc_cons_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zero» []) (refs:hol_refs) =
    (M_success (from_cv (zero_cv:cv)),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_unit»
        [Num variable;from_cv items]) refs =
    (M_success (from_cv (unit_cv:cv)),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_unit»
        [Num (SUC variable);from_cv (Pair item items)]) refs =
    (M_success (from_cv (Pair zero_cv unit_cv)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_unit_num_unfold]
  >> simp
       [registered_case10173_fs_interval_unit_body_def,
        compute_evalTheory.subst_def,
        compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST [`argument` |-> `(Num (SUC variable):cv)`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Binop Eq (Num (SUC variable)) (Num 0)) refs =
      (M_success (Num 0),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_eq_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac >- simp []
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_unit»
          [Binop Sub (Num (SUC variable)) (Num 1);
           Uop Snd (Pair (from_cv item) (from_cv items))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_unit»
          [from_cv (Num variable);from_cv items]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> conj_tac
        >- simp
             [compute_evalTheory.compute_eval_def,
              compute_evalTheory.do_binop_def,
              compute_evalTheory.do_arith_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> fs [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_fs_interval_unit_object_eval:
  !items variable clock refs.
    variable < LENGTH items /\
    8 * (LENGTH items + 1) < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_unit»
          [Num variable;
           from_cv (bounded_interval64_object_cv_list items)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_interval64_object_cv_list
            (registered_case10173_interval_unit_decimal variable items))),refs)
Proof
  Induct_on `items`
  >- simp []
  >> Cases_on `variable`
  >- (rpt gen_tac
      >> strip_tac
      >> PURE_REWRITE_TAC
           [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
            registered_case10173_interval_unit_decimal_def]
      >> irule registered_case10173_fs_interval_unit_zero_cons_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (simp_tac std_ss
            [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
             compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
             compute_boundedAtanDecimalTheory.bounded_atan_one_decimal_def,
             compute_execTheory.from_cv_def]
          >> simp []
          >> irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_one_eval)
          >> intLib.ARITH_TAC)
      >> irule registered_case10173_fs_interval_zeros_object_eval
      >> qpat_x_assum `8 * (LENGTH (h::items) + 1) < clock` mp_tac
      >> simp []
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> strip_tac
  >> PURE_REWRITE_TAC
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        registered_case10173_interval_unit_decimal_def]
  >> irule registered_case10173_fs_interval_unit_suc_cons_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (qpat_x_assum `!variable clock refs. _`
       (qspecl_then [`n`,`clock - 1`,`refs`] mp_tac)
      >> impl_tac
      >- (qpat_x_assum `SUC n < LENGTH (h::items)` mp_tac
          >> qpat_x_assum `8 * (LENGTH (h::items) + 1) < clock` mp_tac
          >> simp []
          >> intLib.ARITH_TAC)
      >> simp [])
  >> simp_tac std_ss
        [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
         compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
         compute_boundedIntervalListTheory.bounded_interval64_zero_def,
         compute_execTheory.from_cv_def]
  >> simp []
  >> irule
    (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
      compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_zero_eval)
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_interval_unit_decimal_six:
  LENGTH items = 6 /\ variable < 6 ==>
  registered_case10173_interval_unit_decimal variable items =
    THE (bounded_interval64_unit_vector_decimal variable)
Proof
  strip_tac
  >> fs [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_interval64_unit_vector_decimal_def]
  >> Cases_on `items` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> (Cases_on `variable`
      >> fs [registered_case10173_interval_unit_decimal_def]
      >- EVAL_TAC)
  >> (Cases_on `n`
      >> fs [registered_case10173_interval_unit_decimal_def]
      >- EVAL_TAC)
  >> (Cases_on `n'`
      >> fs [registered_case10173_interval_unit_decimal_def]
      >- EVAL_TAC)
  >> (Cases_on `n`
      >> fs [registered_case10173_interval_unit_decimal_def]
      >- EVAL_TAC)
  >> (Cases_on `n'`
      >> fs [registered_case10173_interval_unit_decimal_def]
      >- EVAL_TAC)
  >> Cases_on `n` >> fs [registered_case10173_interval_unit_decimal_def]
QED

val _ = export_theory ();
