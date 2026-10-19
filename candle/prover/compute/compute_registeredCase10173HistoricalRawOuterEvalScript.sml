(*****************************************************************************
 * Registered evaluator semantics for the historical raw interval outer map.
 *
 * The multiplication Hessian contains both ordered gradient outer products.
 * This theorem follows the literal source recursion and reuses the proved raw
 * interval-list scaling relation for every row.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalRawOuterEval
Ancestors
  compute_registeredCase10173HistoricalRawMatrixAddEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_raw_interval_outer_body_def:
  registered_case10173_fs_raw_interval_outer_body =
    If (Uop Ispair (Var «xs»))
      (Pair
        (App «candle_cv_fs_raw_interval_list_scale»
          [Uop Fst (Var «xs»);Var «ys»])
        (App «candle_cv_fs_raw_interval_outer»
          [Uop Snd (Var «xs»);Var «ys»]))
      (Num 0)
End

Definition registered_case10173_fs_raw_interval_outer_object_def:
  registered_case10173_fs_raw_interval_outer_object
      ([]:cv list) right = SOME [] /\
  registered_case10173_fs_raw_interval_outer_object
      (left::left_rest) right =
    (case registered_case10173_fs_raw_interval_list_scale_object left right of
     | NONE => NONE
     | SOME row =>
       case registered_case10173_fs_raw_interval_outer_object
         left_rest right of
       | NONE => NONE
       | SOME rows => SOME (row::rows))
End

Theorem registered_case10173_fs_raw_interval_outer_object_shape:
  !right result.
    registered_case10173_fs_raw_interval_outer_object
      left right = SOME result ==>
    LENGTH result = LENGTH left /\
    EVERY ($= (LENGTH right)) (MAP LENGTH result)
Proof
  Induct_on `left`
  >> rw [registered_case10173_fs_raw_interval_outer_object_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_length
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_fs_raw_interval_outer_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_interval_outer» =
    SOME
      ([«xs»;«ys»],
       registered_case10173_fs_raw_interval_outer_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_interval_outer_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_outer»
        [from_cv (registered_case10173_cv_list left);
         from_cv (registered_case10173_cv_list right)])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«xs»,from_cv (registered_case10173_cv_list left));
         («ys»,from_cv (registered_case10173_cv_list right))]
        registered_case10173_fs_raw_interval_outer_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_interval_outer_lookup]
QED

Theorem registered_case10173_fs_raw_interval_outer_object_eval:
  !right result clock refs.
    registered_case10173_fs_raw_interval_outer_object
        left right = SOME result /\
    LENGTH left * (LENGTH right + 1) + 4 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_outer»
          [from_cv (registered_case10173_cv_list left);
           from_cv (registered_case10173_cv_list right)])
        (refs:hol_refs) =
      (M_success
        (from_cv (registered_case10173_cv_matrix result)),refs)
Proof
  Induct_on `left`
  >- (rpt strip_tac
      >> gvs [registered_case10173_fs_raw_interval_outer_object_def]
      >> rw [registered_case10173_fs_raw_interval_outer_unfold]
      >> simp
           [registered_case10173_fs_raw_interval_outer_body_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_cv_matrix_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
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
  >> Cases_on
       `registered_case10173_fs_raw_interval_list_scale_object h right`
  >> gvs [registered_case10173_fs_raw_interval_outer_object_def]
  >> Cases_on
       `registered_case10173_fs_raw_interval_outer_object left right`
  >> gvs [registered_case10173_fs_raw_interval_outer_object_def]
  >> rw [registered_case10173_fs_raw_interval_outer_unfold]
  >> simp
       [registered_case10173_fs_raw_interval_outer_body_def,
        compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_cv_matrix_cons,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair h (registered_case10173_cv_list left):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `registered_case10173_cv_list x`,
            `right_result` |-> `registered_case10173_cv_matrix x'`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_scale»
            [Uop Fst
               (Pair (from_cv h)
                 (from_cv (registered_case10173_cv_list left)));
             from_cv (registered_case10173_cv_list right)]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_scale»
            [from_cv h;
             from_cv (registered_case10173_cv_list right)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
        >> intLib.ARITH_TAC)
      >> rw []
      >> irule
           compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_eval
      >> conj_tac
      >- (qpat_x_assum `SUC _ * _ + 4 < _` mp_tac
          >> simp [arithmeticTheory.MULT_CLAUSES]
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_outer»
          [Uop Snd
             (Pair (from_cv h)
               (from_cv (registered_case10173_cv_list left)));
           from_cv (registered_case10173_cv_list right)]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_outer»
          [from_cv (registered_case10173_cv_list left);
           from_cv (registered_case10173_cv_list right)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
        >> intLib.ARITH_TAC)
  >> rw []
  >> first_x_assum irule
  >> conj_tac
  >- (qpat_x_assum `SUC _ * _ + 4 < _` mp_tac
      >> simp [arithmeticTheory.MULT_CLAUSES]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
