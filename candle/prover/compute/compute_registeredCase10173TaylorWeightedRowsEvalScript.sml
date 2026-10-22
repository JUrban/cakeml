(*****************************************************************************
 * Registered evaluator refinement for fixed-scale weighted Hessian rows.
 *
 * Each source step computes the absolute dot bound for one Hessian row,
 * multiplies it by the corresponding radius and accumulates the result.  The
 * theorem below connects that literal recursion to the bounded-object
 * implementation used by the fast Taylor checker.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorWeightedRowsEval
Ancestors
  compute_registeredCase10173TaylorDotEval
Libs
  bossLib preamble

Definition registered_case10173_fs_weighted_rows_abs_upper_body_def:
  registered_case10173_fs_weighted_rows_abs_upper_body =
    If (Uop Ispair (Var «weights»))
      (If (Uop Ispair (Var «row_lists»))
        (App «candle_cv_fs_raw_add»
          [App «candle_cv_fs_raw_mul»
            [Uop Fst (Var «weights»);
             App «candle_cv_fs_dot_abs_upper»
               [Var «radii»;Uop Fst (Var «row_lists»)]];
           App «candle_cv_fs_weighted_rows_abs_upper»
             [Var «radii»;Uop Snd (Var «weights»);
              Uop Snd (Var «row_lists»)]])
        (App «candle_cv_fs_zero» []))
      (App «candle_cv_fs_zero» [])
End

Theorem registered_case10173_fs_weighted_rows_abs_upper_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_weighted_rows_abs_upper» =
    SOME
      ([«radii»;«weights»;«row_lists»],
       registered_case10173_fs_weighted_rows_abs_upper_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_compute_eval_literal_app3:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME ([first_name;second_name;third_name],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv first_argument;from_cv second_argument;
         from_cv third_argument]) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(first_name,from_cv first_argument);
         (second_name,from_cv second_argument);
         (third_name,from_cv third_argument)] body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_fs_weighted_rows_abs_upper_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_weighted_rows_abs_upper»
        [from_cv encoded_radii;from_cv encoded_weights;
         from_cv encoded_row_lists])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv encoded_radii);
         («weights»,from_cv encoded_weights);
         («row_lists»,from_cv encoded_row_lists)]
        registered_case10173_fs_weighted_rows_abs_upper_body) refs
Proof
  strip_tac
  >> irule registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_weighted_rows_abs_upper_lookup]
QED

Theorem registered_case10173_fs_weighted_rows_abs_upper_object_eval:
  !weights rows clock refs result.
    bounded_object_fs_weighted_rows_abs_upper
        radii weights rows = SOME result /\
    16 * (LENGTH radii + LENGTH weights + 2) < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_weighted_rows_abs_upper»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           from_cv (registered_case10173_word64_object_cv_list weights);
           from_cv (bounded_interval64_object_cv_matrix rows)])
        (refs:hol_refs) =
      (M_success (from_cv result),refs)
Proof
  Induct_on `weights`
  >- (rw
        [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_weighted_rows_abs_upper_def,
         registered_case10173_word64_object_cv_list_def]
      >> simp
           [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`encoded_weights` |-> `(Num 0:cv)`,
                 `encoded_radii` |->
                   `registered_case10173_word64_object_cv_list radii`,
                 `encoded_row_lists` |->
                   `bounded_interval64_object_cv_matrix rows`]
                registered_case10173_fs_weighted_rows_abs_upper_unfold)),
            registered_case10173_fs_weighted_rows_abs_upper_body_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_num,
            registered_case10173_fs_zero_eval]
      >> simp [compute_execTheory.from_cv_def])
  >> Cases_on `rows`
  >- (rw
        [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_weighted_rows_abs_upper_def,
         registered_case10173_word64_object_cv_list_def,
         compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def]
      >> rw
           [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`encoded_radii` |->
                   `registered_case10173_word64_object_cv_list radii`,
                 `encoded_weights` |->
                   `Pair
                     (bounded_signed64_object_cv (BoundedSigned64 F h))
                     (registered_case10173_word64_object_cv_list weights)`,
                 `encoded_row_lists` |-> `(Num 0:cv)`]
                registered_case10173_fs_weighted_rows_abs_upper_unfold))]
      >> simp
           [registered_case10173_fs_weighted_rows_abs_upper_body_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components,
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_num,
            registered_case10173_fs_zero_eval])
  >> rw
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_weighted_rows_abs_upper_def,
        registered_case10173_word64_object_cv_list_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def]
  >> Cases_on `bounded_object_fs_dot_abs_upper radii h`
  >> gvs []
  >> Cases_on `bounded_object_fs_raw_mul (bounded_word64_object_cv h') x`
  >> gvs []
  >> Cases_on
       `bounded_object_fs_weighted_rows_abs_upper radii weights t`
  >> gvs []
  >> Cases_on `bounded_object_fs_raw_add x' x''`
  >> gvs []
  >> rw
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`encoded_radii` |->
               `registered_case10173_word64_object_cv_list radii`,
             `encoded_weights` |->
               `Pair
                 (bounded_signed64_object_cv (BoundedSigned64 F h'))
                 (registered_case10173_word64_object_cv_list weights)`,
             `encoded_row_lists` |->
               `Pair (bounded_interval64_object_cv_list h)
                 (bounded_interval64_object_cv_matrix t)`]
            registered_case10173_fs_weighted_rows_abs_upper_unfold))]
  >> simp
       [registered_case10173_fs_weighted_rows_abs_upper_body_def,
        compute_evalTheory.subst_def,
        compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_dot_abs_upper»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           Uop Fst
             (Pair (from_cv (bounded_interval64_object_cv_list h))
               (from_cv (bounded_interval64_object_cv_matrix t)))]) refs =
      (M_success (from_cv x),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_dot_abs_upper»
             [from_cv (registered_case10173_word64_object_cv_list radii);
              Uop Fst
                (Pair (from_cv (bounded_interval64_object_cv_list h))
                  (from_cv (bounded_interval64_object_cv_matrix t)))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_dot_abs_upper»
             [from_cv (registered_case10173_word64_object_cv_list radii);
              from_cv (bounded_interval64_object_cv_list h)]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_execProofTheory.compute_eval_from_cv,
                 compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> `8 * (LENGTH radii + 1) < clock - 1` by intLib.ARITH_TAC
        >> fs [registered_case10173_fs_dot_abs_upper_object_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_mul»
          [Uop Fst
            (Pair (from_cv (bounded_word64_object_cv h'))
              (from_cv
                (registered_case10173_word64_object_cv_list weights)));
           App «candle_cv_fs_dot_abs_upper»
             [from_cv (registered_case10173_word64_object_cv_list radii);
              Uop Fst
                (Pair (from_cv (bounded_interval64_object_cv_list h))
                  (from_cv (bounded_interval64_object_cv_matrix t)))]]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_mul»
             [Uop Fst
               (Pair (from_cv (bounded_word64_object_cv h'))
                 (from_cv
                   (registered_case10173_word64_object_cv_list weights)));
              App «candle_cv_fs_dot_abs_upper»
                [from_cv (registered_case10173_word64_object_cv_list radii);
                 Uop Fst
                   (Pair (from_cv (bounded_interval64_object_cv_list h))
                     (from_cv
                       (bounded_interval64_object_cv_matrix t)))]]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_mul»
             [from_cv (bounded_word64_object_cv h');from_cv x]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> conj_tac
           >- simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
           >> fs [])
        >> fs
             [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_mul_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_weighted_rows_abs_upper»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           Uop Snd
             (Pair (from_cv (bounded_word64_object_cv h'))
               (from_cv
                 (registered_case10173_word64_object_cv_list weights)));
           Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv_list h))
               (from_cv (bounded_interval64_object_cv_matrix t)))]) refs =
      (M_success (from_cv x''),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_weighted_rows_abs_upper»
             [from_cv (registered_case10173_word64_object_cv_list radii);
              Uop Snd
                (Pair (from_cv (bounded_word64_object_cv h'))
                  (from_cv
                    (registered_case10173_word64_object_cv_list weights)));
              Uop Snd
                (Pair (from_cv (bounded_interval64_object_cv_list h))
                  (from_cv (bounded_interval64_object_cv_matrix t)))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_weighted_rows_abs_upper»
             [from_cv (registered_case10173_word64_object_cv_list radii);
              from_cv
                (registered_case10173_word64_object_cv_list weights);
              from_cv (bounded_interval64_object_cv_matrix t)]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_execProofTheory.compute_eval_from_cv,
                 compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> qpat_x_assum `!rows clock refs result. _`
             (qspecl_then [`t`,`clock - 1`,`refs`,`x''`] mp_tac)
        >> simp [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_add»
          [App «candle_cv_fs_raw_mul»
            [Uop Fst
              (Pair (from_cv (bounded_word64_object_cv h'))
                (from_cv
                  (registered_case10173_word64_object_cv_list weights)));
             App «candle_cv_fs_dot_abs_upper»
               [from_cv
                  (registered_case10173_word64_object_cv_list radii);
                Uop Fst
                  (Pair (from_cv (bounded_interval64_object_cv_list h))
                    (from_cv (bounded_interval64_object_cv_matrix t)))]];
           App «candle_cv_fs_weighted_rows_abs_upper»
             [from_cv (registered_case10173_word64_object_cv_list radii);
              Uop Snd
                (Pair (from_cv (bounded_word64_object_cv h'))
                  (from_cv
                    (registered_case10173_word64_object_cv_list weights)));
              Uop Snd
                (Pair (from_cv (bounded_interval64_object_cv_list h))
                  (from_cv (bounded_interval64_object_cv_matrix t)))]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_add» [from_cv x';from_cv x'']) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> fs []
        >> intLib.ARITH_TAC)
  >> fs
       [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_add_eval]
QED

val _ = export_theory ();
