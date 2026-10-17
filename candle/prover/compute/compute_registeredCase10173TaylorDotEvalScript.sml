(*****************************************************************************
 * Registered evaluator refinement for fixed-scale Taylor dot bounds.
 *
 * The historical source multiplies every radius by the absolute upper bound
 * of its interval entry and accumulates raw signed pairs.  This theorem ties
 * that literal recursion to the bounded-object dot implementation.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorDotEval
Ancestors
  compute_registeredCase10173TaylorIntervalEval
Libs
  bossLib preamble

Definition registered_case10173_word64_object_cv_list_def:
  registered_case10173_word64_object_cv_list ([]:word64 list) =
      (Num 0 : cv) /\
  registered_case10173_word64_object_cv_list (value::values) =
    Pair (bounded_word64_object_cv value)
      (registered_case10173_word64_object_cv_list values)
End

Definition registered_case10173_fs_dot_abs_upper_body_def:
  registered_case10173_fs_dot_abs_upper_body =
    If (Uop Ispair (Var «xs»))
      (If (Uop Ispair (Var «ys»))
        (App «candle_cv_fs_raw_add»
          [App «candle_cv_fs_raw_mul»
            [Uop Fst (Var «xs»);
             App «candle_cv_fs_interval_abs_upper»
               [Uop Fst (Var «ys»)]];
           App «candle_cv_fs_dot_abs_upper»
             [Uop Snd (Var «xs»);Uop Snd (Var «ys»)]])
        (App «candle_cv_fs_zero» []))
      (App «candle_cv_fs_zero» [])
End

Theorem registered_case10173_fs_dot_abs_upper_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_dot_abs_upper» =
    SOME ([«xs»;«ys»],registered_case10173_fs_dot_abs_upper_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_zero_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_zero» []) (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 0) (Num 0))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_zero_lookup,
        compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_zero_body_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_dot_abs_upper_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_dot_abs_upper» [from_cv xs;from_cv ys])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«xs»,from_cv xs);(«ys»,from_cv ys)]
        registered_case10173_fs_dot_abs_upper_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_dot_abs_upper_lookup]
QED

Theorem registered_case10173_fs_dot_abs_upper_object_eval:
  !radii entries clock refs result.
    bounded_object_fs_dot_abs_upper radii entries = SOME result /\
    8 * (LENGTH radii + 1) < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_dot_abs_upper»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           from_cv (bounded_interval64_object_cv_list entries)])
        (refs:hol_refs) =
      (M_success (from_cv result),refs)
Proof
  Induct_on `radii`
  >- (rw
        [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_dot_abs_upper_def,
         registered_case10173_word64_object_cv_list_def]
      >> simp
           [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`xs` |-> `(Num 0:cv)`,
                 `ys` |-> `bounded_interval64_object_cv_list entries`]
                registered_case10173_fs_dot_abs_upper_unfold)),
            registered_case10173_fs_dot_abs_upper_body_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_num,
            registered_case10173_fs_zero_eval]
      >> simp [compute_execTheory.from_cv_def])
  >> Cases_on `entries`
  >- (rw
        [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_dot_abs_upper_def,
         registered_case10173_word64_object_cv_list_def,
         compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
      >> rw
           [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`xs` |->
                   `Pair
                     (bounded_signed64_object_cv (BoundedSigned64 F h))
                     (registered_case10173_word64_object_cv_list radii)`,
                 `ys` |-> `(Num 0:cv)`]
                registered_case10173_fs_dot_abs_upper_unfold))]
      >> simp
           [registered_case10173_fs_dot_abs_upper_body_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components,
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_num,
            registered_case10173_fs_zero_eval])
  >> rw
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_dot_abs_upper_def,
        registered_case10173_word64_object_cv_list_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> `bounded_object_fs_interval_abs_upper
        (bounded_interval64_object_cv h) =
      SOME
        (bounded_word64_object_cv
          (bounded_interval64_abs_upper h))` by
       simp
         [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_interval_abs_upper_exact]
  >> gvs []
  >> Cases_on
       `bounded_object_fs_raw_mul
          (bounded_word64_object_cv h')
          (bounded_word64_object_cv
            (bounded_interval64_abs_upper h))`
  >> gvs []
  >> Cases_on `bounded_object_fs_dot_abs_upper radii t`
  >> gvs []
  >> Cases_on `bounded_object_fs_raw_add x x'`
  >> gvs []
  >> rw
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`xs` |->
               `Pair
                 (bounded_signed64_object_cv (BoundedSigned64 F h'))
                 (registered_case10173_word64_object_cv_list radii)`,
             `ys` |->
               `Pair (bounded_interval64_object_cv h)
                 (bounded_interval64_object_cv_list t)`]
            registered_case10173_fs_dot_abs_upper_unfold))]
  >> simp
       [registered_case10173_fs_dot_abs_upper_body_def,
        compute_evalTheory.subst_def,
        compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_abs_upper»
          [Uop Fst
            (Pair (from_cv (bounded_interval64_object_cv h))
              (from_cv (bounded_interval64_object_cv_list t)))]) refs =
      (M_success
        (from_cv
          (bounded_word64_object_cv
            (bounded_interval64_abs_upper h))),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_interval_abs_upper»
             [Uop Fst
               (Pair (from_cv (bounded_interval64_object_cv h))
                 (from_cv (bounded_interval64_object_cv_list t)))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_interval_abs_upper»
             [from_cv (bounded_interval64_object_cv h)]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> fs [registered_case10173_fs_interval_abs_upper_object_cv_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_mul»
          [Uop Fst
            (Pair (from_cv (bounded_word64_object_cv h'))
              (from_cv
                (registered_case10173_word64_object_cv_list radii)));
           App «candle_cv_fs_interval_abs_upper»
            [Uop Fst
              (Pair (from_cv (bounded_interval64_object_cv h))
                (from_cv (bounded_interval64_object_cv_list t)))]]) refs =
      (M_success (from_cv x),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_mul»
             [Uop Fst
               (Pair (from_cv (bounded_word64_object_cv h'))
                 (from_cv
                   (registered_case10173_word64_object_cv_list radii)));
              App «candle_cv_fs_interval_abs_upper»
               [Uop Fst
                 (Pair (from_cv (bounded_interval64_object_cv h))
                   (from_cv (bounded_interval64_object_cv_list t)))]]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_mul»
             [from_cv (bounded_word64_object_cv h');
              from_cv
                (bounded_word64_object_cv
                  (bounded_interval64_abs_upper h))]) refs` by
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
        (App «candle_cv_fs_dot_abs_upper»
          [Uop Snd
            (Pair (from_cv (bounded_word64_object_cv h'))
              (from_cv
                (registered_case10173_word64_object_cv_list radii)));
           Uop Snd
            (Pair (from_cv (bounded_interval64_object_cv h))
              (from_cv (bounded_interval64_object_cv_list t)))]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_dot_abs_upper»
             [Uop Snd
               (Pair (from_cv (bounded_word64_object_cv h'))
                 (from_cv
                   (registered_case10173_word64_object_cv_list radii)));
              Uop Snd
               (Pair (from_cv (bounded_interval64_object_cv h))
                 (from_cv (bounded_interval64_object_cv_list t)))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_dot_abs_upper»
             [from_cv
                (registered_case10173_word64_object_cv_list radii);
              from_cv (bounded_interval64_object_cv_list t)]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> qpat_x_assum `!entries clock refs result. _`
             (qspecl_then [`t`,`clock - 1`,`refs`,`x'`] mp_tac)
        >> simp [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_add»
          [App «candle_cv_fs_raw_mul»
            [Uop Fst
              (Pair (from_cv (bounded_word64_object_cv h'))
                (from_cv
                  (registered_case10173_word64_object_cv_list radii)));
             App «candle_cv_fs_interval_abs_upper»
              [Uop Fst
                (Pair (from_cv (bounded_interval64_object_cv h))
                  (from_cv (bounded_interval64_object_cv_list t)))]];
           App «candle_cv_fs_dot_abs_upper»
            [Uop Snd
              (Pair (from_cv (bounded_word64_object_cv h'))
                (from_cv
                  (registered_case10173_word64_object_cv_list radii)));
             Uop Snd
              (Pair (from_cv (bounded_interval64_object_cv h))
                (from_cv (bounded_interval64_object_cv_list t)))]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_add» [from_cv x;from_cv x']) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> fs []
        >> intLib.ARITH_TAC)
  >> fs
       [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_add_eval]
QED

val _ = export_theory ();
