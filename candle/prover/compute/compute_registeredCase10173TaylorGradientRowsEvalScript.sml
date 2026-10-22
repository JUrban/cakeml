(*****************************************************************************
 * Registered evaluator refinement for recursive fixed-scale gradient bounds.
 *
 * This lifts the proved single-row calculation over the paired gradient and
 * Hessian-row lists used by the historical source checker.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorGradientRowsEval
Ancestors
  compute_registeredCase10173TaylorGradientEval
Libs
  bossLib preamble

Definition registered_case10173_fs_gradient_bounds_body_def:
  registered_case10173_fs_gradient_bounds_body =
    If (Uop Ispair (Var «gradients»))
      (If (Uop Ispair (Var «row_lists»))
        (Pair
          (registered_case10173_fs_gradient_row_exp
            (Var «radii»)
            (Uop Fst (Var «gradients»))
            (Uop Fst (Var «row_lists»)))
          (App «candle_cv_fs_gradient_bounds»
            [Var «radii»;Uop Snd (Var «gradients»);
             Uop Snd (Var «row_lists»)]))
        (Num 0))
      (Num 0)
End

Theorem registered_case10173_fs_gradient_bounds_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_gradient_bounds» =
    SOME
      ([«radii»;«gradients»;«row_lists»],
       registered_case10173_fs_gradient_bounds_body)
Proof
  rw
    [registered_case10173_fs_gradient_bounds_body_def,
     compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_row_exp_def,
     compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_raw_interval_exp_def,
     compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_center_interval_exp_def,
     compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_variation_interval_exp_def]
  >> EVAL_TAC
QED

Theorem registered_case10173_fs_gradient_bounds_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_gradient_bounds»
        [from_cv encoded_radii;from_cv encoded_gradients;
         from_cv encoded_row_lists])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv encoded_radii);
         («gradients»,from_cv encoded_gradients);
         («row_lists»,from_cv encoded_row_lists)]
        registered_case10173_fs_gradient_bounds_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_gradient_bounds_lookup]
QED

Definition registered_case10173_eval_equiv_def:
  registered_case10173_eval_equiv left right <=>
    !clock refs.
      compute_eval clock registered_case10173_historical_chunk16_ceqs
          left refs =
        compute_eval clock registered_case10173_historical_chunk16_ceqs
          right refs
End

Theorem registered_case10173_eval_equiv_refl:
  registered_case10173_eval_equiv expression expression
Proof
  simp [registered_case10173_eval_equiv_def]
QED

Theorem registered_case10173_eval_equiv_uop:
  registered_case10173_eval_equiv argument normalized ==>
  registered_case10173_eval_equiv
    (Uop operator argument) (Uop operator normalized)
Proof
  rw [registered_case10173_eval_equiv_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_uop_argument_cong
  >> simp []
QED

Theorem registered_case10173_eval_equiv_pair:
  registered_case10173_eval_equiv left normalized_left /\
  registered_case10173_eval_equiv right normalized_right ==>
  registered_case10173_eval_equiv
    (Pair left right) (Pair normalized_left normalized_right)
Proof
  rw [registered_case10173_eval_equiv_def]
  >> simp_tac std_ss
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def]
  >> fs [registered_case10173_eval_equiv_def]
QED

Theorem registered_case10173_eval_equiv_app1:
  registered_case10173_eval_equiv argument normalized ==>
  registered_case10173_eval_equiv
    (App function_name [argument]) (App function_name [normalized])
Proof
  rw [registered_case10173_eval_equiv_def]
  >> Cases_on `clock`
  >> simp_tac std_ss
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def]
  >> fs [registered_case10173_eval_equiv_def]
QED

Theorem registered_case10173_eval_equiv_app2:
  registered_case10173_eval_equiv argument1 normalized1 /\
  registered_case10173_eval_equiv argument2 normalized2 ==>
  registered_case10173_eval_equiv
    (App function_name [argument1;argument2])
    (App function_name [normalized1;normalized2])
Proof
  rw [registered_case10173_eval_equiv_def]
  >> Cases_on `clock`
  >> simp_tac std_ss
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def]
  >> fs [registered_case10173_eval_equiv_def]
QED

Theorem registered_case10173_eval_equiv_fst_pair:
  registered_case10173_eval_equiv
    (Uop Fst (Pair (from_cv left) (from_cv right)))
    (from_cv left)
Proof
  simp
    [registered_case10173_eval_equiv_def,
     compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
     compute_execProofTheory.compute_eval_from_cv]
QED

Theorem registered_case10173_fs_gradient_row_exp_cong:
  registered_case10173_eval_equiv gradient normalized_gradient /\
  registered_case10173_eval_equiv row normalized_row ==>
  registered_case10173_eval_equiv
    (registered_case10173_fs_gradient_row_exp
      radii gradient row)
    (registered_case10173_fs_gradient_row_exp
      radii normalized_gradient normalized_row)
Proof
  rw
    [compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_row_exp_def,
     compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_raw_interval_exp_def,
     compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_center_interval_exp_def,
     compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_variation_interval_exp_def]
  >> irule registered_case10173_eval_equiv_app2
  >> conj_tac
  >- simp [registered_case10173_eval_equiv_refl]
  >> irule registered_case10173_eval_equiv_app2
  >> conj_tac
  >- (irule registered_case10173_eval_equiv_pair
      >> conj_tac
      >> irule registered_case10173_eval_equiv_app2
      >> simp
           [registered_case10173_eval_equiv_refl,
            registered_case10173_eval_equiv_uop])
  >> irule registered_case10173_eval_equiv_pair
  >> conj_tac
  >- (irule registered_case10173_eval_equiv_app1
      >> irule registered_case10173_eval_equiv_app2
      >> simp
           [registered_case10173_eval_equiv_refl])
  >> irule registered_case10173_eval_equiv_app2
  >> simp [registered_case10173_eval_equiv_refl]
QED

Theorem registered_case10173_fs_gradient_bounds_object_eval:
  !gradients rows clock refs result.
    bounded_object_fs_gradient_rows radii gradients rows = SOME result /\
    128 * (LENGTH radii + LENGTH gradients + 2) < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_gradient_bounds»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           from_cv (bounded_interval64_object_cv_list gradients);
           from_cv (bounded_interval64_object_cv_matrix rows)])
        (refs:hol_refs) =
      (M_success (from_cv result),refs)
Proof
  Induct_on `gradients`
  >- (rw
        [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_gradient_rows_def,
         compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
      >> simp
           [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`encoded_radii` |->
                   `registered_case10173_word64_object_cv_list radii`,
                 `encoded_gradients` |-> `(Num 0:cv)`,
                 `encoded_row_lists` |->
                   `bounded_interval64_object_cv_matrix rows`]
                registered_case10173_fs_gradient_bounds_unfold)),
            registered_case10173_fs_gradient_bounds_body_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_num]
      >> simp
           [compute_execTheory.from_cv_def,
            compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> Cases_on `rows`
  >- (rw
        [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_gradient_rows_def,
         compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
         compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def]
      >> rw
           [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`encoded_radii` |->
                   `registered_case10173_word64_object_cv_list radii`,
                 `encoded_gradients` |->
                   `Pair (bounded_interval64_object_cv h)
                     (bounded_interval64_object_cv_list gradients)`,
                `encoded_row_lists` |-> `(Num 0:cv)`]
                registered_case10173_fs_gradient_bounds_unfold))]
      >> simp
           [registered_case10173_fs_gradient_bounds_body_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components,
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_num]
      >> mp_tac
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`x` |-> `(Num 0:cv)`, `s` |-> `refs`,
                `ck` |-> `clock - 1`,
                `eqs` |-> `registered_case10173_historical_chunk16_ceqs`]
               (SPEC_ALL
                 compute_execProofTheory.compute_eval_from_cv)))
      >> simp [])
  >> rw
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_gradient_rows_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def]
  >> Cases_on `bounded_object_fs_gradient_row radii h' h`
  >> gvs []
  >> Cases_on
       `bounded_object_fs_gradient_rows radii gradients t`
  >> gvs []
  >> rw
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`encoded_radii` |->
               `registered_case10173_word64_object_cv_list radii`,
             `encoded_gradients` |->
               `Pair (bounded_interval64_object_cv h')
                 (bounded_interval64_object_cv_list gradients)`,
             `encoded_row_lists` |->
               `Pair (bounded_interval64_object_cv_list h)
                 (bounded_interval64_object_cv_matrix t)`]
            registered_case10173_fs_gradient_bounds_unfold))]
  >> simp
       [registered_case10173_fs_gradient_bounds_body_def,
        compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_row_exp_def,
        compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_raw_interval_exp_def,
        compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_center_interval_exp_def,
        compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_variation_interval_exp_def,
        compute_evalTheory.subst_def,
        compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_gradient_row_exp
          (from_cv (registered_case10173_word64_object_cv_list radii))
          (Uop Fst
            (Pair (from_cv (bounded_interval64_object_cv h'))
              (from_cv
                (bounded_interval64_object_cv_list gradients))))
          (Uop Fst
            (Pair (from_cv (bounded_interval64_object_cv_list h))
              (from_cv (bounded_interval64_object_cv_matrix t))))) refs =
      (M_success (from_cv x),refs)` by
       (`64 * (LENGTH radii + 2) < clock - 1` by intLib.ARITH_TAC
        >> `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (registered_case10173_fs_gradient_row_exp
                (from_cv
                  (registered_case10173_word64_object_cv_list radii))
                (from_cv (bounded_interval64_object_cv h'))
                (from_cv (bounded_interval64_object_cv_list h))) refs =
            (M_success (from_cv x),refs)` by
             (mp_tac
                (Q.INST
                  [`radii` |-> `radii`, `gradient` |-> `h'`,
                   `row` |-> `h`, `result` |-> `x`,
                   `clock` |-> `clock - 1`, `refs` |-> `refs`]
                  compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_row_object_eval)
              >> simp [])
        >> `registered_case10173_eval_equiv
              (registered_case10173_fs_gradient_row_exp
                (from_cv
                  (registered_case10173_word64_object_cv_list radii))
                (Uop Fst
                  (Pair (from_cv (bounded_interval64_object_cv h'))
                    (from_cv
                      (bounded_interval64_object_cv_list gradients))))
                (Uop Fst
                  (Pair
                    (from_cv (bounded_interval64_object_cv_list h))
                    (from_cv
                      (bounded_interval64_object_cv_matrix t)))))
              (registered_case10173_fs_gradient_row_exp
                (from_cv
                  (registered_case10173_word64_object_cv_list radii))
                (from_cv (bounded_interval64_object_cv h'))
                (from_cv (bounded_interval64_object_cv_list h)))` by
             (irule registered_case10173_fs_gradient_row_exp_cong
              >> simp [registered_case10173_eval_equiv_fst_pair])
        >> fs [registered_case10173_eval_equiv_def])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_gradient_bounds»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv h'))
               (from_cv
                 (bounded_interval64_object_cv_list gradients)));
           Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv_list h))
               (from_cv (bounded_interval64_object_cv_matrix t)))]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_gradient_bounds»
             [from_cv
                (registered_case10173_word64_object_cv_list radii);
              Uop Snd
                (Pair (from_cv (bounded_interval64_object_cv h'))
                  (from_cv
                    (bounded_interval64_object_cv_list gradients)));
              Uop Snd
                (Pair (from_cv (bounded_interval64_object_cv_list h))
                  (from_cv
                    (bounded_interval64_object_cv_matrix t)))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_gradient_bounds»
             [from_cv
                (registered_case10173_word64_object_cv_list radii);
              from_cv
                (bounded_interval64_object_cv_list gradients);
              from_cv (bounded_interval64_object_cv_matrix t)]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_execProofTheory.compute_eval_from_cv,
                 compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> qpat_x_assum `!rows clock refs result. _`
             (qspecl_then [`t`,`clock - 1`,`refs`,`x'`] mp_tac)
        >> simp [])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac
  >- fs
       [compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_row_exp_def,
        compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_raw_interval_exp_def,
        compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_center_interval_exp_def,
        compute_registeredCase10173TaylorGradientEvalTheory.registered_case10173_fs_gradient_variation_interval_exp_def]
  >> fs []
QED

val _ = export_theory ();
