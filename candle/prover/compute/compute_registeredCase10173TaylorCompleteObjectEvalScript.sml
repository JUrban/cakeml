(*****************************************************************************
 * Object refinement for the registered fixed-scale Taylor completion.
 *
 * The historical source projects value and gradient fields through accessor
 * calls. Positive-clock evaluator equivalence connects those projections to
 * the direct object encodings proved by the value and gradient refinements.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorCompleteObjectEval
Ancestors
  compute_registeredCase10173TaylorValueEval
Libs
  bossLib preamble

Definition registered_case10173_positive_eval_equiv_def:
  registered_case10173_positive_eval_equiv left right <=>
    !clock refs.
      0 < clock ==>
      compute_eval clock registered_case10173_historical_chunk16_ceqs
          left refs =
        compute_eval clock registered_case10173_historical_chunk16_ceqs
          right refs
End

Theorem registered_case10173_positive_eval_equiv_refl:
  registered_case10173_positive_eval_equiv expression expression
Proof
  simp [registered_case10173_positive_eval_equiv_def]
QED

Theorem registered_case10173_positive_eval_equiv_uop:
  registered_case10173_positive_eval_equiv argument normalized ==>
  registered_case10173_positive_eval_equiv
    (Uop operator argument) (Uop operator normalized)
Proof
  rw [registered_case10173_positive_eval_equiv_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_uop_argument_cong
  >> simp []
QED

Theorem registered_case10173_positive_eval_equiv_pair:
  registered_case10173_positive_eval_equiv left normalized_left /\
  registered_case10173_positive_eval_equiv right normalized_right ==>
  registered_case10173_positive_eval_equiv
    (Pair left right) (Pair normalized_left normalized_right)
Proof
  rw [registered_case10173_positive_eval_equiv_def]
  >> simp_tac std_ss
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def]
  >> fs [registered_case10173_positive_eval_equiv_def]
QED

Theorem registered_case10173_positive_eval_equiv_app1:
  registered_case10173_positive_eval_equiv argument normalized ==>
  registered_case10173_positive_eval_equiv
    (App function_name [argument]) (App function_name [normalized])
Proof
  rw [registered_case10173_positive_eval_equiv_def]
  >> Cases_on `clock`
  >> simp_tac std_ss
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def]
  >> fs [registered_case10173_positive_eval_equiv_def]
QED

Theorem registered_case10173_positive_eval_equiv_app2:
  registered_case10173_positive_eval_equiv argument1 normalized1 /\
  registered_case10173_positive_eval_equiv argument2 normalized2 ==>
  registered_case10173_positive_eval_equiv
    (App function_name [argument1;argument2])
    (App function_name [normalized1;normalized2])
Proof
  rw [registered_case10173_positive_eval_equiv_def]
  >> Cases_on `clock`
  >> simp_tac std_ss
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def]
  >> fs [registered_case10173_positive_eval_equiv_def]
QED

Theorem registered_case10173_positive_eval_equiv_app3:
  registered_case10173_positive_eval_equiv argument1 normalized1 /\
  registered_case10173_positive_eval_equiv argument2 normalized2 /\
  registered_case10173_positive_eval_equiv argument3 normalized3 ==>
  registered_case10173_positive_eval_equiv
    (App function_name [argument1;argument2;argument3])
    (App function_name [normalized1;normalized2;normalized3])
Proof
  rw [registered_case10173_positive_eval_equiv_def]
  >> Cases_on `clock`
  >> simp_tac std_ss
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def]
  >> fs [registered_case10173_positive_eval_equiv_def]
QED

Theorem registered_case10173_fs_first_value_positive_equiv:
  registered_case10173_positive_eval_equiv
    (App «candle_cv_fs_first_value»
      [from_cv (Pair value gradient)])
    (from_cv value)
Proof
  rw [registered_case10173_positive_eval_equiv_def]
  >> mp_tac
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`value` |-> `value`, `gradient` |-> `gradient`,
            `clock` |-> `clock`, `refs` |-> `refs`]
           compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_first_value_eval))
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem registered_case10173_fs_first_gradient_positive_equiv:
  registered_case10173_positive_eval_equiv
    (App «candle_cv_fs_first_gradient»
      [from_cv (Pair value gradient)])
    (from_cv gradient)
Proof
  rw [registered_case10173_positive_eval_equiv_def]
  >> mp_tac
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`value` |-> `value`, `gradient` |-> `gradient`,
            `clock` |-> `clock`, `refs` |-> `refs`]
           compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_first_gradient_eval))
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem registered_case10173_fs_taylor_error_exp_positive_cong:
  registered_case10173_positive_eval_equiv gradient normalized_gradient ==>
  registered_case10173_positive_eval_equiv
    (registered_case10173_fs_taylor_error_exp
      radii gradient hessian_rows)
    (registered_case10173_fs_taylor_error_exp
      radii normalized_gradient hessian_rows)
Proof
  rw [compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_taylor_error_exp_def]
  >> irule registered_case10173_positive_eval_equiv_app2
  >> conj_tac
  >- (irule registered_case10173_positive_eval_equiv_app2
      >> simp [registered_case10173_positive_eval_equiv_refl]
      >> irule registered_case10173_positive_eval_equiv_app2
      >> simp [registered_case10173_positive_eval_equiv_refl])
  >> simp [registered_case10173_positive_eval_equiv_refl]
QED

Theorem registered_case10173_fs_taylor_value_exp_positive_cong:
  registered_case10173_positive_eval_equiv
      center_value normalized_center_value /\
  registered_case10173_positive_eval_equiv
      center_gradient normalized_center_gradient ==>
  registered_case10173_positive_eval_equiv
    (registered_case10173_fs_taylor_value_exp
      radii center_value center_gradient hessian_rows)
    (registered_case10173_fs_taylor_value_exp
      radii normalized_center_value normalized_center_gradient
      hessian_rows)
Proof
  rw
    [compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_taylor_value_exp_def,
     compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_value_raw_interval_exp_def,
     compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_value_center_interval_exp_def,
     compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_value_error_interval_exp_def]
  >> irule registered_case10173_positive_eval_equiv_app2
  >> conj_tac
  >- simp [registered_case10173_positive_eval_equiv_refl]
  >> irule registered_case10173_positive_eval_equiv_app2
  >> conj_tac
  >- (irule registered_case10173_positive_eval_equiv_pair
      >> conj_tac
      >> irule registered_case10173_positive_eval_equiv_app2
      >> simp
           [registered_case10173_positive_eval_equiv_refl,
            registered_case10173_positive_eval_equiv_uop])
  >> irule registered_case10173_positive_eval_equiv_pair
  >> conj_tac
  >- (irule registered_case10173_positive_eval_equiv_app1
      >> irule registered_case10173_fs_taylor_error_exp_positive_cong
      >> simp [])
  >> irule registered_case10173_fs_taylor_error_exp_positive_cong
  >> simp []
QED

Theorem registered_case10173_fs_complete_value_bound_exp_as_taylor_value:
  registered_case10173_fs_complete_value_bound_exp radii center hessian =
  registered_case10173_fs_taylor_value_exp
    radii
    (App «candle_cv_fs_first_value» [center])
    (App «candle_cv_fs_first_gradient» [center])
    hessian
Proof
  simp
    [compute_registeredCase10173TaylorCompletionEvalTheory.registered_case10173_fs_complete_value_bound_exp_def,
     compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_taylor_value_exp_def,
     compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_value_raw_interval_exp_def,
     compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_value_center_interval_exp_def,
     compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_value_error_interval_exp_def,
     compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_taylor_error_exp_def,
     compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_two_scale_exp_def]
QED

Theorem registered_case10173_fs_complete_value_bound_object_eval:
  bounded_object_fs_taylor_value_complete
      radii center_value center_gradient rows = SOME result /\
  128 * (2 * LENGTH radii + LENGTH rows + 2) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (registered_case10173_fs_complete_value_bound_exp
        (from_cv (registered_case10173_word64_object_cv_list radii))
        (from_cv
          (Pair (bounded_interval64_object_cv center_value)
            (bounded_interval64_object_cv_list center_gradient)))
        (from_cv (bounded_interval64_object_cv_matrix rows)))
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_taylor_value_exp
          (from_cv
            (registered_case10173_word64_object_cv_list radii))
          (from_cv (bounded_interval64_object_cv center_value))
          (from_cv
            (bounded_interval64_object_cv_list center_gradient))
          (from_cv
            (bounded_interval64_object_cv_matrix rows))) refs =
      (M_success (from_cv result),refs)` by
       (irule
          compute_registeredCase10173TaylorValueEvalTheory.registered_case10173_fs_taylor_value_object_eval
        >> simp [])
  >> `registered_case10173_positive_eval_equiv
        (registered_case10173_fs_complete_value_bound_exp
          (from_cv
            (registered_case10173_word64_object_cv_list radii))
          (from_cv
            (Pair (bounded_interval64_object_cv center_value)
              (bounded_interval64_object_cv_list center_gradient)))
          (from_cv
            (bounded_interval64_object_cv_matrix rows)))
        (registered_case10173_fs_taylor_value_exp
          (from_cv
            (registered_case10173_word64_object_cv_list radii))
          (from_cv (bounded_interval64_object_cv center_value))
          (from_cv
            (bounded_interval64_object_cv_list center_gradient))
          (from_cv
            (bounded_interval64_object_cv_matrix rows)))` by
       (rw
          [registered_case10173_fs_complete_value_bound_exp_as_taylor_value]
        >> irule registered_case10173_fs_taylor_value_exp_positive_cong
        >> conj_tac
        >> (FIRST
             [irule
                (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                  registered_case10173_fs_first_value_positive_equiv),
              irule
                (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                  registered_case10173_fs_first_gradient_positive_equiv)]))
  >> fs [registered_case10173_positive_eval_equiv_def]
QED

Theorem registered_case10173_fs_complete_gradient_bounds_positive_equiv:
  registered_case10173_positive_eval_equiv
    (registered_case10173_fs_complete_gradient_bounds_exp
      radii (from_cv (Pair center_value center_gradient)) hessian)
    (App «candle_cv_fs_gradient_bounds»
      [radii;from_cv center_gradient;hessian])
Proof
  rw
    [compute_registeredCase10173TaylorCompletionEvalTheory.registered_case10173_fs_complete_gradient_bounds_exp_def]
  >> irule registered_case10173_positive_eval_equiv_app3
  >> conj_tac
  >- simp [registered_case10173_positive_eval_equiv_refl]
  >> conj_tac
  >- irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_first_gradient_positive_equiv)
  >> simp [registered_case10173_positive_eval_equiv_refl]
QED

Theorem registered_case10173_fs_complete_gradient_bounds_object_eval:
  bounded_object_fs_gradient_rows
      radii center_gradient rows = SOME result /\
  128 * (LENGTH radii + LENGTH center_gradient + 2) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (registered_case10173_fs_complete_gradient_bounds_exp
        (from_cv (registered_case10173_word64_object_cv_list radii))
        (from_cv
          (Pair (bounded_interval64_object_cv center_value)
            (bounded_interval64_object_cv_list center_gradient)))
        (from_cv (bounded_interval64_object_cv_matrix rows)))
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_gradient_bounds»
          [from_cv
             (registered_case10173_word64_object_cv_list radii);
           from_cv
             (bounded_interval64_object_cv_list center_gradient);
           from_cv
             (bounded_interval64_object_cv_matrix rows)]) refs =
      (M_success (from_cv result),refs)` by
       (irule
          compute_registeredCase10173TaylorGradientRowsEvalTheory.registered_case10173_fs_gradient_bounds_object_eval
        >> simp [])
  >> `registered_case10173_positive_eval_equiv
        (registered_case10173_fs_complete_gradient_bounds_exp
          (from_cv
            (registered_case10173_word64_object_cv_list radii))
          (from_cv
            (Pair (bounded_interval64_object_cv center_value)
              (bounded_interval64_object_cv_list center_gradient)))
          (from_cv
            (bounded_interval64_object_cv_matrix rows)))
        (App «candle_cv_fs_gradient_bounds»
          [from_cv
             (registered_case10173_word64_object_cv_list radii);
           from_cv
             (bounded_interval64_object_cv_list center_gradient);
           from_cv
             (bounded_interval64_object_cv_matrix rows)])` by
      irule
         registered_case10173_fs_complete_gradient_bounds_positive_equiv
  >> fs [registered_case10173_positive_eval_equiv_def]
QED

Theorem registered_case10173_fs_result_complete_rounded_eval_from_component_results:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (registered_case10173_fs_complete_value_bound_exp
        (from_cv radii)
        (Pair (from_cv center_value) (from_cv center_gradient))
        (from_cv hessian))
      (refs:hol_refs) =
    (M_success (from_cv value_bound),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (registered_case10173_fs_complete_gradient_bounds_exp
        (from_cv radii)
        (Pair (from_cv center_value) (from_cv center_gradient))
        (from_cv hessian)) refs =
    (M_success (from_cv gradient_bounds),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_rounded»
        [from_cv radii;from_cv result_domain;
         Pair (from_cv center_value) (from_cv center_gradient);
         from_cv hessian]) refs =
    (M_success
      (Pair (from_cv result_domain)
        (Pair
          (Pair (from_cv center_value) (from_cv center_gradient))
          (Pair (from_cv value_bound)
            (Pair (from_cv gradient_bounds) (from_cv hessian))))),refs)
Proof
  ACCEPT_TAC
    (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
      (Q.INST
        [`center:cv` |-> `Pair center_value center_gradient`]
        compute_registeredCase10173TaylorCompletionEvalTheory.registered_case10173_fs_result_complete_rounded_eval_from_results))
QED

Theorem registered_case10173_fs_result_complete_rounded_object_eval:
  bounded_hessian64_rows hessian = SOME rows /\
  bounded_object_fs_taylor_complete
      radii result_domain center_value center_gradient hessian rows =
        SOME result /\
  256 *
      (2 * LENGTH radii + LENGTH rows +
       LENGTH center_gradient + 2) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_rounded»
        [from_cv
           (registered_case10173_word64_object_cv_list radii);
         from_cv (bounded_bool_object_cv result_domain);
         from_cv
           (Pair (bounded_interval64_object_cv center_value)
             (bounded_interval64_object_cv_list center_gradient));
         from_cv (bounded_interval64_object_cv_matrix rows)])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw
    [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_complete_def,
     compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_gradient_complete_def]
  >> Cases_on
       `bounded_object_fs_taylor_value_complete
          radii center_value center_gradient rows`
  >> gvs []
  >> Cases_on
       `bounded_object_fs_gradient_rows radii center_gradient rows`
  >> gvs []
  >> irule
       registered_case10173_fs_result_complete_rounded_eval_from_component_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >> (FIRST
       [(irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_complete_value_bound_object_eval)
         >> simp []
         >> intLib.ARITH_TAC),
        (irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_complete_gradient_bounds_object_eval)
         >> simp []
         >> intLib.ARITH_TAC)])
QED

val _ = export_theory ();
