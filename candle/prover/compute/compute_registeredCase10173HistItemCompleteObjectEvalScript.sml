(*****************************************************************************
 * Object completion for one registered historical item.
 *
 * The specialized first- and second-order evaluators deliver the center jet
 * and the expanded Hessian rows respectively.  This theorem composes those
 * two numerical results with the already proved radius projection, Taylor
 * completion, and fixed-item wrapper.  It removes final completion as an
 * independent premise of the historical-item refinement.
 *****************************************************************************)
Theory compute_registeredCase10173HistItemCompleteObjectEval
Ancestors
  compute_registeredCase10173TaylorCompleteObjectEval
  compute_registeredCase10173RadiiEval
Libs
  bossLib preamble

Theorem registered_case10173_hist_item_complete_object_eval:
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME center_environment /\
  bounded_object_positive_q_interval64_decimal_list boxes =
      SOME box_environment /\
  registered_case10173_q_numerator_cv_list encoded_radii =
      registered_case10173_word64_object_cv_list radii /\
  bounded_hessian64_rows hessian = SOME rows /\
  bounded_object_fs_taylor_complete
      radii T center_value center_gradient hessian rows = SOME result /\
  8 < clock /\
  11 * (LENGTH center_environment + 1) < clock - 1 /\
  11 * (LENGTH box_environment + 1) < clock - 2 /\
  LENGTH encoded_radii + 1 < clock - 5 /\
  256 *
      (2 * LENGTH radii + LENGTH rows +
       LENGTH center_gradient + 2) < clock - 5 /\
  compute_eval (clock - 3)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_first_order»
        [from_cv (bounded_interval64_object_cv_list center_environment);
         from_cv root0;from_cv root1]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (bounded_interval64_object_cv center_value)
            (bounded_interval64_object_cv_list center_gradient))),refs) /\
  compute_eval (clock - 4)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_order»
        [from_cv (bounded_interval64_object_cv_list box_environment);
         from_cv root2;from_cv root3]) refs =
      (M_success
        (from_cv
          (Pair (bounded_interval64_object_cv box_second_value)
            (Pair (bounded_interval64_object_cv_list box_second_gradient)
              (bounded_interval64_object_cv_matrix rows)))),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_item»
        [from_cv center_boxes;from_cv boxes;
         from_cv (registered_case10173_q_cv_list encoded_radii);
         from_cv
           (Pair (root0:cv)
             (Pair (root1:cv)
               (Pair (root2:cv)
                 (Pair (root3:cv) (roots_tail:cv)))) : cv)]) refs =
    (M_success (from_cv (Pair (Num 1) result)),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistItemObjectEvalTheory.registered_case10173_hist_item_object_eval_from_results
  >> conj_tac >- simp []
  >> qexists_tac `box_environment`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv box_second_value)
          (Pair (bounded_interval64_object_cv_list box_second_gradient)
            (bounded_interval64_object_cv_matrix rows))`
  >> qexists_tac `center_environment`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv center_value)
          (bounded_interval64_object_cv_list center_gradient)`
  >> simp []
  >> irule
       (let
          val th0 =
            SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_hist_completion_eval_from_results
          val th1 = Q.INST [`clock` |-> `clock - 5`] th0
          val th2 = Q.INST
            [`radii:cv` |->
              `registered_case10173_q_cv_list encoded_radii`] th1
          val th3 = Q.INST
            [`fixed_radii:cv` |->
              `registered_case10173_word64_object_cv_list radii`] th2
          val th4 = Q.INST
            [`center_first:cv` |->
              `Pair (bounded_interval64_object_cv center_value)
                (bounded_interval64_object_cv_list center_gradient)`] th3
          val th5 = Q.INST
            [`box_value:cv` |->
              `bounded_interval64_object_cv box_second_value`] th4
          val th6 = Q.INST
            [`box_gradient:cv` |->
              `bounded_interval64_object_cv_list box_second_gradient`] th5
          val th7 = Q.INST
            [`box_hessian:cv` |->
              `bounded_interval64_object_cv_matrix rows`] th6
        in
          SIMP_RULE std_ss [compute_execTheory.from_cv_def] th7
        end)
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fs_hist_second_hessian_eval)
      >> intLib.ARITH_TAC)
  >> qexists_tac `radii`
  >> conj_tac
  >- (`compute_eval (clock - 5)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_list_of_q»
            [from_cv
              (registered_case10173_q_cv_list encoded_radii)]) refs =
        (M_success
          (from_cv
            (registered_case10173_q_numerator_cv_list
              encoded_radii)),refs)` by
       (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_registeredCase10173RadiiEvalTheory.registered_case10173_fs_list_of_q_projection_eval)
        >> simp [])
      >> fs [])
  >> irule
       (SIMP_RULE std_ss
         [compute_execTheory.from_cv_def,
          compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def]
         (Q.INST [`result_domain` |-> `T`]
           compute_registeredCase10173TaylorCompleteObjectEvalTheory.registered_case10173_fs_result_complete_rounded_object_eval))
  >> conj_tac >- simp []
  >> qexists_tac `hessian`
  >> simp []
QED

val _ = export_theory ();
