(*****************************************************************************
 * Object-aligned registered evaluator seam for the historical item.
 *
 * This discharges the exact q-to-fixed environment conversions and the four
 * positional root lookups.  The remaining evaluator premises are therefore
 * the numerical first-order result, numerical second-order result, and final
 * item completion that the bounded object checker already records.
 *****************************************************************************)
Theory compute_registeredCase10173HistItemObjectEval
Ancestors
  compute_registeredCase10173HistItemEval
  compute_registeredCase10173QConversionEval
  compute_registeredCase10173RootInputsEval
Libs
  bossLib preamble

Theorem registered_case10173_fs_interval_lookup_four_0_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [from_cv (Num 0);
         from_cv
           (Pair (root0:cv)
             (Pair (root1:cv)
               (Pair (root2:cv) (Pair (root3:cv) (roots_tail:cv)))) : cv)])
      (refs:hol_refs) =
    (M_success (from_cv root0),refs)
Proof
  strip_tac
  >> irule registered_case10173_fs_interval_lookup_head_eval
  >> simp []
QED

Theorem registered_case10173_fs_interval_lookup_four_1_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [from_cv (Num (SUC 0));
         from_cv
           (Pair (root0:cv)
             (Pair (root1:cv)
               (Pair (root2:cv) (Pair (root3:cv) (roots_tail:cv)))) : cv)])
      (refs:hol_refs) =
    (M_success (from_cv root1),refs)
Proof
  strip_tac
  >> irule registered_case10173_fs_interval_lookup_tail_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> irule registered_case10173_fs_interval_lookup_head_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_interval_lookup_four_2_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [from_cv (Num (SUC (SUC 0)));
         from_cv
           (Pair (root0:cv)
             (Pair (root1:cv)
               (Pair (root2:cv) (Pair (root3:cv) (roots_tail:cv)))) : cv)])
      (refs:hol_refs) =
    (M_success (from_cv root2),refs)
Proof
  strip_tac
  >> irule registered_case10173_fs_interval_lookup_tail_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> irule registered_case10173_fs_interval_lookup_tail_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> irule registered_case10173_fs_interval_lookup_head_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_interval_lookup_four_3_eval:
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [from_cv (Num (SUC (SUC (SUC 0))));
         from_cv
           (Pair (root0:cv)
             (Pair (root1:cv)
               (Pair (root2:cv) (Pair (root3:cv) (roots_tail:cv)))) : cv)])
      (refs:hol_refs) =
    (M_success (from_cv root3),refs)
Proof
  strip_tac
  >> irule registered_case10173_fs_interval_lookup_tail_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> irule registered_case10173_fs_interval_lookup_tail_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> irule registered_case10173_fs_interval_lookup_tail_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> irule registered_case10173_fs_interval_lookup_head_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_first_order_four_root_args:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_first_order»
        [from_cv environment;
         App «candle_cv_fs_interval_lookup»
           [Num 0;
            from_cv
              (Pair (root0:cv)
                (Pair (root1:cv)
                  (Pair (root2:cv)
                    (Pair (root3:cv) (roots_tail:cv)))) : cv)];
         App «candle_cv_fs_interval_lookup»
           [Num 1;
            from_cv
              (Pair (root0:cv)
                (Pair (root1:cv)
                  (Pair (root2:cv)
                    (Pair (root3:cv) (roots_tail:cv)))) : cv)]])
      (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_first_order»
        [from_cv environment;from_cv root0;from_cv root1]) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
  >> simp [compute_execProofTheory.compute_eval_from_cv]
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_interval_lookup_four_0_eval)
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_interval_lookup_four_1_eval)
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_second_order_four_root_args:
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_order»
        [from_cv environment;
         App «candle_cv_fs_interval_lookup»
           [Num 2;
            from_cv
              (Pair (root0:cv)
                (Pair (root1:cv)
                  (Pair (root2:cv)
                    (Pair (root3:cv) (roots_tail:cv)))) : cv)];
         App «candle_cv_fs_interval_lookup»
           [Num 3;
            from_cv
              (Pair (root0:cv)
                (Pair (root1:cv)
                  (Pair (root2:cv)
                    (Pair (root3:cv) (roots_tail:cv)))) : cv)]])
      (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_order»
        [from_cv environment;from_cv root2;from_cv root3]) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
  >> simp [compute_execProofTheory.compute_eval_from_cv]
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_interval_lookup_four_2_eval)
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_interval_lookup_four_3_eval)
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_hist_item_object_eval_from_results:
  8 < clock /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME center_environment /\
  bounded_object_positive_q_interval64_decimal_list boxes =
      SOME box_environment /\
  11 * (LENGTH center_environment + 1) < clock - 1 /\
  11 * (LENGTH box_environment + 1) < clock - 2 /\
  compute_eval (clock - 3)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_first_order»
        [from_cv (bounded_interval64_object_cv_list center_environment);
         from_cv root0;from_cv root1]) (refs:hol_refs) =
      (M_success (from_cv center_first),refs) /\
  compute_eval (clock - 4)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_order»
        [from_cv (bounded_interval64_object_cv_list box_environment);
         from_cv root2;from_cv root3]) refs =
      (M_success (from_cv box_second),refs) /\
  compute_eval (clock - 5)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_fixed»
        [App «candle_cv_fs_result_complete_rounded»
          [App «candle_cv_fs_list_of_q» [from_cv radii];Num 1;
           from_cv center_first;
           App «candle_cv_fs_hist_second_hessian»
             [from_cv box_second]]]) refs =
      (M_success (from_cv item),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_item»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv
           (Pair (root0:cv)
             (Pair (root1:cv)
               (Pair (root2:cv) (Pair (root3:cv) (roots_tail:cv)))) : cv)]) refs =
    (M_success (from_cv item),refs)
Proof
  strip_tac
  >> irule registered_case10173_hist_item_eval_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv_list box_environment`
  >> qexists_tac `box_second`
  >> qexists_tac `bounded_interval64_object_cv_list center_environment`
  >> qexists_tac `center_first`
  >> conj_tac
  >- (irule registered_case10173_fs_interval_list_of_q_object_eval
      >> simp [])
  >> conj_tac
  >- (`2 < clock - 3` by intLib.ARITH_TAC
      >> simp [registered_case10173_hist_first_order_four_root_args])
  >> conj_tac
  >- simp []
  >> conj_tac
  >- (irule registered_case10173_fs_interval_list_of_q_object_eval
      >> simp [])
  >> `4 < clock - 4` by intLib.ARITH_TAC
  >> simp [registered_case10173_hist_second_order_four_root_args]
QED

val _ = export_theory ();
