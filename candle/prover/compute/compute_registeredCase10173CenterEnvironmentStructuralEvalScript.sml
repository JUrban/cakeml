(*****************************************************************************
 * Structural-clock evaluation of the rational center-environment traversal.
 *
 * The evaluator recurses over the list spine and performs fixed-depth
 * rational midpoint operations at each node.  Its clock use is independent
 * of numerator and denominator magnitudes, which cv_size unnecessarily
 * charges.
 *****************************************************************************)
Theory compute_registeredCase10173CenterEnvironmentStructuralEval
Ancestors
  compute_registeredCase10173CenterEnvironmentEval
Libs
  bossLib preamble intLib

Definition registered_case10173_center_list_length_def:
  registered_case10173_center_list_length (Num n : cv) = 0 /\
  registered_case10173_center_list_length (Pair item items) =
    SUC (registered_case10173_center_list_length items)
End

Theorem registered_case10173_center_list_length_positive_decode:
  !encoded intervals.
    bounded_object_positive_q_interval64_decimal_list encoded =
      SOME intervals ==>
    registered_case10173_center_list_length encoded = LENGTH intervals
Proof
  ho_match_mp_tac
    compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_ind
  >> rw
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_def,
        registered_case10173_center_list_length_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_q_center_environment_positive_eval_structural:
  !boxes centers clock refs.
    registered_case10173_q_center_environment_positive boxes = SOME centers /\
    8 * (registered_case10173_center_list_length boxes + 1) < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_center_environment_list» [from_cv boxes])
        (refs:hol_refs) =
      (M_success (from_cv centers),refs)
Proof
  ho_match_mp_tac
    compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_center_environment_positive_ind
  >> rw
       [compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_center_environment_positive_def]
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_center_environment_list_nil_eval)
      >> intLib.ARITH_TAC)
  >> Cases_on
       `registered_case10173_q_center_environment_positive boxes`
  >> gvs []
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`interval` |->
              `Pair
                (Pair (Pair (Num lower_value) (Num 0))
                  (Num lower_denominator_minus_one))
                (Pair (Pair (Num upper_value) (Num 0))
                  (Num upper_denominator_minus_one))`,
            `midpoint` |->
              `registered_case10173_q_midpoint_positive_cv
                lower_value lower_denominator_minus_one
                upper_value upper_denominator_minus_one`]
           compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_center_environment_list_cons_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >> FIRST
       [irule
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            (Q.INST
              [`clock` |-> `clock - 1`,
               `lower_value` |-> `lower_value`,
               `lower_denominator_minus_one` |->
                 `lower_denominator_minus_one`,
               `upper_value` |-> `upper_value`,
               `upper_denominator_minus_one` |->
                 `upper_denominator_minus_one`,
               `refs` |-> `refs`]
              compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_midpoint_positive_eval))
        >> intLib.ARITH_TAC,
        qpat_x_assum `!clock' refs. _`
          (qspecl_then [`clock - 1`,`refs`] match_mp_tac)
        >> fs
             [registered_case10173_center_list_length_def]
        >> intLib.ARITH_TAC]
QED

Theorem registered_case10173_center_environment_decimal_eval_structural:
  registered_case10173_q_center_environment_positive boxes =
      SOME center_boxes /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME center_environment /\
  8 * (registered_case10173_center_list_length boxes + 1) < clock /\
  11 * (LENGTH center_environment + 1) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_of_q»
        [App «candle_cv_q_center_environment_list» [from_cv boxes]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv_list center_environment)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_center_environment_list» [from_cv boxes]) refs =
      (M_success (from_cv center_boxes),refs)` by
       simp [registered_case10173_q_center_environment_positive_eval_structural]
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_of_q»
          [App «candle_cv_q_center_environment_list» [from_cv boxes]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_of_q»
          [from_cv center_boxes]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp []
        >> intLib.ARITH_TAC)
  >> simp
       [compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_list_of_q_object_eval]
QED

val _ = export_theory ();
