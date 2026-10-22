(*****************************************************************************
 * Composition of the authenticated historical production-guard predicates.
 *
 * The preceding theory proves each primitive against its logical decimal
 * contract.  This layer keeps the final twelve-way conjunction independent
 * of the let-bound source computations that supply its values.
 *****************************************************************************)
Theory compute_registeredCase10173ProductionGuardCompositionEval
Ancestors
  compute_registeredCase10173ProductionGuardAuthenticatedEval
Libs
  bossLib preamble intLib

Definition registered_case10173_hist_production_guard_checks_body_def:
  registered_case10173_hist_production_guard_checks_body =
    App «candle_cv_fs_hist_bool_and»
      [App «candle_cv_fs_hist_positive_product»
        [Var «center_root_delta»;Var «center_root_four_x0»];
       App «candle_cv_fs_hist_bool_and»
        [App «candle_cv_fs_hist_positive_product»
          [Var «box_root_delta»;Var «box_root_four_x0»];
         App «candle_cv_fs_hist_bool_and»
          [App «candle_cv_fs_hist_positive_interval» [Var «center_u126»];
           App «candle_cv_fs_hist_bool_and»
            [App «candle_cv_fs_hist_positive_interval» [Var «center_u135»];
             App «candle_cv_fs_hist_bool_and»
              [App «candle_cv_fs_hist_positive_product»
                [Var «center_u126»;Var «center_u135»];
               App «candle_cv_fs_hist_bool_and»
                [App «candle_cv_fs_hist_positive_interval» [Var «box_u126»];
                 App «candle_cv_fs_hist_bool_and»
                  [App «candle_cv_fs_hist_positive_interval» [Var «box_u135»];
                   App «candle_cv_fs_hist_bool_and»
                    [App «candle_cv_fs_hist_positive_product»
                      [Var «box_u126»;Var «box_u135»];
                     App «candle_cv_fs_hist_bool_and»
                      [App «candle_cv_fs_hist_unit_interval»
                        [Var «center_quotient»];
                       App «candle_cv_fs_hist_bool_and»
                        [App «candle_cv_fs_hist_unit_interval»
                          [Var «box_quotient»];
                         App «candle_cv_fs_hist_bool_and»
                          [App «candle_cv_fs_hist_environment_nonnegative»
                            [Var «center_environment»];
                           App «candle_cv_fs_hist_environment_nonnegative»
                            [Var «box_environment»]]]]]]]]]]]]
End

Theorem registered_case10173_hist_production_guard_checks_eval:
  bounded_signed64_strict_positive
      (bounded_interval64_lower center_root_delta) /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower center_root_four_x0) /\
  0 <
    (w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower center_root_delta)) *
     w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower center_root_four_x0))) DIV
      1000000000000 /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower box_root_delta) /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower box_root_four_x0) /\
  0 <
    (w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower box_root_delta)) *
     w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower box_root_four_x0))) DIV
      1000000000000 /\
  bounded_interval64_valid center_u126 /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower center_u126) /\
  bounded_interval64_valid center_u135 /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower center_u135) /\
  0 <
    (w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower center_u126)) *
     w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower center_u135))) DIV
      1000000000000 /\
  bounded_interval64_valid box_u126 /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower box_u126) /\
  bounded_interval64_valid box_u135 /\
  bounded_signed64_strict_positive
      (bounded_interval64_lower box_u135) /\
  0 <
    (w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower box_u126)) *
     w2n
       (bounded_signed64_magnitude
         (bounded_interval64_lower box_u135))) DIV
      1000000000000 /\
  word_lo
    (bounded_signed64_magnitude
      (bounded_interval64_lower center_quotient))
    bounded_atan_scale_decimal /\
  word_lo
    (bounded_signed64_magnitude
      (bounded_interval64_upper center_quotient))
    bounded_atan_scale_decimal /\
  word_lo
    (bounded_signed64_magnitude
      (bounded_interval64_lower box_quotient))
    bounded_atan_scale_decimal /\
  word_lo
    (bounded_signed64_magnitude
      (bounded_interval64_upper box_quotient))
    bounded_atan_scale_decimal /\
  bounded_case10173_positive_environment center_environment /\
  bounded_case10173_positive_environment box_environment /\
  1000 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«center_root_delta»,
          from_cv (bounded_interval64_object_cv center_root_delta));
         («center_root_four_x0»,
          from_cv (bounded_interval64_object_cv center_root_four_x0));
         («box_root_delta»,
          from_cv (bounded_interval64_object_cv box_root_delta));
         («box_root_four_x0»,
          from_cv (bounded_interval64_object_cv box_root_four_x0));
         («center_u126»,from_cv (bounded_interval64_object_cv center_u126));
         («center_u135»,from_cv (bounded_interval64_object_cv center_u135));
         («box_u126»,from_cv (bounded_interval64_object_cv box_u126));
         («box_u135»,from_cv (bounded_interval64_object_cv box_u135));
         («center_quotient»,
          from_cv (bounded_interval64_object_cv center_quotient));
         («box_quotient»,
          from_cv (bounded_interval64_object_cv box_quotient));
         («center_environment»,
          from_cv (bounded_interval64_object_cv_list center_environment));
         («box_environment»,
          from_cv (bounded_interval64_object_cv_list box_environment))]
        registered_case10173_hist_production_guard_checks_body) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  rpt strip_tac
  >> simp
       [registered_case10173_hist_production_guard_checks_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_positive_product_eval >> simp [])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_positive_product_eval >> simp [])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_positive_interval_eval >> simp [])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_positive_interval_eval >> simp [])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_positive_product_eval >> simp [])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_positive_interval_eval >> simp [])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_positive_interval_eval >> simp [])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_positive_product_eval >> simp [])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_unit_interval_eval >> simp [])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_unit_interval_eval >> simp [])
  >> irule
       compute_registeredCase10173RootRecordEvalTheory.registered_case10173_hist_bool_and_true_one_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_hist_environment_nonnegative_eval
      >> simp [])
  >> irule registered_case10173_hist_environment_nonnegative_eval
  >> simp []
QED

val _ = export_theory ();
