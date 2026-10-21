(*****************************************************************************
 * Packet-parametric handoff from an authenticated literal fixed result to
 * the rational certified-finish result consumed by the historical wrapper.
 *
 * Decimal packet coverage is intentionally kept at its native 10^12 scale.
 * The final source box-validity check needs only the ordering of the encoded
 * rational endpoints, which follows directly from that coverage relation;
 * no conversion through the legacy 2^40 carrier is involved.
 *****************************************************************************)
Theory compute_registeredCase10173AuthenticatedLiteralHandoffEval
Ancestors
  compute_registeredCase10173FixedItemToQEval
  compute_registeredCase10173BoxValidityEval
  compute_registeredCase10173LiteralSourceComponentsEval
Libs
  bossLib preamble intLib

Theorem bounded_case10173_literal_source_decimal_well_formed:
  bounded_case10173_literal_source_decimal packet = SOME result ==>
  bounded_taylor64_well_formed result
Proof
  Cases_on `packet`
  >> strip_tac
  >> drule
       compute_registeredCase10173LiteralSourceComponentsEvalTheory.registered_case10173_literal_source_components
  >> strip_tac
  >> imp_res_tac
       compute_boundedTaylorMulDecimalTheory.bounded_taylor64_mul_decimal_some
  >> imp_res_tac
       compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_add_stack_decimal_some
QED

Theorem registered_case10173_literal_result_item_to_q_eval:
  bounded_taylor64_well_formed
    (BoundedTaylor64 result_domain center_value center_gradient
      value_bound gradient_bounds hessian) /\
  64 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_to_q»
        [from_cv
          (Pair (Num 1)
            (registered_case10173_taylor_object
              (BoundedTaylor64 result_domain center_value center_gradient
                value_bound gradient_bounds hessian)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_fixed_q_taylor_object_cv
          (BoundedTaylor64 result_domain center_value center_gradient
            value_bound gradient_bounds hessian)
          (registered_case10173_taylor_rows
            (BoundedTaylor64 result_domain center_value center_gradient
              value_bound gradient_bounds hessian)))),refs)
Proof
  strip_tac
  >> drule
       compute_registeredCase10173LiteralAddChainEvalTheory.registered_case10173_taylor_rows_exact
  >> strip_tac
  >> imp_res_tac
       compute_registeredCase10173ResultMulAboveEvalTheory.registered_case10173_matrix_shape6_sum
  >> PURE_ONCE_REWRITE_TAC
       [compute_registeredCase10173LiteralAddChainEvalTheory.registered_case10173_taylor_object_def]
  >> irule
       compute_registeredCase10173FixedItemToQEvalTheory.registered_case10173_fsa_item_to_q_fixed_taylor_eval
  >> fs [compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_list_rel_decimal_coverage_ordered:
  !intervals object_intervals.
    LIST_REL bounded_interval64_covers_object_q_ints_decimal
      intervals object_intervals ==>
    EVERY
      (\object_interval.
        (FST (FST object_interval)) * (SND (SND object_interval)) <=
        (FST (SND object_interval)) * (SND (FST object_interval)))
      object_intervals
Proof
  Induct_on `intervals`
  >> Cases_on `object_intervals`
  >> simp
       [compute_boundedObjectDecimalQTheory.bounded_interval64_covers_object_q_ints_decimal_def]
  >> Cases_on `h`
  >> Cases_on `r`
  >> Cases_on `q`
  >> simp
       [compute_boundedObjectDecimalQTheory.bounded_interval64_covers_object_q_ints_decimal_def]
QED

Theorem registered_case10173_q_box_valid_list_from_decimal_coverage_eval:
  bounded_interval64_list_covers_object_q_decimal intervals boxes /\
  LENGTH intervals + 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_box_valid_list» [from_cv boxes])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  rw
    [compute_boundedObjectDecimalQTheory.bounded_interval64_list_covers_object_q_decimal_def]
  >> Cases_on `bounded_object_q_interval_list boxes`
  >> fs []
  >> irule
       compute_registeredCase10173BoxValidityEvalTheory.registered_case10173_q_box_valid_list_ordered_eval
  >> qexists_tac `x`
  >> simp []
  >> conj_tac
  >- (imp_res_tac LIST_REL_LENGTH
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_list_rel_decimal_coverage_ordered
  >> qexists_tac `intervals`
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_q_certified_finish_fixed_taylor_from_decimal_coverage_eval:
  bounded_interval64_list_covers_object_q_decimal intervals boxes /\
  bounded_signed64_strict_negative value_upper /\
  6 < clock /\
  LENGTH intervals + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_certified_finish»
        [from_cv boxes;
         from_cv
           (registered_case10173_fixed_q_taylor_object_cv
             (BoundedTaylor64 T center_value center_gradient
               (BoundedInterval64 value_lower value_upper)
               gradient_bounds hessian) rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (registered_case10173_fixed_q_endpoint_cv value_upper))),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173FixedCertifiedFinishEvalTheory.registered_case10173_q_certified_finish_fixed_taylor_eval
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> irule registered_case10173_q_box_valid_list_from_decimal_coverage_eval
  >> qexists_tac `intervals`
  >> conj_tac >- intLib.ARITH_TAC
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
