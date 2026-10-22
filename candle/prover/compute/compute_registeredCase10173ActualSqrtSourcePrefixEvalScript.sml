(*****************************************************************************
 * Registered evaluation of one authenticated actual-operand sqrt step.
 *
 * The executable prefix contract recomputes the completed coordinate
 * variable and authenticates every numerical witness consumed by the
 * unchanged source sqrt instruction.  This theory decomposes one prefix
 * step and hands those witnesses directly to the registered evaluator
 * theorem, without replaying the generic numerical calculation.
 *****************************************************************************)
Theory compute_registeredCase10173ActualSqrtSourcePrefixEval
Ancestors
  compute_boundedCase10173ActualSqrtOperand
  compute_registeredCase10173ResultSqrtContract
Libs
  bossLib preamble

Theorem registered_case10173_actual_sqrt_source_prefix_head_eval:
  LENGTH radii = 6 /\
  bounded_case10173_actual_sqrt_source_prefix_exact
      (SUC remaining) index radii center_environment
      (Pair center_root center_roots)
      (Pair box_root box_roots)
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::certificates) /\
  8192 < clock ==>
  ?center_value center_gradient value_bound gradient_bounds source_hessian
   center_input box_input result source_hessian_rows result_rows.
    bounded_case10173_actual_variable_decimal
      radii center_environment index =
        SOME
          (BoundedTaylor64 T center_value center_gradient value_bound
            gradient_bounds source_hessian) /\
    bounded_case10173_positive_interval64_q_cv center_value =
      SOME center_input /\
    bounded_case10173_positive_interval64_q_cv value_bound = SOME box_input /\
    bounded_case10173_source_q_sqrt_certificate_exact
      center_input center_root /\
    bounded_case10173_source_q_sqrt_certificate_exact box_input box_root /\
    bounded_case10173_source_positive_q_interval64_exact
      center_root center_sqrt /\
    bounded_case10173_source_positive_q_interval64_exact box_root box_sqrt /\
    bounded_case10173_source_sqrt_dd_interval64_exact
      box_root box_input box_second_reciprocal /\
    bounded_hessian64_rows source_hessian = SOME source_hessian_rows /\
    bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal
      (BoundedTaylor64 T center_value center_gradient value_bound
        gradient_bounds source_hessian) = SOME result /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsn_result_sqrt»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           from_cv center_root;
           from_cv box_root;
           from_cv
             (Pair (Num 1)
               (Pair
                 (Pair (bounded_interval64_object_cv center_value)
                   (bounded_interval64_object_cv_list center_gradient))
                 (Pair (bounded_interval64_object_cv value_bound)
                   (Pair
                     (bounded_interval64_object_cv_list gradient_bounds)
                     (bounded_interval64_object_cv_matrix
                       source_hessian_rows)))))])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_taylor64_rows_object_cv result result_rows)),refs) /\
    bounded_case10173_actual_sqrt_source_prefix_exact
      remaining (SUC index) radii center_environment
      center_roots box_roots certificates
Proof
  strip_tac
  >> drule
       compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_cons
  >> disch_then strip_assume_tac
  >> Cases_on `domain_flag`
  >> gvs []
  >> `bounded_taylor64_well_formed
        (BoundedTaylor64 T center_value center_gradient value_bound
          gradient_bounds hessian)` by
       (irule
          compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_variable_decimal_some
        >> metis_tac [])
  >> fs [compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> drule
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length
  >> disch_then
       (qx_choose_then `source_hessian_rows` strip_assume_tac)
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173ResultSqrtContractTheory.registered_case10173_taylor_sqrt_decimal_eval
  >> qpat_x_assum `!refs. ?result_rows. _`
       (qspec_then `refs` strip_assume_tac)
  >> qexistsl_tac [`source_hessian_rows`,`result_rows`]
  >> fs []
QED

Theorem registered_case10173_actual_sqrt_source_prefix_head_uniform_eval:
  LENGTH radii = 6 /\
  bounded_case10173_actual_sqrt_source_prefix_exact
      (SUC remaining) index radii center_environment
      (Pair center_root center_roots)
      (Pair box_root box_roots)
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::certificates) ==>
  ?center_value center_gradient value_bound gradient_bounds source_hessian
   center_input box_input result source_hessian_rows result_rows.
    bounded_case10173_actual_variable_decimal
      radii center_environment index =
        SOME
          (BoundedTaylor64 T center_value center_gradient value_bound
            gradient_bounds source_hessian) /\
    bounded_case10173_positive_interval64_q_cv center_value =
      SOME center_input /\
    bounded_case10173_positive_interval64_q_cv value_bound = SOME box_input /\
    bounded_case10173_source_q_sqrt_certificate_exact
      center_input center_root /\
    bounded_case10173_source_q_sqrt_certificate_exact box_input box_root /\
    bounded_case10173_source_positive_q_interval64_exact
      center_root center_sqrt /\
    bounded_case10173_source_positive_q_interval64_exact box_root box_sqrt /\
    bounded_case10173_source_sqrt_dd_interval64_exact
      box_root box_input box_second_reciprocal /\
    bounded_hessian64_rows source_hessian = SOME source_hessian_rows /\
    bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal
      (BoundedTaylor64 T center_value center_gradient value_bound
        gradient_bounds source_hessian) = SOME result /\
    (case result of
     | BoundedTaylor64 result_domain center result_gradient result_value
         result_gradient_bounds result_hessian =>
         bounded_hessian64_rows result_hessian = SOME result_rows) /\
    (!clock refs.
      8192 < clock ==>
      compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fsn_result_sqrt»
            [from_cv (registered_case10173_word64_object_cv_list radii);
             from_cv center_root;
             from_cv box_root;
             from_cv
               (Pair (Num 1)
                 (Pair
                   (Pair (bounded_interval64_object_cv center_value)
                     (bounded_interval64_object_cv_list center_gradient))
                   (Pair (bounded_interval64_object_cv value_bound)
                     (Pair
                       (bounded_interval64_object_cv_list gradient_bounds)
                       (bounded_interval64_object_cv_matrix
                         source_hessian_rows)))))])
          (refs:hol_refs) =
        (M_success
          (from_cv (bounded_taylor64_rows_object_cv result result_rows)),
         refs)) /\
    bounded_case10173_actual_sqrt_source_prefix_exact
      remaining (SUC index) radii center_environment
      center_roots box_roots certificates
Proof
  strip_tac
  >> drule
       compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_cons
  >> disch_then strip_assume_tac
  >> Cases_on `domain_flag`
  >> gvs []
  >> `bounded_taylor64_well_formed
        (BoundedTaylor64 T center_value center_gradient value_bound
          gradient_bounds hessian)` by
       (irule
          compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_variable_decimal_some
        >> metis_tac [])
  >> fs [compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> drule
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length
  >> disch_then
       (qx_choose_then `source_hessian_rows` strip_assume_tac)
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173ResultSqrtContractTheory.registered_case10173_taylor_sqrt_decimal_typed_contract
  >> Cases_on `root`
  >> gvs []
  >> rpt gen_tac
  >> strip_tac
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173ActualResultSqrtEvalTheory.registered_case10173_actual_result_sqrt_eval
  >> qpat_x_assum `!refs. compute_eval clock _ _ refs = _`
       (qspec_then `refs` assume_tac)
  >> fs []
QED

val _ = export_theory ();
