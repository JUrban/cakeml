(*****************************************************************************
 * Literal result-level square-root evaluation on authenticated decimals.
 *
 * This is the composition boundary needed by the unchanged Taylor source:
 * domain checks, the center first jet, the box Hessian, and Taylor completion
 * are all evaluated by their registered source programs.  The theorem stays
 * parameterized by one genuine coordinate result; no case-10173 constants or
 * closed numerical answers are substituted into the evaluator.
 *****************************************************************************)
Theory compute_registeredCase10173ActualResultSqrtEval
Ancestors
  compute_registeredCase10173ActualSqrtFirstEval
  compute_registeredCase10173ResultSqrtAccessorEval
  compute_registeredCase10173TaylorCompleteObjectEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_actual_result_sqrt_eval:
  LENGTH radii = 6 /\
  bounded_interval64_valid center_value /\
  bounded_interval64_valid value_bound /\
  bounded_case10173_positive_interval64_q_cv center_value =
    SOME center_input /\
  bounded_case10173_positive_interval64_q_cv value_bound =
    SOME box_input /\
  bounded_case10173_source_q_sqrt_certificate_exact
    center_input center_root /\
  bounded_case10173_source_q_sqrt_certificate_exact
    box_input box_root /\
  bounded_case10173_source_positive_q_interval64_exact
    center_root center_sqrt /\
  bounded_case10173_source_positive_q_interval64_exact
    box_root box_sqrt /\
  (case center_sqrt of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  (case box_sqrt of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  bounded_interval64_add center_sqrt center_sqrt = SOME center_twice /\
  bounded_interval64_add box_sqrt box_sqrt = SOME box_twice /\
  (case center_twice of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  (case box_twice of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  bounded_interval64_positive_inv_certificate_decimal
    center_twice center_derivative /\
  bounded_interval64_positive_inv_certificate_decimal
    box_twice box_derivative /\
  (case center_derivative of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  (case box_derivative of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  bounded_case10173_source_sqrt_dd_interval64_exact
    box_root box_input box_second_reciprocal /\
  LENGTH center_gradient = 6 /\
  LENGTH gradient_bounds = 6 /\
  bounded_interval64_list_scale_decimal
    center_derivative center_gradient = SOME result_center_gradient /\
  bounded_interval64_self_outer_decimal gradient_bounds =
    SOME compact_outer /\
  bounded_hessian64_rows compact_outer = SOME outer_rows /\
  bounded_interval64_list_scale_decimal
    (bounded_interval64_neg box_second_reciprocal) compact_outer =
      SOME outer_hessian /\
  bounded_hessian64_rows outer_hessian = SOME outer_hessian_rows /\
  bounded_hessian64_rows source_hessian = SOME source_hessian_rows /\
  bounded_interval64_list_scale_decimal box_derivative source_hessian =
    SOME scaled_hessian /\
  bounded_hessian64_rows scaled_hessian = SOME scaled_hessian_rows /\
  bounded_interval64_list_add outer_hessian scaled_hessian =
    SOME result_hessian /\
  bounded_hessian64_rows result_hessian = SOME result_rows /\
  bounded_object_fs_taylor_complete radii T center_sqrt
    result_center_gradient result_hessian result_rows = SOME result_object /\
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
      (refs:hol_refs) = (M_success (from_cv result_object),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173ResultSqrtEvalTheory.registered_case10173_fsn_result_sqrt_eval_from_components
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `Pair (bounded_interval64_object_cv center_sqrt)
          (bounded_interval64_object_cv_list result_center_gradient)`
  >> qexists_tac `bounded_interval64_object_cv_matrix result_rows`
  >> qexists_tac `Num 1`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss
          [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def]
          (Q.INST [`result_domain` |-> `T`]
            compute_registeredCase10173TaylorCompleteObjectEvalTheory.registered_case10173_fs_result_complete_rounded_object_eval))
      >> imp_res_tac
           compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_length
      >> imp_res_tac
           compute_registeredCase10173ActualSqrtHessianComposeTheory.registered_case10173_hessian_rows_size
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `result_hessian`
      >> asm_rewrite_tac [])
  >> conj_tac
  >- (irule
        compute_registeredCase10173ResultSqrtAccessorEvalTheory.registered_case10173_fsn_result_sqrt_center_direct_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_registeredCase10173ActualSqrtFirstEvalTheory.registered_case10173_actual_sqrt_first_eval
      >> asm_rewrite_tac []
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `center_derivative`
      >> qexists_tac `center_twice`
      >> asm_rewrite_tac [])
  >> conj_tac
  >- (simp [compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173ResultSqrtAccessorEvalTheory.registered_case10173_fsn_result_sqrt_domain_direct_eval)
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            compute_registeredCase10173ActualSqrtDomainEvalTheory.registered_case10173_actual_sqrt_domain_eval
          >> asm_rewrite_tac []
          >> conj_tac >- intLib.ARITH_TAC
          >> conj_tac
          >- metis_tac
               [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_interval64_exact_conversion]
          >> qexists_tac `box_input`
          >> asm_rewrite_tac [])
      >> irule
           compute_registeredCase10173ActualSqrtDomainEvalTheory.registered_case10173_actual_sqrt_domain_eval
      >> asm_rewrite_tac []
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- metis_tac
           [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_interval64_exact_conversion]
      >> qexists_tac `center_input`
      >> asm_rewrite_tac [])
  >> irule
        compute_registeredCase10173ResultSqrtAccessorEvalTheory.registered_case10173_fsn_result_sqrt_hessian_direct_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       compute_registeredCase10173ActualSqrtHessianComposeTheory.registered_case10173_actual_sqrt_hessian_eval
  >> asm_rewrite_tac []
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `compact_outer`
  >> qexists_tac `box_derivative`
  >> qexists_tac `source_hessian`
  >> qexists_tac `box_input`
  >> qexists_tac `outer_hessian`
  >> qexists_tac `outer_hessian_rows`
  >> qexists_tac `outer_rows`
  >> qexists_tac `result_hessian`
  >> qexists_tac `box_sqrt`
  >> qexists_tac `scaled_hessian`
  >> qexists_tac `scaled_hessian_rows`
  >> qexists_tac `box_second_reciprocal`
  >> qexists_tac `box_twice`
  >> asm_rewrite_tac []
  >> metis_tac
       [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_interval64_exact_conversion]
QED

val _ = export_theory ();
