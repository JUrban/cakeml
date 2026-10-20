(*****************************************************************************
 * Registered evaluation of the genuine coordinate-root coefficient product.
 *
 * The canonical actual-operand contract now checks the square root and the
 * immediately following multiplication by the coordinate's fixed source
 * coefficient.  This layer exposes the checked typed product through the
 * unchanged literal [fs_result_mul] source call.  It is generic in the
 * coordinate; the six fixed source programs are identified only when the
 * complete prefix is assembled.
 *****************************************************************************)
Theory compute_registeredCase10173ActualGroupProductEval
Ancestors
  compute_registeredCase10173ActualSqrtSourcePrefixEval
  compute_registeredCase10173ResultMulAboveEval
Libs
  bossLib preamble

Definition registered_case10173_taylor_hessian_def:
  registered_case10173_taylor_hessian
      (BoundedTaylor64 domain center center_gradient value gradient hessian) =
    hessian
End

Definition registered_case10173_taylor_domain_def:
  registered_case10173_taylor_domain
      (BoundedTaylor64 domain center center_gradient value gradient hessian) =
    domain
End

Theorem bounded_taylor64_constant_true_domain:
  bounded_taylor64_constant coefficient =
    SOME (BoundedTaylor64 domain_flag center center_gradient value gradient
      hessian)
  ==>
  domain_flag
Proof
  rw [compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def]
  >> gvs [compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
          LET_THM]
QED

Theorem bounded_taylor64_complete_decimal_true_domain:
  bounded_taylor64_complete_decimal radii T center center_gradient hessian =
    SOME (BoundedTaylor64 domain_flag result_center result_center_gradient
      value gradient result_hessian)
  ==>
  domain_flag
Proof
  rw
    [compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_def]
  >> every_case_tac
  >> gvs [compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
          LET_THM]
QED

Theorem bounded_taylor64_unary_complete_decimal_true_domain:
  bounded_taylor64_unary_complete_decimal radii T center_result
      center_derivative box_derivative box_second
      (BoundedTaylor64 T source_center source_center_gradient source_value
        source_gradient source_hessian) =
    SOME (BoundedTaylor64 domain_flag center center_gradient value gradient
      hessian)
  ==>
  domain_flag
Proof
  rw
    [compute_boundedTaylorUnaryDecimalTheory.bounded_taylor64_unary_complete_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_taylor64_complete_decimal_true_domain
QED

Theorem bounded_taylor64_sqrt_decimal_true_domain:
  bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal
      (BoundedTaylor64 T source_center source_center_gradient source_value
        source_gradient source_hessian) =
    SOME (BoundedTaylor64 domain_flag center center_gradient value gradient
      hessian)
  ==>
  domain_flag
Proof
  rw [compute_boundedTaylorSqrtDecimalTheory.bounded_taylor64_sqrt_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_taylor64_unary_complete_decimal_true_domain
QED

Theorem bounded_taylor64_mul_decimal_true_domain:
  bounded_taylor64_mul_decimal radii
      (BoundedTaylor64 T left_center left_center_gradient left_value
        left_gradient left_hessian)
      (BoundedTaylor64 T right_center right_center_gradient right_value
        right_gradient right_hessian) =
    SOME
      (BoundedTaylor64 domain_flag center center_gradient value gradient
        hessian)
  ==>
  domain_flag
Proof
  rw [compute_boundedTaylorMulDecimalTheory.bounded_taylor64_mul_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_taylor64_complete_decimal_true_domain
QED

Theorem registered_case10173_taylor_mul_decimal_eval_above_exists:
  LENGTH radii = 6 /\
  registered_case10173_taylor_domain left /\
  registered_case10173_taylor_domain right /\
  bounded_taylor64_mul_decimal radii left right = SOME result ==>
  ?left_rows right_rows result_rows.
    bounded_hessian64_rows (registered_case10173_taylor_hessian left) =
      SOME left_rows /\
    bounded_hessian64_rows (registered_case10173_taylor_hessian right) =
      SOME right_rows /\
    bounded_hessian64_rows (registered_case10173_taylor_hessian result) =
      SOME result_rows /\
    registered_case10173_eval_above 8210
      (App «candle_cv_fs_result_mul»
        [from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv (bounded_taylor64_rows_object_cv left left_rows);
         from_cv (bounded_taylor64_rows_object_cv right right_rows)])
      (bounded_taylor64_rows_object_cv result result_rows)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> simp
       [registered_case10173_taylor_domain_def,
        registered_case10173_taylor_hessian_def]
  >> strip_tac
  >> imp_res_tac
       compute_boundedTaylorMulDecimalTheory.bounded_taylor64_mul_decimal_some
  >> imp_res_tac
       compute_registeredCase10173ResultMulContractTheory.registered_case10173_taylor_mul_decimal_contract_components
  >> gvs []
  >> imp_res_tac bounded_taylor64_mul_decimal_true_domain
  >> gvs []
  >> fs [compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length
  >> qexistsl_tac [`rows'`,`rows`,`rows''`]
  >> asm_rewrite_tac []
  >> irule
       compute_registeredCase10173ResultMulAboveEvalTheory.registered_case10173_taylor_mul_decimal_eval_above
  >> simp []
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_actual_group_product_eval_above:
  LENGTH radii = 6 /\
  bounded_case10173_actual_sqrt_source_prefix_exact
      (SUC remaining) index radii center_environment
      (Pair center_root center_roots)
      (Pair box_root box_roots)
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::certificates)
  ==>
  ?variable root root_rows coefficient coefficient_state coefficient_rows product
   product_rows.
    bounded_case10173_actual_variable_decimal
      radii center_environment index = SOME variable /\
    bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal variable =
      SOME root /\
    bounded_interval64_nth bounded_case10173_root_coefficients_decimal index =
      SOME coefficient /\
    bounded_taylor64_constant coefficient = SOME coefficient_state /\
    bounded_taylor64_mul_decimal radii root coefficient_state = SOME product /\
    bounded_hessian64_rows (registered_case10173_taylor_hessian root) =
      SOME root_rows /\
    bounded_hessian64_rows
      (registered_case10173_taylor_hessian coefficient_state) =
      SOME coefficient_rows /\
    bounded_hessian64_rows (registered_case10173_taylor_hessian product) =
      SOME product_rows /\
    registered_case10173_eval_above 8210
      (App «candle_cv_fs_result_mul»
        [from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv (bounded_taylor64_rows_object_cv root root_rows);
         from_cv
           (bounded_taylor64_rows_object_cv coefficient_state
             coefficient_rows)])
      (bounded_taylor64_rows_object_cv product product_rows)
Proof
  strip_tac
  >> drule
       compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_cons
  >> disch_then strip_assume_tac
  >> imp_res_tac
       compute_boundedTaylorSqrtDecimalTheory.bounded_taylor64_sqrt_decimal_some
  >> imp_res_tac
       compute_boundedTaylorBaseTheory.bounded_taylor64_constant_some
  >> imp_res_tac
       compute_boundedTaylorMulDecimalTheory.bounded_taylor64_mul_decimal_some
  >> Cases_on `domain_flag`
  >> gvs []
  >> `registered_case10173_taylor_domain root` by
       (Cases_on `root`
        >> simp [registered_case10173_taylor_domain_def]
        >> imp_res_tac bounded_taylor64_sqrt_decimal_true_domain)
  >> `registered_case10173_taylor_domain coefficient_state` by
       (Cases_on `coefficient_state`
        >> simp [registered_case10173_taylor_domain_def]
        >> imp_res_tac bounded_taylor64_constant_true_domain)
  >> mp_tac
       (Q.INST
         [`left` |-> `root`,
          `right` |-> `coefficient_state`,
          `result` |-> `product`]
         registered_case10173_taylor_mul_decimal_eval_above_exists)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> qexistsl_tac [`left_rows`,`right_rows`,`result_rows`]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
