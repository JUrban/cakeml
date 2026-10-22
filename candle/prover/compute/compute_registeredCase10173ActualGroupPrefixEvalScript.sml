(*****************************************************************************
 * Genuine six-coordinate numerical contracts for the literal source prefix.
 *
 * The authenticated actual-operand contract supplies the variable, square
 * root and following fixed-coefficient product for every coordinate.  The
 * literal polynomial theorem supplies the fixed coefficient and term
 * programs.  This layer joins those facts through one indexed source table;
 * no result object or coordinate-specific arithmetic fact is supplied by the
 * caller.
 *****************************************************************************)
Theory compute_registeredCase10173ActualGroupPrefixEval
Ancestors
  compute_registeredCase10173ActualCoordinatePrefixEval
  compute_registeredCase10173ActualGroupProductEval
  compute_registeredCase10173PolynomialConstantTrace
Libs
  bossLib preamble intLib

Definition registered_case10173_root_coefficient_programs_def:
  registered_case10173_root_coefficient_programs =
    [registered_case10173_ordinary_coefficient0_program;
     registered_case10173_ordinary_coefficient12_program;
     registered_case10173_ordinary_coefficient12_program;
     registered_case10173_ordinary_coefficient3_program;
     registered_case10173_ordinary_coefficient45_program;
     registered_case10173_ordinary_coefficient45_program]
End

Definition registered_case10173_root_coefficient_values_def:
  registered_case10173_root_coefficient_values =
    [registered_case10173_ordinary_coefficient0_value;
     registered_case10173_ordinary_coefficient12_value;
     registered_case10173_ordinary_coefficient12_value;
     registered_case10173_ordinary_coefficient3_value;
     registered_case10173_ordinary_coefficient45_value;
     registered_case10173_ordinary_coefficient45_value]
End

Definition registered_case10173_root_term_programs_def:
  registered_case10173_root_term_programs =
    [registered_case10173_ordinary_term1_program;
     registered_case10173_ordinary_term23_program;
     registered_case10173_ordinary_term23_program;
     registered_case10173_ordinary_term4_program;
     registered_case10173_ordinary_term56_program;
     registered_case10173_ordinary_term56_program]
End

Definition registered_case10173_root_term_values_def:
  registered_case10173_root_term_values =
    [registered_case10173_ordinary_term1_value;
     registered_case10173_ordinary_term23_value;
     registered_case10173_ordinary_term23_value;
     registered_case10173_ordinary_term4_value;
     registered_case10173_ordinary_term56_value;
     registered_case10173_ordinary_term56_value]
End

Theorem registered_case10173_root_source_table_lengths:
  LENGTH registered_case10173_root_coefficient_programs = 6 /\
  LENGTH registered_case10173_root_coefficient_values = 6 /\
  LENGTH registered_case10173_root_term_programs = 6 /\
  LENGTH registered_case10173_root_term_values = 6
Proof
  simp
    [registered_case10173_root_coefficient_programs_def,
     registered_case10173_root_coefficient_values_def,
     registered_case10173_root_term_programs_def,
     registered_case10173_root_term_values_def]
QED

Theorem registered_case10173_root_coefficients_decimal_at:
  index < 6 ==>
  bounded_interval64_nth bounded_case10173_root_coefficients_decimal index =
    SOME (EL index registered_case10173_root_coefficient_values)
Proof
  Cases_on `index`
  >> simp
       [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def,
        compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_root_coefficients_decimal_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_ordinary_coefficient0_value_def,
        registered_case10173_ordinary_coefficient12_value_def,
        registered_case10173_ordinary_coefficient3_value_def,
        registered_case10173_ordinary_coefficient45_value_def,
        registered_case10173_decimal_point_def]
  >> Cases_on `n`
  >> simp
       [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def,
        compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_root_coefficients_decimal_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_ordinary_coefficient0_value_def,
        registered_case10173_ordinary_coefficient12_value_def,
        registered_case10173_ordinary_coefficient3_value_def,
        registered_case10173_ordinary_coefficient45_value_def,
        registered_case10173_decimal_point_def]
  >> Cases_on `n'`
  >> simp
       [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def,
        compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_root_coefficients_decimal_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_ordinary_coefficient0_value_def,
        registered_case10173_ordinary_coefficient12_value_def,
        registered_case10173_ordinary_coefficient3_value_def,
        registered_case10173_ordinary_coefficient45_value_def,
        registered_case10173_decimal_point_def]
  >> Cases_on `n`
  >> simp
       [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def,
        compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_root_coefficients_decimal_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_ordinary_coefficient0_value_def,
        registered_case10173_ordinary_coefficient12_value_def,
        registered_case10173_ordinary_coefficient3_value_def,
        registered_case10173_ordinary_coefficient45_value_def,
        registered_case10173_decimal_point_def]
  >> Cases_on `n'`
  >> simp
       [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def,
        compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_root_coefficients_decimal_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_ordinary_coefficient0_value_def,
        registered_case10173_ordinary_coefficient12_value_def,
        registered_case10173_ordinary_coefficient3_value_def,
        registered_case10173_ordinary_coefficient45_value_def,
        registered_case10173_decimal_point_def]
  >> Cases_on `n`
  >> simp
       [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def,
        compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_root_coefficients_decimal_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_ordinary_coefficient0_value_def,
        registered_case10173_ordinary_coefficient12_value_def,
        registered_case10173_ordinary_coefficient3_value_def,
        registered_case10173_ordinary_coefficient45_value_def,
        registered_case10173_decimal_point_def]
QED

Theorem registered_case10173_constant_taylor_from_checked_constructor:
  bounded_taylor64_constant value = SOME coefficient_state ==>
  coefficient_state = registered_case10173_constant_taylor value
Proof
  rw
    [compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def,
     compute_boundedTaylorStateTheory.bounded_taylor64_make_def]
  >> every_case_tac
  >> gvs [registered_case10173_constant_taylor_def]
  >> EVAL_TAC
QED

Theorem registered_case10173_root_literal_programs_eval_above:
  LENGTH dimensions = 6 /\ LENGTH radii = 6 /\ index < 6 /\
  registered_case10173_eval_above 8208
      (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
      (bounded_interval64_object_cv_list dimensions) /\
  registered_case10173_eval_above 8208
      (App «candle_cv_fs_list_of_q» [from_cv source_radii])
      (registered_case10173_word64_object_cv_list radii) ==>
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv (EL index registered_case10173_root_coefficient_programs)])
      (registered_case10173_constant_object
        (EL index registered_case10173_root_coefficient_values)) /\
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv (EL index registered_case10173_root_term_programs)])
      (registered_case10173_constant_object
        (EL index registered_case10173_root_term_values))
Proof
  strip_tac
  >> imp_res_tac registered_case10173_literal_programs_eval_above
  >> Cases_on `index`
  >> gvs
       [registered_case10173_root_coefficient_programs_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_root_term_programs_def,
        registered_case10173_root_term_values_def]
  >> Cases_on `n`
  >> gvs
       [registered_case10173_root_coefficient_programs_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_root_term_programs_def,
        registered_case10173_root_term_values_def]
  >> Cases_on `n'`
  >> gvs
       [registered_case10173_root_coefficient_programs_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_root_term_programs_def,
        registered_case10173_root_term_values_def]
  >> Cases_on `n`
  >> gvs
       [registered_case10173_root_coefficient_programs_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_root_term_programs_def,
        registered_case10173_root_term_values_def]
  >> Cases_on `n'`
  >> gvs
       [registered_case10173_root_coefficient_programs_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_root_term_programs_def,
        registered_case10173_root_term_values_def]
  >> Cases_on `n`
  >> gvs
       [registered_case10173_root_coefficient_programs_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_root_term_programs_def,
        registered_case10173_root_term_values_def]
QED

Theorem registered_case10173_actual_group_numeric_contract:
  LENGTH radii = 6 /\
  LENGTH center_environment = 6 /\
  LENGTH dimensions = 6 /\
  index < 6 /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
    SOME center_environment /\
  registered_case10173_eval_above 8208
      (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
      (bounded_interval64_object_cv_list dimensions) /\
  registered_case10173_eval_above 8208
      (App «candle_cv_fs_list_of_q» [from_cv source_radii])
      (registered_case10173_word64_object_cv_list radii) /\
  bounded_case10173_actual_sqrt_source_prefix_exact
      (SUC remaining) index radii center_environment
      (Pair center_root center_roots)
      (Pair box_root box_roots)
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::certificates)
  ==>
  ?variable root product variable_rows root_rows product_rows.
    bounded_case10173_actual_variable_decimal
        radii center_environment index = SOME variable /\
    bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal variable =
      SOME root /\
    bounded_taylor64_mul_decimal radii root
        (registered_case10173_constant_taylor
          (EL index registered_case10173_root_coefficient_values)) =
      SOME product /\
    bounded_hessian64_rows
        (registered_case10173_taylor_hessian variable) = SOME variable_rows /\
    bounded_hessian64_rows
        (registered_case10173_taylor_hessian root) = SOME root_rows /\
    bounded_hessian64_rows
        (registered_case10173_taylor_hessian product) = SOME product_rows /\
    registered_case10173_ordinary_group_numeric_contract 8210
      center_boxes boxes source_radii
      (registered_case10173_word64_object_cv_list radii)
      (registered_case10173_ordinary_variable_program index)
      center_root box_root
      (EL index registered_case10173_root_coefficient_programs)
      (EL index registered_case10173_root_term_programs)
      (bounded_taylor64_rows_object_cv variable variable_rows)
      (bounded_taylor64_rows_object_cv root root_rows)
      (registered_case10173_constant_object
        (EL index registered_case10173_root_coefficient_values))
      (bounded_taylor64_rows_object_cv product product_rows)
      (registered_case10173_constant_object
        (EL index registered_case10173_root_term_values))
Proof
  strip_tac
  >> drule_all_then strip_assume_tac
       registered_case10173_root_literal_programs_eval_above
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173ActualSqrtSourcePrefixEvalTheory.registered_case10173_actual_sqrt_source_prefix_head_uniform_eval
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_actual_group_product_eval_above
  >> imp_res_tac registered_case10173_root_coefficients_decimal_at
  >> imp_res_tac registered_case10173_constant_taylor_from_checked_constructor
  >> imp_res_tac
       compute_registeredCase10173ActualCoordinatePrefixEvalTheory.bounded_case10173_actual_variable_decimal_hessian
  >> gvs []
  >> `source_hessian_rows =
        REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)` by
       fs
         [compute_registeredCase10173ActualCoordinatePrefixEvalTheory.registered_case10173_zero_hessian_rows]
  >> `coefficient_rows =
        REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)` by
       fs
         [registered_case10173_constant_taylor_def,
          registered_case10173_zero_hessian_rows_constant,
          compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_hessian_def]
  >> qexists_tac `source_hessian_rows`
  >> asm_rewrite_tac []
  >> rw
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_hessian_def,
        compute_registeredCase10173OrdinaryGroupTraceEvalTheory.registered_case10173_ordinary_group_numeric_contract_def]
  >- (irule
        compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_weaken
      >> qexists_tac `8208`
      >> simp []
      >> asm_rewrite_tac [])
  >- (irule
        compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_weaken
      >> qexists_tac `8209`
      >> simp []
      >> rw
           [compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_variable_program_def]
      >> irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_registeredCase10173ActualCoordinatePrefixEvalTheory.registered_case10173_actual_variable_poly_program_eval_above)
      >> asm_rewrite_tac []
      >> conj_tac
      >- (qexists_tac
            `REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)`
          >> asm_rewrite_tac [])
      >> qexists_tac `center_environment`
      >> qexists_tac `radii`
      >> asm_rewrite_tac [])
  >- (irule
        compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_weaken
      >> qexists_tac `8192`
      >> simp []
      >> PURE_REWRITE_TAC
           [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def,
            compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def,
            COND_CLAUSES]
      >> fs
           [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def,
            compute_execTheory.from_cv_def]
      >> Cases_on `result`
      >> gvs
           [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_hessian_def])
  >> asm_rewrite_tac
       [registered_case10173_constant_object_def]
QED

Definition registered_case10173_actual_group_eval_prefix_def:
  registered_case10173_actual_group_eval_prefix
      0 index center_boxes boxes source_radii fixed_radii center_roots
      box_roots certificates = T /\
  registered_case10173_actual_group_eval_prefix
      (SUC remaining) index center_boxes boxes source_radii fixed_radii
      (Pair center_root center_roots) (Pair box_root box_roots)
      (certificate::certificates) =
    (?variable root product variable_rows root_rows product_rows.
       registered_case10173_ordinary_group_numeric_contract 8210
         center_boxes boxes source_radii fixed_radii
         (registered_case10173_ordinary_variable_program index)
         center_root box_root
         (EL index registered_case10173_root_coefficient_programs)
         (EL index registered_case10173_root_term_programs)
         (bounded_taylor64_rows_object_cv variable variable_rows)
         (bounded_taylor64_rows_object_cv root root_rows)
         (registered_case10173_constant_object
           (EL index registered_case10173_root_coefficient_values))
         (bounded_taylor64_rows_object_cv product product_rows)
         (registered_case10173_constant_object
           (EL index registered_case10173_root_term_values)) /\
       registered_case10173_actual_group_eval_prefix remaining (SUC index)
         center_boxes boxes source_radii fixed_radii center_roots box_roots
         certificates) /\
  registered_case10173_actual_group_eval_prefix
      (SUC remaining) index center_boxes boxes source_radii fixed_radii
      center_roots box_roots certificates = F
End

Theorem registered_case10173_actual_group_eval_prefix_sound:
  !remaining index center_roots box_roots certificates.
    LENGTH radii = 6 /\
    LENGTH center_environment = 6 /\
    LENGTH dimensions = 6 /\
    index + remaining <= 6 /\
    bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME center_environment /\
    registered_case10173_eval_above 8208
      (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
      (bounded_interval64_object_cv_list dimensions) /\
    registered_case10173_eval_above 8208
      (App «candle_cv_fs_list_of_q» [from_cv source_radii])
      (registered_case10173_word64_object_cv_list radii) /\
    bounded_case10173_actual_sqrt_source_prefix_exact remaining index radii
      center_environment center_roots box_roots certificates ==>
    registered_case10173_actual_group_eval_prefix remaining index center_boxes
      boxes source_radii
      (registered_case10173_word64_object_cv_list radii)
      center_roots box_roots certificates
Proof
  Induct_on `remaining`
  >- simp [registered_case10173_actual_group_eval_prefix_def]
  >> rpt gen_tac
  >> Cases_on `center_roots`
  >- simp
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> Cases_on `box_roots`
  >- simp
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> Cases_on `certificates`
  >- simp
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> strip_tac
  >> Cases_on `h`
  >> `index < 6` by intLib.ARITH_TAC
  >> drule_all_then strip_assume_tac
       registered_case10173_actual_group_numeric_contract
  >> qpat_x_assum `!boxes. _` (qspec_then `boxes` strip_assume_tac)
  >> simp [registered_case10173_actual_group_eval_prefix_def]
  >> fs
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> Cases_on `variable`
  >> gvs
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem registered_case10173_actual_six_group_eval_prefix:
  LENGTH radii = 6 /\
  LENGTH center_environment = 6 /\
  LENGTH dimensions = 6 /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
    SOME center_environment /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
    (bounded_interval64_object_cv_list dimensions) /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_list_of_q» [from_cv source_radii])
    (registered_case10173_word64_object_cv_list radii) /\
  bounded_case10173_actual_sqrt_source_prefix_exact 6 0 radii
    center_environment center_roots box_roots certificates ==>
  registered_case10173_actual_group_eval_prefix 6 0 center_boxes boxes
    source_radii (registered_case10173_word64_object_cv_list radii)
    center_roots box_roots certificates
Proof
  strip_tac
  >> irule registered_case10173_actual_group_eval_prefix_sound
  >> simp []
  >> qexists_tac `dimensions`
  >> asm_rewrite_tac []
  >> qexists_tac `center_environment`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
