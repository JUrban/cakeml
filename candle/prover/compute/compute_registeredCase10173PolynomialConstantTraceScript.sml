(*****************************************************************************
 * Exact constant-only polynomial traces in the literal case-10173 source.
 *
 * The nine coefficient/term programs contain only rational constants,
 * negation, and multiplication.  All of their rationals are exact at the
 * historical 10^12 scale.  This layer proves once that completing a constant
 * Taylor state is independent of the six radii, then uses the registered
 * constant/negation/multiplication instructions to authenticate the literal
 * postfix programs.
 *****************************************************************************)
Theory compute_registeredCase10173PolynomialConstantTrace
Ancestors
  compute_registeredCase10173PolynomialNegStepEval
  compute_registeredCase10173OrdinarySourceTemplateEval
Libs
  bossLib preamble intLib

Definition registered_case10173_decimal_point_def:
  registered_case10173_decimal_point negative magnitude =
    BoundedInterval64
      (BoundedSigned64 negative (n2w magnitude))
      (BoundedSigned64 negative (n2w magnitude))
End

Definition registered_case10173_constant_taylor_def:
  registered_case10173_constant_taylor value =
    BoundedTaylor64 T value
      (REPLICATE 6 bounded_interval64_zero) value
      (REPLICATE 6 bounded_interval64_zero)
      (bounded_interval64_zeros 21)
End

Definition registered_case10173_constant_object_def:
  registered_case10173_constant_object value =
    bounded_taylor64_rows_object_cv
      (registered_case10173_constant_taylor value)
      (REPLICATE 6 (REPLICATE 6 bounded_interval64_zero))
End

Definition registered_case10173_zero_outer_pairs_def:
  registered_case10173_zero_outer_pairs =
    REPLICATE 21
      ((bounded_interval64_zero,bounded_interval64_zero),
       (bounded_interval64_zero,bounded_interval64_zero))
End

Definition registered_case10173_ordinary_term0_value_def:
  registered_case10173_ordinary_term0_value =
    registered_case10173_decimal_point F 1277000000000
End


Definition registered_case10173_ordinary_coefficient0_value_def:
  registered_case10173_ordinary_coefficient0_value =
    registered_case10173_decimal_point F 273298000000
End

Definition registered_case10173_ordinary_term1_value_def:
  registered_case10173_ordinary_term1_value =
    registered_case10173_decimal_point T 595789640000
End

Definition registered_case10173_ordinary_coefficient12_value_def:
  registered_case10173_ordinary_coefficient12_value =
    registered_case10173_decimal_point T 273853000000
End

Definition registered_case10173_ordinary_term23_value_def:
  registered_case10173_ordinary_term23_value =
    registered_case10173_decimal_point F 547706000000
End

Definition registered_case10173_ordinary_coefficient3_value_def:
  registered_case10173_ordinary_coefficient3_value =
    registered_case10173_decimal_point F 708818000000
End

Definition registered_case10173_ordinary_term4_value_def:
  registered_case10173_ordinary_term4_value =
    registered_case10173_decimal_point T 1417636000000
End

Definition registered_case10173_ordinary_coefficient45_value_def:
  registered_case10173_ordinary_coefficient45_value =
    registered_case10173_decimal_point T 313988000000
End

Definition registered_case10173_ordinary_term56_value_def:
  registered_case10173_ordinary_term56_value =
    registered_case10173_decimal_point F 627976000000
End

Definition registered_case10173_polynomial_constant_values_def:
  registered_case10173_polynomial_constant_values =
    [registered_case10173_decimal_point F 1000000000000;
     registered_case10173_decimal_point F 1277000000000;
     registered_case10173_decimal_point F 273298000000;
     registered_case10173_decimal_point F 2180000000000;
     registered_case10173_decimal_point F 273853000000;
     registered_case10173_decimal_point F 2000000000000;
     registered_case10173_decimal_point F 708818000000;
     registered_case10173_decimal_point F 313988000000;
     registered_case10173_decimal_point T 1000000000000;
     registered_case10173_decimal_point T 2180000000000;
     registered_case10173_decimal_point T 273853000000;
     registered_case10173_decimal_point T 2000000000000;
     registered_case10173_decimal_point T 313988000000;
     registered_case10173_ordinary_term1_value;
     registered_case10173_ordinary_term23_value;
     registered_case10173_ordinary_term4_value;
     registered_case10173_ordinary_term56_value]
End

Theorem registered_case10173_zero_taylor_error_decimal:
  LENGTH radii = 6 ==>
  bounded_taylor_error_decimal radii
      (REPLICATE 6 bounded_interval64_zero)
      (bounded_interval64_zeros 21) = SOME bounded192_zero
Proof
  strip_tac
  >> fs [listTheory.LENGTH_EQ_NUM_compute]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_zero_taylor_gradient_decimal:
  LENGTH radii = 6 ==>
  bounded_taylor_gradient_complete_decimal radii
      (REPLICATE 6 bounded_interval64_zero)
      (bounded_interval64_zeros 21) =
    SOME (REPLICATE 6 bounded_interval64_zero)
Proof
  strip_tac
  >> fs [listTheory.LENGTH_EQ_NUM_compute]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_taylor_complete_decimal_values:
  LENGTH radii = 6 ==>
  EVERY
    (\value.
      bounded_taylor64_complete_decimal radii T value
        (REPLICATE 6 bounded_interval64_zero)
        (bounded_interval64_zeros 21) =
      SOME (registered_case10173_constant_taylor value))
    registered_case10173_polynomial_constant_values
Proof
  strip_tac
  >> `bounded_taylor_error_decimal radii
        (REPLICATE 6 bounded_interval64_zero)
        (bounded_interval64_zeros 21) = SOME bounded192_zero` by
       metis_tac [registered_case10173_zero_taylor_error_decimal]
  >> `bounded_taylor_gradient_complete_decimal radii
        (REPLICATE 6 bounded_interval64_zero)
        (bounded_interval64_zeros 21) =
      SOME (REPLICATE 6 bounded_interval64_zero)` by
       metis_tac [registered_case10173_zero_taylor_gradient_decimal]
  >> simp
       [registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_term1_value_def,
        registered_case10173_ordinary_term23_value_def,
        registered_case10173_ordinary_term4_value_def,
        registered_case10173_ordinary_term56_value_def,
        compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_def,
        compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_value_complete_decimal_def,
        compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
        compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def,
        registered_case10173_constant_taylor_def,
        registered_case10173_decimal_point_def,
        compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def,
        compute_boundedIntervalListTheory.bounded_interval64_zero_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_taylor_complete_decimal_member:
  LENGTH radii = 6 /\
  MEM value registered_case10173_polynomial_constant_values ==>
  bounded_taylor64_complete_decimal radii T value
      (REPLICATE 6 bounded_interval64_zero)
      (bounded_interval64_zeros 21) =
    SOME (registered_case10173_constant_taylor value)
Proof
  strip_tac
  >> drule registered_case10173_constant_taylor_complete_decimal_values
  >> fs [listTheory.EVERY_MEM]
QED

Theorem registered_case10173_source_constant_decimal_values:
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 1) (Num 0)) (Num 0)) =
    SOME (registered_case10173_decimal_point F 1000000000000) /\
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 1277) (Num 0)) (Num 999)) =
    SOME registered_case10173_ordinary_term0_value /\
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 136649) (Num 0)) (Num 499999)) =
    SOME registered_case10173_ordinary_coefficient0_value /\
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 109) (Num 0)) (Num 49)) =
    SOME (registered_case10173_decimal_point F 2180000000000) /\
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 273853) (Num 0)) (Num 999999)) =
    SOME (registered_case10173_decimal_point F 273853000000) /\
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 2) (Num 0)) (Num 0)) =
    SOME (registered_case10173_decimal_point F 2000000000000) /\
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 354409) (Num 0)) (Num 499999)) =
    SOME registered_case10173_ordinary_coefficient3_value /\
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 78497) (Num 0)) (Num 249999)) =
    SOME (registered_case10173_decimal_point F 313988000000) /\
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 0) (Num 1)) (Num 0)) =
    SOME (registered_case10173_decimal_point T 1000000000000)
Proof
  EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
  >> simp (CONJUNCTS
       (DB.fetch "compute_boundedObjectDecimalQ"
          "bounded_object_positive_q_floor64_decimal_compute"))
QED

Theorem registered_case10173_zero_hessian_rows_constant:
  bounded_hessian64_rows (bounded_interval64_zeros 21) =
    SOME (REPLICATE 6 (REPLICATE 6 bounded_interval64_zero))
Proof
  EVAL_TAC
QED

Theorem registered_case10173_constant_object_eval_above:
  LENGTH dimensions = 6 /\
  LENGTH radii = 6 /\
  bounded_object_q_constant_interval64_decimal encoded = SOME value /\
  MEM value registered_case10173_polynomial_constant_values ==>
  registered_case10173_eval_above 8192
      (App «candle_cv_fs_result_constant»
        [from_cv (bounded_interval64_object_cv_list dimensions);
         from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv encoded])
      (registered_case10173_constant_object value)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173PolynomialTraceEvalTheory.registered_case10173_fs_result_constant_object_eval_above
  >> simp []
  >> conj_tac
  >- (simp [registered_case10173_constant_object_def]
      >> irule
           compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_complete_exact
      >> simp
           [registered_case10173_constant_taylor_complete_decimal_member,
            registered_case10173_zero_hessian_rows_constant])
  >> simp [registered_case10173_zero_hessian_rows_constant]
QED

Theorem registered_case10173_constant_step_eval_above:
  LENGTH dimensions = 6 /\
  LENGTH radii = 6 /\
  bounded_object_q_constant_interval64_decimal encoded = SOME value /\
  MEM value registered_case10173_polynomial_constant_values ==>
  registered_case10173_poly_step_eval_above 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      (Pair (Num 0) encoded) stack
      (Pair (registered_case10173_constant_object value) stack)
Proof
  strip_tac
  >> irule
       (SIMP_RULE arith_ss []
         (Q.INST [`result_floor` |-> `8192`]
           compute_registeredCase10173PolynomialTraceEvalTheory.registered_case10173_poly_constant_step_eval_above))
  >> irule registered_case10173_constant_object_eval_above
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_constant_taylor_well_formed:
  MEM value registered_case10173_polynomial_constant_values ==>
  bounded_taylor64_well_formed
    (registered_case10173_constant_taylor value)
Proof
  strip_tac
  >> `bounded_taylor64_complete_decimal
        (REPLICATE 6 (0w:word64)) T value
        (REPLICATE 6 bounded_interval64_zero)
        (bounded_interval64_zeros 21) =
      SOME (registered_case10173_constant_taylor value)` by
       (irule registered_case10173_constant_taylor_complete_decimal_member
        >> simp [])
  >> imp_res_tac
       compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_some
QED

Theorem registered_case10173_constant_mul_from_components:
  LENGTH radii = 6 /\
  MEM left registered_case10173_polynomial_constant_values /\
  MEM right registered_case10173_polynomial_constant_values /\
  MEM result registered_case10173_polynomial_constant_values /\
  bounded_interval64_mul_decimal left right = SOME result /\
  bounded_interval64_fused_scale_add_decimal right
      (REPLICATE 6 bounded_interval64_zero) left
      (REPLICATE 6 bounded_interval64_zero) =
    SOME (REPLICATE 6 bounded_interval64_zero) /\
  bounded_interval64_symmetric_product_pairs
      (REPLICATE 6 bounded_interval64_zero)
      (REPLICATE 6 bounded_interval64_zero) =
    SOME registered_case10173_zero_outer_pairs /\
  bounded_interval64_fused_hessian_decimal left right
      (bounded_interval64_zeros 21) (bounded_interval64_zeros 21)
      registered_case10173_zero_outer_pairs =
    SOME (bounded_interval64_zeros 21) ==>
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor left)
      (registered_case10173_constant_taylor right) =
    SOME (registered_case10173_constant_taylor result)
Proof
  strip_tac
  >> `bounded_taylor64_well_formed
        (registered_case10173_constant_taylor left)` by
       (irule registered_case10173_constant_taylor_well_formed
        >> asm_rewrite_tac [])
  >> `bounded_taylor64_well_formed
        (registered_case10173_constant_taylor right)` by
       (irule registered_case10173_constant_taylor_well_formed
        >> asm_rewrite_tac [])
  >> rw
       [compute_boundedTaylorMulDecimalTheory.bounded_taylor64_mul_decimal_def]
  >> PURE_REWRITE_TAC [registered_case10173_constant_taylor_def]
  >> simp []
  >> PURE_REWRITE_TAC [GSYM registered_case10173_constant_taylor_def]
  >> irule registered_case10173_constant_taylor_complete_decimal_member
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_constant_mul_term0:
  LENGTH radii = 6 ==>
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point F 1000000000000))
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term0_value) =
    SOME
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term0_value)
Proof
  strip_tac
  >> irule registered_case10173_constant_mul_from_components
  >> asm_rewrite_tac []
  >> simp
       [registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_term0_value_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_mul_term1_inner:
  LENGTH radii = 6 ==>
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_coefficient0_value)
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point T 2180000000000)) =
    SOME
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term1_value)
Proof
  strip_tac
  >> irule registered_case10173_constant_mul_from_components
  >> asm_rewrite_tac []
  >> simp
       [registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_coefficient0_value_def,
        registered_case10173_ordinary_term1_value_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_mul_term1_outer:
  LENGTH radii = 6 ==>
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point F 1000000000000))
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term1_value) =
    SOME
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term1_value)
Proof
  strip_tac
  >> irule registered_case10173_constant_mul_from_components
  >> asm_rewrite_tac []
  >> simp
       [registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_term1_value_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_mul_term23_inner:
  LENGTH radii = 6 ==>
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point F 273853000000))
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point F 2000000000000)) =
    SOME
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term23_value)
Proof
  strip_tac
  >> irule registered_case10173_constant_mul_from_components
  >> asm_rewrite_tac []
  >> simp
       [registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_term23_value_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_mul_term23_outer:
  LENGTH radii = 6 ==>
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point F 1000000000000))
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term23_value) =
    SOME
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term23_value)
Proof
  strip_tac
  >> irule registered_case10173_constant_mul_from_components
  >> asm_rewrite_tac []
  >> simp
       [registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_term23_value_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_mul_term4_inner:
  LENGTH radii = 6 ==>
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_coefficient3_value)
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point T 2000000000000)) =
    SOME
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term4_value)
Proof
  strip_tac
  >> irule registered_case10173_constant_mul_from_components
  >> asm_rewrite_tac []
  >> simp
       [registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_coefficient3_value_def,
        registered_case10173_ordinary_term4_value_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_mul_term4_outer:
  LENGTH radii = 6 ==>
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point F 1000000000000))
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term4_value) =
    SOME
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term4_value)
Proof
  strip_tac
  >> irule registered_case10173_constant_mul_from_components
  >> asm_rewrite_tac []
  >> simp
       [registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_term4_value_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_mul_term56_inner:
  LENGTH radii = 6 ==>
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point F 313988000000))
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point F 2000000000000)) =
    SOME
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term56_value)
Proof
  strip_tac
  >> irule registered_case10173_constant_mul_from_components
  >> asm_rewrite_tac []
  >> simp
       [registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_term56_value_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_mul_term56_outer:
  LENGTH radii = 6 ==>
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point F 1000000000000))
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term56_value) =
    SOME
      (registered_case10173_constant_taylor
        registered_case10173_ordinary_term56_value)
Proof
  strip_tac
  >> irule registered_case10173_constant_mul_from_components
  >> asm_rewrite_tac []
  >> simp
       [registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_term56_value_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_constant_neg_literal_values:
  bounded_interval64_neg
      (registered_case10173_decimal_point F 2180000000000) =
    registered_case10173_decimal_point T 2180000000000 /\
  bounded_interval64_neg
      (registered_case10173_decimal_point F 273853000000) =
    registered_case10173_ordinary_coefficient12_value /\
  bounded_interval64_neg
      (registered_case10173_decimal_point F 2000000000000) =
    registered_case10173_decimal_point T 2000000000000 /\
  bounded_interval64_neg
      (registered_case10173_decimal_point F 313988000000) =
    registered_case10173_ordinary_coefficient45_value
Proof
  EVAL_TAC
QED

Theorem registered_case10173_constant_mul_eval_above:
  LENGTH radii = 6 /\
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor left)
      (registered_case10173_constant_taylor right) =
    SOME (registered_case10173_constant_taylor result) ==>
  registered_case10173_eval_above 8192
      (App «candle_cv_fs_result_mul»
        [from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv (registered_case10173_constant_object left);
         from_cv (registered_case10173_constant_object right)])
      (registered_case10173_constant_object result)
Proof
  strip_tac
  >> PURE_REWRITE_TAC [registered_case10173_constant_object_def]
  >> PURE_REWRITE_TAC [registered_case10173_constant_taylor_def]
  >> irule
       compute_registeredCase10173ResultMulAboveEvalTheory.registered_case10173_taylor_mul_decimal_eval_above
  >> simp [registered_case10173_zero_hessian_rows_constant]
  >> PURE_REWRITE_TAC [GSYM registered_case10173_constant_taylor_def]
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_constant_mul_step_eval_above:
  LENGTH radii = 6 /\
  bounded_taylor64_mul_decimal radii
      (registered_case10173_constant_taylor left)
      (registered_case10173_constant_taylor right) =
    SOME (registered_case10173_constant_taylor result) ==>
  registered_case10173_poly_step_eval_above 8194 dimensions
      (registered_case10173_word64_object_cv_list radii) (Num 4)
      (Pair (registered_case10173_constant_object right)
        (Pair (registered_case10173_constant_object left) stack_tail))
      (Pair (registered_case10173_constant_object result) stack_tail)
Proof
  strip_tac
  >> irule
       (SIMP_RULE arith_ss []
         (Q.INST [`result_floor` |-> `8192`]
           compute_registeredCase10173PolynomialMulStepEvalTheory.registered_case10173_poly_mul_step_eval_above))
  >> irule registered_case10173_constant_mul_eval_above
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_constant_neg_from_components:
  LENGTH radii = 6 /\
  MEM result registered_case10173_polynomial_constant_values /\
  bounded_interval64_neg source = result ==>
  bounded_taylor64_complete_decimal radii T
      (bounded_interval64_neg source)
      (bounded_interval64_list_neg
        (REPLICATE 6 bounded_interval64_zero))
      (bounded_interval64_list_neg (bounded_interval64_zeros 21)) =
    SOME (registered_case10173_constant_taylor result)
Proof
  strip_tac
  >> `bounded_interval64_list_neg
        (REPLICATE 6 bounded_interval64_zero) =
      REPLICATE 6 bounded_interval64_zero` by EVAL_TAC
  >> `bounded_interval64_list_neg (bounded_interval64_zeros 21) =
      bounded_interval64_zeros 21` by EVAL_TAC
  >> asm_rewrite_tac []
  >> irule registered_case10173_constant_taylor_complete_decimal_member
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_zero_hessian_rows_neg:
  MAP bounded_interval64_list_neg
      (REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)) =
    REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_zero_gradient_neg:
  bounded_interval64_list_neg
      (REPLICATE 6 bounded_interval64_zero) =
    REPLICATE 6 bounded_interval64_zero
Proof
  EVAL_TAC
QED

Theorem registered_case10173_zero_hessian_values_neg:
  bounded_interval64_list_neg (bounded_interval64_zeros 21) =
    bounded_interval64_zeros 21
Proof
  EVAL_TAC
QED

Theorem registered_case10173_constant_neg_eval_above:
  LENGTH radii = 6 /\
  MEM result registered_case10173_polynomial_constant_values /\
  bounded_interval64_neg source = result ==>
  registered_case10173_eval_above 8192
      (App «candle_cv_fs_result_neg»
        [from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv (registered_case10173_constant_object source)])
      (registered_case10173_constant_object result)
Proof
  strip_tac
  >> PURE_REWRITE_TAC [registered_case10173_constant_object_def]
  >> PURE_REWRITE_TAC [registered_case10173_constant_taylor_def]
  >> irule
       (SIMP_RULE std_ss [registered_case10173_zero_hessian_rows_neg]
         (Q.INST
           [`source_rows` |->
              `REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)`]
           compute_registeredCase10173PolynomialNegStepEvalTheory.registered_case10173_taylor_neg_decimal_eval_above))
  >> simp
       [registered_case10173_zero_hessian_rows_constant,
        registered_case10173_zero_gradient_neg,
        registered_case10173_zero_hessian_values_neg]
  >> PURE_REWRITE_TAC [GSYM registered_case10173_constant_taylor_def]
  >> irule registered_case10173_constant_taylor_complete_decimal_member
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_constant_neg_step_eval_above:
  LENGTH radii = 6 /\
  MEM result registered_case10173_polynomial_constant_values /\
  bounded_interval64_neg source = result ==>
  registered_case10173_poly_step_eval_above 8194 dimensions
      (registered_case10173_word64_object_cv_list radii) (Num 2)
      (Pair (registered_case10173_constant_object source) stack_tail)
      (Pair (registered_case10173_constant_object result) stack_tail)
Proof
  strip_tac
  >> irule
       (SIMP_RULE arith_ss []
         (Q.INST [`result_floor` |-> `8192`]
           compute_registeredCase10173PolynomialNegStepEvalTheory.registered_case10173_poly_neg_step_eval_above))
  >> irule registered_case10173_constant_neg_eval_above
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_literal_constant_steps:
  LENGTH dimensions = 6 /\ LENGTH radii = 6 ==>
  (!stack. registered_case10173_poly_step_eval_above 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0))) stack
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 1000000000000)) stack)) /\
  (!stack. registered_case10173_poly_step_eval_above 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      (Pair (Num 0) (Pair (Pair (Num 1277) (Num 0)) (Num 999))) stack
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term0_value) stack)) /\
  (!stack. registered_case10173_poly_step_eval_above 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      (Pair (Num 0) (Pair (Pair (Num 136649) (Num 0)) (Num 499999))) stack
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient0_value) stack)) /\
  (!stack. registered_case10173_poly_step_eval_above 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      (Pair (Num 0) (Pair (Pair (Num 109) (Num 0)) (Num 49))) stack
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 2180000000000)) stack)) /\
  (!stack. registered_case10173_poly_step_eval_above 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      (Pair (Num 0) (Pair (Pair (Num 273853) (Num 0)) (Num 999999))) stack
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 273853000000)) stack)) /\
  (!stack. registered_case10173_poly_step_eval_above 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      (Pair (Num 0) (Pair (Pair (Num 2) (Num 0)) (Num 0))) stack
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 2000000000000)) stack)) /\
  (!stack. registered_case10173_poly_step_eval_above 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      (Pair (Num 0) (Pair (Pair (Num 354409) (Num 0)) (Num 499999))) stack
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient3_value) stack)) /\
  (!stack. registered_case10173_poly_step_eval_above 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      (Pair (Num 0) (Pair (Pair (Num 78497) (Num 0)) (Num 249999))) stack
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 313988000000)) stack))
Proof
  strip_tac
  >> rpt conj_tac
  >> gen_tac
  >> irule registered_case10173_constant_step_eval_above
  >> simp
       [registered_case10173_source_constant_decimal_values,
        registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_term0_value_def,
        registered_case10173_ordinary_coefficient0_value_def,
        registered_case10173_ordinary_coefficient3_value_def]
QED

Theorem registered_case10173_literal_neg_steps:
  LENGTH radii = 6 ==>
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 2)
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 2180000000000)) stack)
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point T 2180000000000)) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 2)
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 273853000000)) stack)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient12_value) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 2)
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 2000000000000)) stack)
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point T 2000000000000)) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 2)
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 313988000000)) stack)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient45_value) stack))
Proof
  strip_tac
  >> rpt conj_tac
  >> rpt gen_tac
  >> irule registered_case10173_constant_neg_step_eval_above
  >> simp
       [registered_case10173_constant_neg_literal_values,
        registered_case10173_polynomial_constant_values_def,
        registered_case10173_ordinary_coefficient12_value_def,
        registered_case10173_ordinary_coefficient45_value_def]
QED

Theorem registered_case10173_literal_mul_steps:
  LENGTH radii = 6 ==>
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 4)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term0_value)
        (Pair (registered_case10173_constant_object
          (registered_case10173_decimal_point F 1000000000000)) stack))
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term0_value) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 4)
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point T 2180000000000))
        (Pair (registered_case10173_constant_object
          registered_case10173_ordinary_coefficient0_value) stack))
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term1_value) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 4)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term1_value)
        (Pair (registered_case10173_constant_object
          (registered_case10173_decimal_point F 1000000000000)) stack))
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term1_value) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 4)
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 2000000000000))
        (Pair (registered_case10173_constant_object
          (registered_case10173_decimal_point F 273853000000)) stack))
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term23_value) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 4)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term23_value)
        (Pair (registered_case10173_constant_object
          (registered_case10173_decimal_point F 1000000000000)) stack))
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term23_value) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 4)
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point T 2000000000000))
        (Pair (registered_case10173_constant_object
          registered_case10173_ordinary_coefficient3_value) stack))
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term4_value) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 4)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term4_value)
        (Pair (registered_case10173_constant_object
          (registered_case10173_decimal_point F 1000000000000)) stack))
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term4_value) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 4)
      (Pair (registered_case10173_constant_object
        (registered_case10173_decimal_point F 2000000000000))
        (Pair (registered_case10173_constant_object
          (registered_case10173_decimal_point F 313988000000)) stack))
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term56_value) stack)) /\
  (!dimensions stack. registered_case10173_poly_step_eval_above 8194
      dimensions (registered_case10173_word64_object_cv_list radii) (Num 4)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term56_value)
        (Pair (registered_case10173_constant_object
          (registered_case10173_decimal_point F 1000000000000)) stack))
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term56_value) stack))
Proof
  strip_tac
  >> rpt conj_tac
  >> rpt gen_tac
  >> irule registered_case10173_constant_mul_step_eval_above
  >> conj_tac >- asm_rewrite_tac []
  >> metis_tac
       [registered_case10173_constant_mul_term0,
        registered_case10173_constant_mul_term1_inner,
        registered_case10173_constant_mul_term1_outer,
        registered_case10173_constant_mul_term23_inner,
        registered_case10173_constant_mul_term23_outer,
        registered_case10173_constant_mul_term4_inner,
        registered_case10173_constant_mul_term4_outer,
        registered_case10173_constant_mul_term56_inner,
        registered_case10173_constant_mul_term56_outer]
QED

Theorem registered_case10173_ordinary_term0_program_trace:
  LENGTH dimensions = 6 /\ LENGTH radii = 6 ==>
  registered_case10173_poly_program_trace 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      registered_case10173_ordinary_term0_program (Num 0)
      (Pair
        (registered_case10173_constant_object
          registered_case10173_ordinary_term0_value)
        (Num 0))
Proof
  strip_tac
  >> `registered_case10173_poly_step_eval_above 8194
        (bounded_interval64_object_cv_list dimensions)
        (registered_case10173_word64_object_cv_list radii)
        (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
        (Num 0)
        (Pair
          (registered_case10173_constant_object
            (registered_case10173_decimal_point F 1000000000000))
          (Num 0))` by
       (irule registered_case10173_constant_step_eval_above
        >> simp
             [registered_case10173_source_constant_decimal_values,
              registered_case10173_polynomial_constant_values_def,
              registered_case10173_ordinary_term0_value_def])
  >> `registered_case10173_poly_step_eval_above 8194
        (bounded_interval64_object_cv_list dimensions)
        (registered_case10173_word64_object_cv_list radii)
        (Pair (Num 0) (Pair (Pair (Num 1277) (Num 0)) (Num 999)))
        (Pair
          (registered_case10173_constant_object
            (registered_case10173_decimal_point F 1000000000000))
          (Num 0))
        (Pair
          (registered_case10173_constant_object
            registered_case10173_ordinary_term0_value)
          (Pair
            (registered_case10173_constant_object
              (registered_case10173_decimal_point F 1000000000000))
            (Num 0)))` by
       (irule registered_case10173_constant_step_eval_above
        >> simp
             [registered_case10173_source_constant_decimal_values,
              registered_case10173_polynomial_constant_values_def,
              registered_case10173_ordinary_term0_value_def])
  >> `registered_case10173_poly_step_eval_above 8194
        (bounded_interval64_object_cv_list dimensions)
        (registered_case10173_word64_object_cv_list radii) (Num 4)
        (Pair
          (registered_case10173_constant_object
            registered_case10173_ordinary_term0_value)
          (Pair
            (registered_case10173_constant_object
              (registered_case10173_decimal_point F 1000000000000))
            (Num 0)))
        (Pair
          (registered_case10173_constant_object
            registered_case10173_ordinary_term0_value)
          (Num 0))` by
       (irule registered_case10173_constant_mul_step_eval_above
        >> conj_tac >- asm_rewrite_tac []
        >> irule registered_case10173_constant_mul_term0
        >> asm_rewrite_tac [])
  >> simp
       [compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_term0_program_def,
        compute_registeredCase10173PolynomialTraceEvalTheory.registered_case10173_poly_program_trace_def]
  >> metis_tac []
QED

Theorem registered_case10173_remaining_literal_program_traces:
  LENGTH dimensions = 6 /\ LENGTH radii = 6 ==>
  registered_case10173_poly_program_trace 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      registered_case10173_ordinary_coefficient0_program (Num 0)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient0_value) (Num 0)) /\
  registered_case10173_poly_program_trace 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      registered_case10173_ordinary_term1_program (Num 0)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term1_value) (Num 0)) /\
  registered_case10173_poly_program_trace 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      registered_case10173_ordinary_coefficient12_program (Num 0)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient12_value) (Num 0)) /\
  registered_case10173_poly_program_trace 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      registered_case10173_ordinary_term23_program (Num 0)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term23_value) (Num 0)) /\
  registered_case10173_poly_program_trace 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      registered_case10173_ordinary_coefficient3_program (Num 0)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient3_value) (Num 0)) /\
  registered_case10173_poly_program_trace 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      registered_case10173_ordinary_term4_program (Num 0)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term4_value) (Num 0)) /\
  registered_case10173_poly_program_trace 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      registered_case10173_ordinary_coefficient45_program (Num 0)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient45_value) (Num 0)) /\
  registered_case10173_poly_program_trace 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      registered_case10173_ordinary_term56_program (Num 0)
      (Pair (registered_case10173_constant_object
        registered_case10173_ordinary_term56_value) (Num 0))
Proof
  strip_tac
  >> rpt conj_tac
  >> simp
       [compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_coefficient0_program_def,
        compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_term1_program_def,
        compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_coefficient12_program_def,
        compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_term23_program_def,
        compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_coefficient3_program_def,
        compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_term4_program_def,
        compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_coefficient45_program_def,
        compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_term56_program_def,
        compute_registeredCase10173PolynomialTraceEvalTheory.registered_case10173_poly_program_trace_def]
  >> metis_tac
       [registered_case10173_literal_constant_steps,
        registered_case10173_literal_neg_steps,
        registered_case10173_literal_mul_steps]
QED

Theorem registered_case10173_literal_program_lengths:
  registered_case10173_cv_list_length
      registered_case10173_ordinary_term0_program = 3 /\
  registered_case10173_cv_list_length
      registered_case10173_ordinary_coefficient0_program = 1 /\
  registered_case10173_cv_list_length
      registered_case10173_ordinary_term1_program = 6 /\
  registered_case10173_cv_list_length
      registered_case10173_ordinary_coefficient12_program = 2 /\
  registered_case10173_cv_list_length
      registered_case10173_ordinary_term23_program = 5 /\
  registered_case10173_cv_list_length
      registered_case10173_ordinary_coefficient3_program = 1 /\
  registered_case10173_cv_list_length
      registered_case10173_ordinary_term4_program = 6 /\
  registered_case10173_cv_list_length
      registered_case10173_ordinary_coefficient45_program = 2 /\
  registered_case10173_cv_list_length
      registered_case10173_ordinary_term56_program = 5
Proof
  simp
    [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def,
     compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_term0_program_def,
     compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_coefficient0_program_def,
     compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_term1_program_def,
     compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_coefficient12_program_def,
     compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_term23_program_def,
     compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_coefficient3_program_def,
     compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_term4_program_def,
     compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_coefficient45_program_def,
     compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_ordinary_term56_program_def]
QED

Theorem registered_case10173_literal_programs_eval_above:
  LENGTH dimensions = 6 /\ LENGTH radii = 6 /\
  registered_case10173_eval_above 8208
      (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
      (bounded_interval64_object_cv_list dimensions) /\
  registered_case10173_eval_above 8208
      (App «candle_cv_fs_list_of_q» [from_cv source_radii])
      (registered_case10173_word64_object_cv_list radii) ==>
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv registered_case10173_ordinary_term0_program])
      (registered_case10173_constant_object
        registered_case10173_ordinary_term0_value) /\
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv registered_case10173_ordinary_coefficient0_program])
      (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient0_value) /\
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv registered_case10173_ordinary_term1_program])
      (registered_case10173_constant_object
        registered_case10173_ordinary_term1_value) /\
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv registered_case10173_ordinary_coefficient12_program])
      (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient12_value) /\
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv registered_case10173_ordinary_term23_program])
      (registered_case10173_constant_object
        registered_case10173_ordinary_term23_value) /\
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv registered_case10173_ordinary_coefficient3_program])
      (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient3_value) /\
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv registered_case10173_ordinary_term4_program])
      (registered_case10173_constant_object
        registered_case10173_ordinary_term4_value) /\
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv registered_case10173_ordinary_coefficient45_program])
      (registered_case10173_constant_object
        registered_case10173_ordinary_coefficient45_value) /\
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv registered_case10173_ordinary_term56_program])
      (registered_case10173_constant_object
        registered_case10173_ordinary_term56_value)
Proof
  strip_tac
  >> imp_res_tac registered_case10173_ordinary_term0_program_trace
  >> imp_res_tac registered_case10173_remaining_literal_program_traces
  >> rpt conj_tac
  >> irule
       (SIMP_RULE arith_ss []
         (Q.INST
           [`conversion_floor` |-> `8208`,
            `step_floor` |-> `8194`,
           `numeric_floor` |-> `8208`]
           compute_registeredCase10173PolynomialTraceEvalTheory.registered_case10173_poly_program_eval_above_from_trace))
  >> simp [registered_case10173_literal_program_lengths]
  >> qexists_tac `bounded_interval64_object_cv_list dimensions`
  >> qexists_tac `registered_case10173_word64_object_cv_list radii`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
