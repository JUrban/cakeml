(*****************************************************************************
 * Typed stack identity for the genuine 31-instruction case-10173 prefix.
 *
 * The existing prefix trace pins all six genuine products, but states its
 * result using the row witnesses produced while evaluating them.  The
 * literal-source checker instead carries typed Taylor states.  This layer
 * identifies the seven fixed source constants and rewrites the full
 * thirteen-element prefix stack to the canonical typed Taylor objects used
 * by the suffix contract.
 *****************************************************************************)
Theory compute_registeredCase10173LiteralPrefixStackEval
Ancestors
  compute_registeredCase10173LiteralSuffixContractEval
  compute_registeredCase10173ActualSourcePrefixEval
Libs
  bossLib preamble

Theorem registered_case10173_constant_taylor_constructor_member:
  MEM value registered_case10173_polynomial_constant_values ==>
  bounded_taylor64_constant value =
    SOME (registered_case10173_constant_taylor value)
Proof
  strip_tac
  >> `bounded_taylor64_well_formed
        (registered_case10173_constant_taylor value)` by
       (irule
          compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_constant_taylor_well_formed
        >> asm_rewrite_tac [])
  >> `bounded_interval64_zeros 6 =
        REPLICATE 6 bounded_interval64_zero /\
      bounded_interval64_zeros 21 =
        REPLICATE 21 bounded_interval64_zero` by EVAL_TAC
  >> fs
       [compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def,
        compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
        compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_constant_taylor_def,
        compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def]
QED

Theorem registered_case10173_literal_constant_value_identities:
  bounded_case10173_literal_term0_decimal =
      registered_case10173_ordinary_term0_value /\
  bounded_case10173_literal_term1_decimal =
      registered_case10173_ordinary_term1_value /\
  bounded_case10173_literal_term23_decimal =
      registered_case10173_ordinary_term23_value /\
  bounded_case10173_literal_term4_decimal =
      registered_case10173_ordinary_term4_value /\
  bounded_case10173_literal_term56_decimal =
      registered_case10173_ordinary_term56_value /\
  bounded_case10173_literal_negative_one_decimal =
      registered_case10173_decimal_point T 1000000000000
Proof
  simp
    [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_term0_decimal_def,
     compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_term1_decimal_def,
     compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_term23_decimal_def,
     compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_term4_decimal_def,
     compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_term56_decimal_def,
     compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_negative_one_decimal_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_ordinary_term0_value_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_ordinary_term1_value_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_ordinary_term23_value_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_ordinary_term4_value_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_ordinary_term56_value_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_decimal_point_def]
QED

Theorem registered_case10173_literal_constants_exact:
  bounded_case10173_literal_constants_decimal =
    SOME
      [registered_case10173_constant_taylor
         registered_case10173_ordinary_term0_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term1_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term23_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term23_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term4_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term56_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term56_value]
Proof
  rw
    [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_constants_decimal_def]
  >> simp
       [registered_case10173_literal_constant_value_identities,
        registered_case10173_constant_taylor_constructor_member,
        compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_polynomial_constant_values_def,
        compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_ordinary_term0_value_def]
QED

Theorem registered_case10173_literal_summands_exact:
  bounded_case10173_literal_summands_decimal
      [product0;product1;product2;product3;product4;product5]
      [registered_case10173_constant_taylor
         registered_case10173_ordinary_term0_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term1_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term23_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term23_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term4_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term56_value;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term56_value] =
    SOME
      [registered_case10173_constant_taylor
         registered_case10173_ordinary_term56_value;
       product5;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term56_value;
       product4;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term4_value;
       product3;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term23_value;
       product2;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term23_value;
       product1;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term1_value;
       product0;
       registered_case10173_constant_taylor
         registered_case10173_ordinary_term0_value]
Proof
  simp
    [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_summands_decimal_def]
QED

Theorem registered_case10173_literal_products_source_prefix_taylor_stack_trace:
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
    center_environment
    (Pair center0
      (Pair center1
        (Pair center2
          (Pair center3 (Pair center4 (Pair center5 (Num 0)))))))
    (Pair box0
      (Pair box1
        (Pair box2
          (Pair box3 (Pair box4 (Pair box5 (Num 0)))))))
    [certificate0;certificate1;certificate2;
     certificate3;certificate4;certificate5] /\
  bounded_case10173_literal_products_decimal 6 0 radii center_environment
    [certificate0;certificate1;certificate2;
     certificate3;certificate4;certificate5] =
    SOME [product0;product1;product2;product3;product4;product5] ==>
  registered_case10173_ordinary_program_trace 8215
    center_boxes boxes source_radii
    (registered_case10173_source_prefix_template
      center0 center1 center2 center3 center4 center5)
    (registered_case10173_source_prefix_template
      box0 box1 box2 box3 box4 box5)
    stack
    (registered_case10173_ordinary_result_stack
      (MAP registered_case10173_taylor_object
        [registered_case10173_constant_taylor
           registered_case10173_ordinary_term56_value;
         product5;
         registered_case10173_constant_taylor
           registered_case10173_ordinary_term56_value;
         product4;
         registered_case10173_constant_taylor
           registered_case10173_ordinary_term4_value;
         product3;
         registered_case10173_constant_taylor
           registered_case10173_ordinary_term23_value;
         product2;
         registered_case10173_constant_taylor
           registered_case10173_ordinary_term23_value;
         product1;
         registered_case10173_constant_taylor
           registered_case10173_ordinary_term1_value;
         product0;
         registered_case10173_constant_taylor
           registered_case10173_ordinary_term0_value])
      stack)
Proof
  strip_tac
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173ActualSourcePrefixEvalTheory.registered_case10173_literal_products_source_prefix_stack_trace
  >> qpat_x_assum `!stack boxes. _`
       (qspecl_then [`stack`,`boxes`] strip_assume_tac)
  >> imp_res_tac
       compute_registeredCase10173LiteralSuffixContractEvalTheory.registered_case10173_taylor_object_from_hessian_rows
  >> simp
       [compute_registeredCase10173LiteralSuffixContractEvalTheory.registered_case10173_constant_taylor_object_exact]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
