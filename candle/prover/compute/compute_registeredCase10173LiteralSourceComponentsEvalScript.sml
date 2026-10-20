(*****************************************************************************
 * Structural and invariant facts for the literal case-10173 source checker.
 *
 * A successful six-product computation determines six true-domain,
 * well-formed Taylor states.  A successful whole literal-source computation
 * also exposes the exact historical multiplication and addition chain that
 * the registered source trace consumes.  These facts are independent of the
 * evaluator composition and keep the final trace proof small.
 *****************************************************************************)
Theory compute_registeredCase10173LiteralSourceComponentsEval
Ancestors
  compute_registeredCase10173LiteralPrefixStackEval
Libs
  bossLib preamble

Theorem registered_case10173_actual_variable_true_domain:
  bounded_case10173_actual_variable_decimal radii center_environment index =
      SOME result ==>
  registered_case10173_taylor_domain result
Proof
  Cases_on `result`
  >> simp
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def]
  >> rw
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_variable_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_registeredCase10173ActualGroupProductEvalTheory.bounded_taylor64_complete_decimal_true_domain
QED

Theorem registered_case10173_constant_true_domain:
  bounded_taylor64_constant value = SOME result ==>
  registered_case10173_taylor_domain result
Proof
  Cases_on `result`
  >> simp
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def]
  >> strip_tac
  >> imp_res_tac
       compute_registeredCase10173ActualGroupProductEvalTheory.bounded_taylor64_constant_true_domain
QED

Theorem registered_case10173_sqrt_true_domain:
  registered_case10173_taylor_domain source /\
  bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal source =
    SOME result ==>
  registered_case10173_taylor_domain result
Proof
  Cases_on `source`
  >> Cases_on `result`
  >> rw
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def]
  >> imp_res_tac
       compute_registeredCase10173ActualGroupProductEvalTheory.bounded_taylor64_sqrt_decimal_true_domain
QED

Theorem registered_case10173_literal_products_length:
  !remaining index certificates products.
    bounded_case10173_literal_products_decimal remaining index radii
        center_environment certificates = SOME products ==>
    LENGTH products = remaining
Proof
  Induct_on `remaining`
  >- (rpt gen_tac
      >> simp
           [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_products_decimal_def])
  >> rpt gen_tac
  >> Cases_on `certificates`
  >- simp
       [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_products_decimal_def]
  >> Cases_on `h`
  >> rw
       [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_products_decimal_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
QED

Theorem registered_case10173_literal_products_properties:
  !remaining index certificates products.
    bounded_case10173_literal_products_decimal remaining index radii
        center_environment certificates = SOME products ==>
    EVERY registered_case10173_taylor_domain products /\
    EVERY bounded_taylor64_well_formed products
Proof
  Induct_on `remaining`
  >- (rpt gen_tac
      >> simp
           [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_products_decimal_def])
  >> rpt gen_tac
  >> Cases_on `certificates`
  >- simp
       [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_products_decimal_def]
  >> Cases_on `h`
  >> rw
       [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_products_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_actual_variable_true_domain
  >> imp_res_tac registered_case10173_sqrt_true_domain
  >> imp_res_tac registered_case10173_constant_true_domain
  >> imp_res_tac
       compute_registeredCase10173LiteralSuffixContractEvalTheory.registered_case10173_taylor_mul_true_domain
  >> imp_res_tac
       compute_boundedTaylorMulDecimalTheory.bounded_taylor64_mul_decimal_some
  >> res_tac
  >> simp []
QED

Theorem registered_case10173_literal_typed_summands_properties:
  EVERY registered_case10173_taylor_domain
      [product0;product1;product2;product3;product4;product5] /\
  EVERY bounded_taylor64_well_formed
      [product0;product1;product2;product3;product4;product5] ==>
  EVERY registered_case10173_taylor_domain
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
         registered_case10173_ordinary_term0_value] /\
  EVERY bounded_taylor64_well_formed
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
  strip_tac
  >> fs []
  >> conj_tac
  >- simp
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def,
        compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_constant_taylor_def]
  >> simp []
  >> rpt conj_tac
  >> irule
       compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_constant_taylor_well_formed
  >> simp
       [compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_polynomial_constant_values_def,
        compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_ordinary_term0_value_def]
QED

Theorem registered_case10173_literal_source_components:
  bounded_case10173_literal_source_decimal
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) =
    SOME final_result ==>
  ?products literal_states summands historical_item negative_one
   scaled_historical.
    bounded_case10173_literal_products_decimal 6 0 radii
      center_environment coordinate_sqrt_certificates = SOME products /\
    bounded_case10173_literal_constants_decimal = SOME literal_states /\
    bounded_case10173_literal_summands_decimal products literal_states =
      SOME summands /\
    bounded_case10173_literal_historical_item_decimal radii
      center_environment box_environment center_root_delta
      center_root_four_x0 center_reciprocals box_root_delta
      box_root_four_x0 box_reciprocals = SOME historical_item /\
    bounded_taylor64_constant
      bounded_case10173_literal_negative_one_decimal = SOME negative_one /\
    bounded_taylor64_mul_decimal radii historical_item negative_one =
      SOME scaled_historical /\
    bounded_case10173_literal_add_stack_decimal radii summands
      scaled_historical = SOME final_result
Proof
  rw
    [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_source_decimal_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

val _ = export_theory ();
