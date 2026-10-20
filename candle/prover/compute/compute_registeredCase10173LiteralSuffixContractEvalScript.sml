(*****************************************************************************
 * Typed numerical contract for the fixed case-10173 source suffix.
 *
 * The genuine source suffix evaluates the literal polynomial [-1],
 * multiplies the authenticated historical item by it, and performs thirteen
 * additions.  This layer relates those source calls to the same typed
 * Taylor states used by the bounded literal-source checker.  In particular,
 * no evaluator result is left as an unrelated existential cv value.
 *****************************************************************************)
Theory compute_registeredCase10173LiteralSuffixContractEval
Ancestors
  compute_registeredCase10173LiteralHistoricalItemEval
  compute_registeredCase10173OrdinarySuffixTraceEval
  compute_registeredCase10173PolynomialConstantTrace
Libs
  bossLib preamble intLib

Theorem registered_case10173_taylor_object_from_hessian_rows:
  bounded_hessian64_rows
      (registered_case10173_taylor_hessian taylor) = SOME rows ==>
  registered_case10173_taylor_object taylor =
    bounded_taylor64_rows_object_cv taylor rows
Proof
  Cases_on `taylor`
  >> simp
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_hessian_def,
        compute_registeredCase10173LiteralAddChainEvalTheory.registered_case10173_taylor_object_def,
        compute_registeredCase10173LiteralAddChainEvalTheory.registered_case10173_taylor_rows_def]
QED

Theorem registered_case10173_constant_taylor_object_exact:
  registered_case10173_taylor_object
      (registered_case10173_constant_taylor value) =
    registered_case10173_constant_object value
Proof
  simp
    [compute_registeredCase10173LiteralAddChainEvalTheory.registered_case10173_taylor_object_def,
     compute_registeredCase10173LiteralAddChainEvalTheory.registered_case10173_taylor_rows_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_constant_taylor_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_constant_object_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_zero_hessian_rows_constant]
QED

Theorem registered_case10173_literal_negative_one_taylor:
  bounded_taylor64_constant
      bounded_case10173_literal_negative_one_decimal =
    SOME
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point T 1000000000000))
Proof
  simp
    [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_negative_one_decimal_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_decimal_point_def,
     compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def,
     compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
     compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_constant_taylor_def,
     compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def,
     compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def,
     compute_boundedIntervalListTheory.bounded_interval64_zero_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_literal_negative_one_program_trace:
  LENGTH dimensions = 6 /\ LENGTH radii = 6 ==>
  registered_case10173_poly_program_trace 8194
      (bounded_interval64_object_cv_list dimensions)
      (registered_case10173_word64_object_cv_list radii)
      registered_case10173_ordinary_negative_one_program (Num 0)
      (Pair
        (registered_case10173_constant_object
          (registered_case10173_decimal_point T 1000000000000))
        (Num 0))
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173OrdinarySuffixTraceEvalTheory.registered_case10173_ordinary_negative_one_program_def,
        compute_registeredCase10173PolynomialTraceEvalTheory.registered_case10173_poly_program_trace_def]
  >> irule
       compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_constant_step_eval_above
  >> simp
       [compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_source_constant_decimal_values,
        compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_polynomial_constant_values_def]
QED

Theorem registered_case10173_literal_negative_one_program_eval_above:
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
         from_cv registered_case10173_ordinary_negative_one_program])
      (registered_case10173_constant_object
        (registered_case10173_decimal_point T 1000000000000))
Proof
  strip_tac
  >> irule
       (SIMP_RULE arith_ss []
         (Q.INST
           [`conversion_floor:num` |-> `8208`,
            `step_floor:num` |-> `8194`,
           `numeric_floor:num` |-> `8208`]
           compute_registeredCase10173PolynomialTraceEvalTheory.registered_case10173_poly_program_eval_above_from_trace))
  >> conj_tac
  >- simp
       [compute_registeredCase10173OrdinarySuffixTraceEvalTheory.registered_case10173_ordinary_negative_one_program_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> qexists_tac `bounded_interval64_object_cv_list dimensions`
  >> qexists_tac `registered_case10173_word64_object_cv_list radii`
  >> asm_rewrite_tac []
  >> irule registered_case10173_literal_negative_one_program_trace
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_taylor_mul_true_domain:
  registered_case10173_taylor_domain left /\
  registered_case10173_taylor_domain right /\
  bounded_taylor64_mul_decimal radii left right = SOME result ==>
  registered_case10173_taylor_domain result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def]
  >> imp_res_tac
       compute_registeredCase10173ActualGroupProductEvalTheory.bounded_taylor64_mul_decimal_true_domain
QED

Theorem registered_case10173_taylor_mul_object_eval_above:
  LENGTH radii = 6 /\
  registered_case10173_taylor_domain left /\
  registered_case10173_taylor_domain right /\
  bounded_taylor64_mul_decimal radii left right = SOME result ==>
  registered_case10173_eval_above 8210
      (App «candle_cv_fs_result_mul»
        [from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv (registered_case10173_taylor_object left);
         from_cv (registered_case10173_taylor_object right)])
      (registered_case10173_taylor_object result)
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`left` |-> `left`, `right` |-> `right`, `result` |-> `result`]
         compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_mul_decimal_eval_above_exists)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> imp_res_tac registered_case10173_taylor_object_from_hessian_rows
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_ordinary_add_chain_contract_weaken:
  !summands sum_results accumulator final_result.
    registered_case10173_ordinary_add_chain_contract lower fixed_radii
        summands sum_results accumulator final_result /\
    lower <= upper ==>
    registered_case10173_ordinary_add_chain_contract upper fixed_radii
        summands sum_results accumulator final_result
Proof
  Induct_on `summands`
  >> rpt gen_tac
  >> Cases_on `sum_results`
  >> simp
       [compute_registeredCase10173OrdinaryAddChainTraceEvalTheory.registered_case10173_ordinary_add_chain_contract_def]
  >> metis_tac
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_weaken]
QED

Theorem registered_case10173_literal_suffix_numeric_contract:
  LENGTH dimensions = 6 /\ LENGTH radii = 6 /\
  registered_case10173_eval_above 8208
      (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
      (bounded_interval64_object_cv_list dimensions) /\
  registered_case10173_eval_above 8208
      (App «candle_cv_fs_list_of_q» [from_cv source_radii])
      (registered_case10173_word64_object_cv_list radii) /\
  EVERY registered_case10173_taylor_domain summands /\
  registered_case10173_taylor_domain historical_item /\
  EVERY bounded_taylor64_well_formed summands /\
  bounded_taylor64_well_formed historical_item /\
  bounded_taylor64_mul_decimal radii historical_item
      (registered_case10173_constant_taylor
        (registered_case10173_decimal_point T 1000000000000)) =
    SOME scaled_historical /\
  bounded_case10173_literal_add_stack_decimal radii summands
      scaled_historical = SOME final_result ==>
  ?sum_results.
    registered_case10173_ordinary_suffix_numeric_contract 8210
      center_boxes boxes source_radii
      (registered_case10173_word64_object_cv_list radii)
      (registered_case10173_taylor_object historical_item)
      (MAP registered_case10173_taylor_object summands)
      (MAP registered_case10173_taylor_object sum_results)
      (registered_case10173_taylor_object
        (registered_case10173_constant_taylor
          (registered_case10173_decimal_point T 1000000000000)))
      (registered_case10173_taylor_object scaled_historical)
      (registered_case10173_taylor_object final_result)
Proof
  strip_tac
  >> `registered_case10173_taylor_domain
        (registered_case10173_constant_taylor
          (registered_case10173_decimal_point T 1000000000000))` by
       simp
         [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def,
          compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_constant_taylor_def]
  >> `bounded_taylor64_well_formed
        (registered_case10173_constant_taylor
          (registered_case10173_decimal_point T 1000000000000))` by
       (irule
          compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_constant_taylor_well_formed
        >> simp
             [compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_polynomial_constant_values_def])
  >> `registered_case10173_taylor_domain scaled_historical` by
       metis_tac [registered_case10173_taylor_mul_true_domain]
  >> `bounded_taylor64_well_formed scaled_historical` by
       metis_tac
         [compute_boundedTaylorMulDecimalTheory.bounded_taylor64_mul_decimal_some]
  >> `registered_case10173_eval_above 8210
        (App «candle_cv_fs_poly_program»
          [from_cv center_boxes;from_cv source_radii;
           from_cv registered_case10173_ordinary_negative_one_program])
        (registered_case10173_taylor_object
          (registered_case10173_constant_taylor
            (registered_case10173_decimal_point T 1000000000000)))` by
       (PURE_REWRITE_TAC [registered_case10173_constant_taylor_object_exact]
        >> irule registered_case10173_literal_negative_one_program_eval_above
        >> conj_tac
        >- (qexists_tac `dimensions` >> asm_rewrite_tac [])
        >> qexists_tac `radii`
        >> asm_rewrite_tac [])
  >> `registered_case10173_eval_above 8210
        (App «candle_cv_fs_result_mul»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           from_cv (registered_case10173_taylor_object historical_item);
           from_cv
             (registered_case10173_taylor_object
               (registered_case10173_constant_taylor
                 (registered_case10173_decimal_point T 1000000000000)))])
        (registered_case10173_taylor_object scaled_historical)` by
       (irule registered_case10173_taylor_mul_object_eval_above
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST [`radii` |-> `radii`]
         compute_registeredCase10173LiteralAddChainEvalTheory.registered_case10173_literal_add_stack_contract)
  >> disch_then
       (qspecl_then [`summands`,`scaled_historical`,`final_result`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> `registered_case10173_eval_above 8210
        (App «candle_cv_fs_list_of_q» [from_cv source_radii])
        (registered_case10173_word64_object_cv_list radii)` by
       (irule
          compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_weaken
        >> qexists_tac `8208`
        >> asm_rewrite_tac []
        >> simp [])
  >> `registered_case10173_ordinary_add_chain_contract 8210
        (registered_case10173_word64_object_cv_list radii)
        (MAP registered_case10173_taylor_object summands)
        (MAP registered_case10173_taylor_object sum_results)
        (registered_case10173_taylor_object scaled_historical)
        (registered_case10173_taylor_object final_result)` by
       (irule registered_case10173_ordinary_add_chain_contract_weaken
        >> qexists_tac `8192`
        >> asm_rewrite_tac []
        >> simp [])
  >> qexists_tac `sum_results`
  >> rw
       [compute_registeredCase10173OrdinarySuffixTraceEvalTheory.registered_case10173_ordinary_suffix_numeric_contract_def]
QED

val _ = export_theory ();
