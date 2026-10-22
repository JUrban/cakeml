(*****************************************************************************
 * Source-object contract for the literal source-shaped addition chain.
 *
 * The bounded checker keeps Taylor states as typed data while the registered
 * Candle evaluator consumes their row-expanded cv objects.  A well-formed
 * state has a unique six-by-six row expansion; selecting that canonical
 * expansion once avoids threading thirteen unrelated existential row names
 * through the fixed suffix.
 *****************************************************************************)
Theory compute_registeredCase10173LiteralAddChainEval
Ancestors
  compute_boundedCase10173LiteralSourceDecimal
  compute_registeredCase10173ActualGroupProductEval
  compute_registeredCase10173ResultAddAboveEval
  compute_registeredCase10173OrdinaryAddChainTraceEval
Libs
  bossLib preamble intLib

Definition registered_case10173_taylor_rows_def:
  registered_case10173_taylor_rows
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    case bounded_hessian64_rows hessian of
    | NONE => []
    | SOME rows => rows
End

Definition registered_case10173_taylor_object_def:
  registered_case10173_taylor_object (taylor:bounded_taylor64) =
    bounded_taylor64_rows_object_cv taylor
      (registered_case10173_taylor_rows taylor)
End

Theorem registered_case10173_taylor_rows_exact:
  bounded_taylor64_well_formed
      (BoundedTaylor64 domain_flag center_value center_gradient
        value_bound gradient_bounds hessian) ==>
  bounded_hessian64_rows hessian =
    SOME
      (registered_case10173_taylor_rows
        (BoundedTaylor64 domain_flag center_value center_gradient
          value_bound gradient_bounds hessian)) /\
  LENGTH
      (registered_case10173_taylor_rows
        (BoundedTaylor64 domain_flag center_value center_gradient
          value_bound gradient_bounds hessian)) = 6 /\
  EVERY (\row. LENGTH row = 6)
      (registered_case10173_taylor_rows
        (BoundedTaylor64 domain_flag center_value center_gradient
          value_bound gradient_bounds hessian))
Proof
  strip_tac
  >> fs [compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> drule
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length
  >> strip_tac
  >> fs [registered_case10173_taylor_rows_def]
QED

Theorem registered_case10173_taylor_object_exact:
  bounded_taylor64_well_formed (taylor:bounded_taylor64) ==>
  ?rows.
    bounded_hessian64_rows (registered_case10173_taylor_hessian taylor) =
      SOME rows /\
    registered_case10173_taylor_object taylor =
      bounded_taylor64_rows_object_cv taylor rows
Proof
  Cases_on `taylor`
  >> strip_tac
  >> drule registered_case10173_taylor_rows_exact
  >> strip_tac
  >> qexists_tac
       `registered_case10173_taylor_rows
          (BoundedTaylor64 b b0 l b1 l0 l1)`
  >> fs
       [registered_case10173_taylor_object_def,
        compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_hessian_def]
QED

Theorem registered_case10173_taylor_add_true_domain:
  registered_case10173_taylor_domain left /\
  registered_case10173_taylor_domain right /\
  bounded_taylor64_add left right = SOME result ==>
  registered_case10173_taylor_domain result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def,
        compute_boundedTaylorStateTheory.bounded_taylor64_add_def,
        compute_boundedTaylorStateTheory.bounded_taylor64_add_unchecked_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_literal_add_true_domain:
  registered_case10173_taylor_domain left /\
  registered_case10173_taylor_domain right /\
  bounded_case10173_literal_add_decimal radii left right = SOME result ==>
  registered_case10173_taylor_domain result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw
       [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_add_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_taylor_add_true_domain
  >> fs
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def]
  >> imp_res_tac
       compute_registeredCase10173ActualGroupProductEvalTheory.bounded_taylor64_complete_decimal_true_domain
  >> gvs
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def]
QED

Theorem registered_case10173_literal_add_decimal_eval_above:
  LENGTH radii = 6 /\
  registered_case10173_taylor_domain left /\
  registered_case10173_taylor_domain right /\
  bounded_taylor64_well_formed left /\
  bounded_taylor64_well_formed right /\
  bounded_case10173_literal_add_decimal radii left right = SOME result ==>
  registered_case10173_eval_above 8192
    (App «candle_cv_fs_result_add»
      [from_cv (registered_case10173_word64_object_cv_list radii);
       from_cv (registered_case10173_taylor_object left);
       from_cv (registered_case10173_taylor_object right)])
    (registered_case10173_taylor_object result)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> strip_tac
  >> fs [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_add_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_taylor_add_true_domain
  >> fs
       [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def]
  >> imp_res_tac
       compute_boundedTaylorStateTheory.bounded_taylor64_add_well_formed
  >> imp_res_tac
       compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_some
  >> imp_res_tac
       compute_registeredCase10173ActualGroupProductEvalTheory.bounded_taylor64_complete_decimal_true_domain
  >> imp_res_tac
       compute_registeredCase10173ResultSqrtContractTheory.registered_case10173_taylor_complete_decimal_hessian
  >> gvs []
  >> imp_res_tac registered_case10173_taylor_rows_exact
  >> simp [registered_case10173_taylor_object_def]
  >> irule
       compute_registeredCase10173ResultAddAboveEvalTheory.registered_case10173_deferred_add_object_eval_above
  >> fs
       [compute_boundedCase10173HistoricalCellTheory.bounded_case10173_deferred_add_def,
        compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> imp_res_tac
       compute_registeredCase10173ResultMulAboveEvalTheory.registered_case10173_matrix_shape6_sum
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_literal_add_stack_contract:
  !summands accumulator result.
    LENGTH radii = 6 /\
    EVERY registered_case10173_taylor_domain summands /\
    registered_case10173_taylor_domain accumulator /\
    EVERY bounded_taylor64_well_formed summands /\
    bounded_taylor64_well_formed accumulator /\
    bounded_case10173_literal_add_stack_decimal radii summands accumulator =
      SOME result ==>
    ?sum_results.
      registered_case10173_ordinary_add_chain_contract 8192
        (registered_case10173_word64_object_cv_list radii)
        (MAP registered_case10173_taylor_object summands)
        (MAP registered_case10173_taylor_object sum_results)
        (registered_case10173_taylor_object accumulator)
        (registered_case10173_taylor_object result)
Proof
  Induct_on `summands`
  >- (rpt gen_tac
      >> simp
           [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_add_stack_decimal_def,
            compute_registeredCase10173OrdinaryAddChainTraceEvalTheory.registered_case10173_ordinary_add_chain_contract_def]
      >> strip_tac
      >> qexists_tac `[]`
      >> simp
           [compute_registeredCase10173OrdinaryAddChainTraceEvalTheory.registered_case10173_ordinary_add_chain_contract_def])
  >> rpt gen_tac
  >> simp
       [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_add_stack_decimal_def]
  >> every_case_tac
  >> gvs []
  >> strip_tac
  >> imp_res_tac
       compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_add_decimal_some
  >> imp_res_tac registered_case10173_literal_add_true_domain
  >> last_x_assum (qspecl_then [`x`,`result`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> qexists_tac `x::sum_results`
  >> simp
       [compute_registeredCase10173OrdinaryAddChainTraceEvalTheory.registered_case10173_ordinary_add_chain_contract_def]
  >> irule registered_case10173_literal_add_decimal_eval_above
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
