(*****************************************************************************
 * Literal first-order square-root evaluation from authenticated decimals.
 *
 * The source keeps the square-root value as a positive rational interval and
 * computes its derivative by taking the reciprocal of twice that interval.
 * This theorem composes those unchanged calls with the checked decimal list
 * scaler.  It is parameterized by the input first jet and performs no closed
 * case-10173 arithmetic.
 *****************************************************************************)
Theory compute_registeredCase10173ActualSqrtFirstEval
Ancestors
  compute_registeredCase10173ActualSqrtHessianCompose
  compute_registeredCase10173HistoricalBasicEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_actual_sqrt_first_eval:
  bounded_case10173_source_positive_q_interval64_exact root root_decimal /\
  (case root_decimal of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  bounded_interval64_add root_decimal root_decimal = SOME twice /\
  (case twice of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  bounded_interval64_positive_inv_certificate_decimal twice derivative /\
  (case derivative of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  LENGTH gradient = 6 /\
  bounded_interval64_list_scale_decimal derivative gradient =
    SOME scaled_gradient /\
  180 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_first_sqrt»
        [from_cv root;
         from_cv
           (Pair (bounded_interval64_object_cv center_value)
             (bounded_interval64_object_cv_list gradient))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (bounded_interval64_object_cv root_decimal)
          (bounded_interval64_object_cv_list scaled_gradient))),refs)
Proof
  strip_tac
  >> rw
       [compute_registeredCase10173ResultSqrtEvalTheory.registered_case10173_fsn_first_sqrt_unfold]
  >> simp
       [compute_registeredCase10173ResultSqrtEvalTheory.registered_case10173_fsn_first_sqrt_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv root_decimal)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_of_q_object_eval
      >> conj_tac
      >> TRY
           (irule
              compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_interval64_exact_conversion
            >> asm_rewrite_tac [])
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv derivative)`
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`clock` |-> `clock - 2`]
          compute_registeredCase10173ActualSqrtDerivativeEvalTheory.registered_case10173_actual_sqrt_derivative_eval)
      >> impl_tac
      >- (asm_rewrite_tac []
          >> intLib.ARITH_TAC)
      >> simp [])
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 3)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_first_make»
            [from_cv (bounded_interval64_object_cv root_decimal);
             from_cv
               (bounded_interval64_object_cv_list scaled_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >> TRY (irule compute_execProofTheory.compute_eval_from_cv)
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 3)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fsn_interval_list_scale»
                [from_cv (bounded_interval64_object_cv derivative);
                 from_cv
                   (bounded_interval64_object_cv_list gradient)]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
          >> simp [compute_execProofTheory.compute_eval_from_cv]
          >> ONCE_REWRITE_TAC
               [GSYM (CONJUNCT2 compute_execTheory.from_cv_def)]
          >> irule
               compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_first_gradient_eval
          >> intLib.ARITH_TAC)
      >> irule
           compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_fsn_interval_list_scale_bounded_eval
      >> conj_tac
      >> TRY
           (irule
              compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_exact
            >> asm_rewrite_tac [])
      >> imp_res_tac
           compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_length
      >> intLib.ARITH_TAC)
  >> ONCE_REWRITE_TAC
       [GSYM (CONJUNCT2 compute_execTheory.from_cv_def)]
  >> irule
       compute_registeredCase10173HistoricalBasicEvalTheory.registered_case10173_fs_first_make_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
