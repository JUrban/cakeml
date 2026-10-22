(*****************************************************************************
 * Composition of the unchanged source sqrt Hessian on the actual operand.
 *
 * The fast checker stores the symmetric Hessian in 21 entries.  This theory
 * combines the authenticated source d/dd evaluations with the proved 21-to-
 * 6x6 matrix trace and evaluates the literal source matrix expression.
 *****************************************************************************)
Theory compute_registeredCase10173ActualSqrtHessianCompose
Ancestors
  compute_registeredCase10173ActualSqrtDerivativeEval
  compute_registeredCase10173ResultSqrtEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_actual_sqrt_hessian_matrix_trace:
  LENGTH gradient = 6 /\
  bounded_interval64_self_outer_decimal gradient = SOME compact_outer /\
  bounded_hessian64_rows compact_outer = SOME outer_rows /\
  bounded_interval64_list_scale_decimal second compact_outer =
    SOME outer_hessian /\
  bounded_hessian64_rows outer_hessian = SOME outer_hessian_rows /\
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  bounded_interval64_list_scale_decimal derivative hessian =
    SOME scaled_hessian /\
  bounded_hessian64_rows scaled_hessian = SOME scaled_hessian_rows /\
  bounded_interval64_list_add outer_hessian scaled_hessian =
    SOME result_hessian /\
  bounded_hessian64_rows result_hessian = SOME result_rows ==>
  bounded_interval64_matrix_outer_decimal gradient gradient =
      SOME outer_rows /\
  bounded_interval64_matrix_scale_decimal second outer_rows =
      SOME outer_hessian_rows /\
  bounded_interval64_matrix_scale_decimal derivative hessian_rows =
      SOME scaled_hessian_rows /\
  bounded_interval64_matrix_add outer_hessian_rows scaled_hessian_rows =
      SOME result_rows
Proof
  strip_tac
  >> conj_tac
  >- metis_tac
       [compute_registeredCase10173ActualSqrtHessianTraceTheory.bounded_interval64_self_outer_decimal_rows]
  >> conj_tac
  >- metis_tac
       [compute_boundedObjectTaylorStateDecimalTheory.bounded_hessian64_rows_scale_decimal]
  >> conj_tac
  >- metis_tac
       [compute_boundedObjectTaylorStateDecimalTheory.bounded_hessian64_rows_scale_decimal]
  >> metis_tac
       [compute_boundedObjectTaylorStateDecimalTheory.bounded_hessian64_rows_add]
QED

Theorem registered_case10173_hessian_rows_size:
  bounded_hessian64_rows hessian = SOME rows ==>
  LENGTH rows = 6 /\ EVERY (\row. LENGTH row = 6) rows /\
  SUM (MAP LENGTH rows) = 36
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_actual_sqrt_hessian_eval:
  bounded_interval64_valid value_bound /\
  bounded_case10173_positive_interval64_q_cv value_bound = SOME input /\
  bounded_object_positive_q_interval64_decimal root = SOME root_decimal /\
  bounded_case10173_source_q_sqrt_certificate_exact input root /\
  bounded_case10173_source_sqrt_dd_interval64_exact
    root input second_reciprocal /\
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
  bounded_interval64_self_outer_decimal gradient = SOME compact_outer /\
  bounded_hessian64_rows compact_outer = SOME outer_rows /\
  bounded_interval64_list_scale_decimal
    (bounded_interval64_neg second_reciprocal) compact_outer =
      SOME outer_hessian /\
  bounded_hessian64_rows outer_hessian = SOME outer_hessian_rows /\
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  bounded_interval64_list_scale_decimal derivative hessian =
    SOME scaled_hessian /\
  bounded_hessian64_rows scaled_hessian = SOME scaled_hessian_rows /\
  bounded_interval64_list_add outer_hessian scaled_hessian =
    SOME result_hessian /\
  bounded_hessian64_rows result_hessian = SOME result_rows /\
  200 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_hessian»
        [from_cv root;
         from_cv (bounded_interval64_object_cv value_bound);
         from_cv (bounded_interval64_object_cv_list gradient);
         from_cv (bounded_interval64_object_cv_matrix hessian_rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_matrix result_rows)),refs)
Proof
  strip_tac
  >> `bounded_interval64_matrix_outer_decimal gradient gradient =
        SOME outer_rows /\
      bounded_interval64_matrix_scale_decimal
        (bounded_interval64_neg second_reciprocal) outer_rows =
        SOME outer_hessian_rows /\
      bounded_interval64_matrix_scale_decimal derivative hessian_rows =
        SOME scaled_hessian_rows /\
      bounded_interval64_matrix_add outer_hessian_rows scaled_hessian_rows =
        SOME result_rows` by
       (match_mp_tac registered_case10173_actual_sqrt_hessian_matrix_trace
        >> asm_rewrite_tac [])
  >> imp_res_tac registered_case10173_hessian_rows_size
  >> rw
       [compute_registeredCase10173ResultSqrtEvalTheory.registered_case10173_fsn_sqrt_hessian_unfold]
  >> simp
       [compute_registeredCase10173ResultSqrtEvalTheory.registered_case10173_fsn_sqrt_hessian_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv input`
  >> conj_tac
  >- (irule
        compute_registeredCase10173ActualSqrtHessianEvalTheory.registered_case10173_actual_fs_interval_to_q_eval
      >> asm_rewrite_tac []
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
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv
            (bounded_interval64_neg second_reciprocal))`
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`clock` |-> `clock - 3`,
           `reciprocal` |-> `second_reciprocal`]
          compute_registeredCase10173ActualSqrtHessianEvalTheory.registered_case10173_actual_sqrt_second_derivative_direct_eval)
      >> impl_tac
      >- (asm_rewrite_tac []
          >> intLib.ARITH_TAC)
      >> simp [])
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 4)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_matrix_add»
            [from_cv
               (bounded_interval64_object_cv_matrix outer_hessian_rows);
             from_cv
               (bounded_interval64_object_cv_matrix scaled_hessian_rows)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule EQ_TRANS
          >> qexists_tac
               `compute_eval (clock - 4)
                  registered_case10173_historical_chunk16_ceqs
                  (App «candle_cv_fsn_interval_matrix_scale»
                    [from_cv
                       (bounded_interval64_object_cv
                         (bounded_interval64_neg second_reciprocal));
                     from_cv
                       (bounded_interval64_object_cv_matrix outer_rows)]) refs`
          >> conj_tac
          >- (irule
                compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
              >> simp [compute_execProofTheory.compute_eval_from_cv]
              >> irule
                   compute_registeredCase10173ActualSqrtHessianTraceTheory.registered_case10173_fsn_interval_outer_typed_eval
              >> asm_rewrite_tac []
              >> intLib.ARITH_TAC)
          >> irule
               compute_registeredCase10173SqrtMatrixWrapperEvalTheory.registered_case10173_fsn_interval_matrix_scale_typed_eval
          >> asm_rewrite_tac []
          >> intLib.ARITH_TAC)
      >> irule
           compute_registeredCase10173SqrtMatrixWrapperEvalTheory.registered_case10173_fsn_interval_matrix_scale_typed_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalSecondOrderMatrixEvalTheory.registered_case10173_fs_interval_matrix_add_typed_eval
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
