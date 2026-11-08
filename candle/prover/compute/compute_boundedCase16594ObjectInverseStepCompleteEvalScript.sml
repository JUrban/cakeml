(*****************************************************************************
 * Complete production evaluator semantics for a successful inverse
 * instruction.  This composes the authenticated certificate-list operations,
 * the exact two-certificate guard, and the inverse state update.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseStepCompleteEval
Ancestors
  compute_boundedCase16594ObjectInverseStepEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_inverse_step_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_reciprocal /\
  bounded_packed_q_interval_encoded box_reciprocal /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  bounded_object_q_positive_inv_certificate_exact
    center_value center_reciprocal /\
  bounded_object_q_positive_inv_certificate_exact
    value_bound box_reciprocal /\
  8210 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inv_step»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv
           (bounded_object_q_cv_list
             ([center_reciprocal;box_reciprocal] ++ certificate_rest));
         from_cv
           (Pair
             (bounded_case16594_object_state_cv domain_cv center_value
               (bounded_object_q_cv_list center_gradient) value_bound
               (bounded_object_q_cv_list gradient_bounds)
               (bounded_object_q_cv_list packed_hessian))
             stack_rest)]) (refs:hol_refs) =
    (M_success
      (Pair (Num 1)
        (Pair
          (Pair
            (from_cv
              (bounded_case16594_object_state_unary_cv radii domain_cv
                center_reciprocal
                (bounded_object_q_interval_neg_cv
                  (bounded_object_q_interval_mul_cv
                    center_reciprocal center_reciprocal))
                (bounded_object_q_interval_neg_cv
                  (bounded_object_q_interval_mul_cv
                    box_reciprocal box_reciprocal))
                (bounded_object_q_interval_add_cv
                  (bounded_object_q_interval_mul_cv
                    (bounded_object_q_interval_mul_cv
                      box_reciprocal box_reciprocal) box_reciprocal)
                  (bounded_object_q_interval_mul_cv
                    (bounded_object_q_interval_mul_cv
                      box_reciprocal box_reciprocal) box_reciprocal))
                center_gradient gradient_bounds packed_hessian))
            (from_cv stack_rest))
          (from_cv (bounded_object_q_cv_list certificate_rest)))),refs)
Proof
  strip_tac
  >> rw
       [compute_boundedCase16594ObjectInverseStepEvalTheory.bounded_case16594_object_inverse_step_unfold]
  >> simp
       [compute_boundedCase16594ObjectInverseStepEvalTheory.bounded_case16594_object_inverse_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_if_ispair_from_cv_pair]
  >> irule
       compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_if_true_result
  >> conj_tac
  >- simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule
       compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_if_true_result
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_has_eval)
      >> conj_tac >- intLib.ARITH_TAC
      >> simp [])
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_case16594_object_state_cv domain_cv center_value
          (bounded_object_q_cv_list center_gradient) value_bound
          (bounded_object_q_cv_list gradient_bounds)
          (bounded_object_q_cv_list packed_hessian)`
  >> conj_tac
  >- simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `center_reciprocal`
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          (Q.INST
            [`position` |-> `0`,
             `values` |->
               `center_reciprocal::box_reciprocal::certificate_rest`]
            compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_nth_eval))
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `box_reciprocal`
  >> conj_tac
  >- (irule
        (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          (Q.INST
            [`position` |-> `1`,
             `values` |->
               `center_reciprocal::box_reciprocal::certificate_rest`]
            compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_nth_eval))
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_object_q_cv_list certificate_rest`
  >> conj_tac
  >- (mp_tac
        (Q.SPECL
          [`2`,`center_reciprocal::box_reciprocal::certificate_rest`,
           `clock - 4`,`refs`]
          compute_boundedCase16594ObjectCertificateListEvalTheory.bounded_case16594_object_cval_list_drop_eval)
      >> simp [compute_execTheory.from_cv_def]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_if_true_result
  >> conj_tac
  >- (rewrite_tac
        [GSYM
          compute_boundedCase16594ObjectInverseStepEvalTheory.bounded_case16594_object_inverse_step_check_expression_def]
      >> irule
           compute_boundedCase16594ObjectInverseStepEvalTheory.bounded_case16594_object_inverse_step_check_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- simp
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectInverseStateEvalTheory.bounded_case16594_object_state_inverse_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> simp
           [Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

val _ = export_theory ();
