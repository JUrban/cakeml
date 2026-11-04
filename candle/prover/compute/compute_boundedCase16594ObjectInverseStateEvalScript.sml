(*****************************************************************************
 * Complete production evaluator semantics for the object inverse state
 * wrapper.  Exact certificate checking remains in the inverse-step layer;
 * this theory authenticates the three reciprocal derivative calculations
 * and their composition through the shared unary-state implementation.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseStateEval
Ancestors
  compute_boundedCase16594ObjectInverseControlEval
  compute_boundedCase16594ObjectInverseCoreCongruence
  compute_boundedCase16594ObjectUnaryCompleteEval
  compute_boundedCase16594ObjectMulEval
  compute_boundedObjectTaylorZeroAlgebra
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_inverse_second_body_def:
  bounded_case16594_object_inverse_second_body =
    App «candle_cv_q_interval_add»
      [App «candle_cv_q_interval_mul»
        [App «candle_cv_q_interval_mul»
          [Var «reciprocal»;Var «reciprocal»];
         Var «reciprocal»];
       App «candle_cv_q_interval_mul»
        [App «candle_cv_q_interval_mul»
          [Var «reciprocal»;Var «reciprocal»];
         Var «reciprocal»]]
End

Theorem bounded_case16594_object_inverse_second_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_inverse_second» =
    SOME
      ([«reciprocal»],bounded_case16594_object_inverse_second_body)
Proof
  rw [bounded_case16594_object_inverse_second_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_inverse_second_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inverse_second»
        [from_cv reciprocal]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«reciprocal»,from_cv reciprocal)]
        bounded_case16594_object_inverse_second_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_inverse_second_lookup
QED

Theorem bounded_case16594_object_inverse_derivative_eval:
  bounded_packed_q_interval_encoded reciprocal /\
  10 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inverse_derivative»
        [from_cv reciprocal]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_interval_neg_cv
          (bounded_object_q_interval_mul_cv reciprocal reciprocal))),refs)
Proof
  strip_tac
  >> `compute_exp_uses_only bounded_case16594_object_inverse_core
        (App «candle_cv_q_packed_object_inverse_derivative»
          [from_cv reciprocal])` by
       (simp
          [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
           compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_inverse_core_def,
           compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_uses_only_from_cv]
        >> EVAL_TAC)
  >> `compute_eval clock bounded_object_interval_inverse_witness_ceqs
        (App «candle_cv_q_packed_object_inverse_derivative»
          [from_cv reciprocal]) (refs:hol_refs) =
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_inverse_derivative»
          [from_cv reciprocal]) refs` by
       metis_tac
         [compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_inverse_core_eval_cong]
  >> metis_tac
       [compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_derivative_eval]
QED

Theorem bounded_case16594_object_inverse_cube_eval:
  bounded_packed_q_interval_encoded reciprocal /\
  8 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_mul»
        [App «candle_cv_q_interval_mul»
          [from_cv reciprocal;from_cv reciprocal];
         from_cv reciprocal]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_mul_cv reciprocal reciprocal)
          reciprocal)),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_mul_argument_results
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_q_interval_mul_eval,
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded,
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded,
        compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded]
QED

Theorem bounded_case16594_object_inverse_second_eval:
  bounded_packed_q_interval_encoded reciprocal /\
  10 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inverse_second»
        [from_cv reciprocal]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_interval_add_cv
          (bounded_object_q_interval_mul_cv
            (bounded_object_q_interval_mul_cv reciprocal reciprocal)
            reciprocal)
          (bounded_object_q_interval_mul_cv
            (bounded_object_q_interval_mul_cv reciprocal reciprocal)
            reciprocal))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_inverse_second_unfold]
  >> simp
       [bounded_case16594_object_inverse_second_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_argument_results
  >> simp
       [bounded_case16594_object_inverse_cube_eval,
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded,
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded,
        compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_inverse_outputs_encoded:
  bounded_packed_q_interval_encoded reciprocal ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_neg_cv
      (bounded_object_q_interval_mul_cv reciprocal reciprocal)) /\
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_add_cv
      (bounded_object_q_interval_mul_cv
        (bounded_object_q_interval_mul_cv reciprocal reciprocal)
        reciprocal)
      (bounded_object_q_interval_mul_cv
        (bounded_object_q_interval_mul_cv reciprocal reciprocal)
        reciprocal))
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded
  >> rpt conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
      >> irule
           compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_neg_cv_encoded
      >> irule
           compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded
      >> simp [])
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded
  >> simp
       [compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded]
QED

Theorem bounded_case16594_object_state_inverse_eval:
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
  8194 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_inverse»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv center_reciprocal;from_cv box_reciprocal;
         from_cv
           (bounded_case16594_object_state_cv domain_cv center_value
             (bounded_object_q_cv_list center_gradient) value_bound
             (bounded_object_q_cv_list gradient_bounds)
             (bounded_object_q_cv_list packed_hessian))])
      (refs:hol_refs) =
    (M_success
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
          center_gradient gradient_bounds packed_hessian)),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectInverseControlEvalTheory.bounded_case16594_object_state_inverse_eval_from_components
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_interval_neg_cv
          (bounded_object_q_interval_mul_cv
            box_reciprocal box_reciprocal)`
  >> qexists_tac
       `bounded_object_q_interval_add_cv
          (bounded_object_q_interval_mul_cv
            (bounded_object_q_interval_mul_cv
              box_reciprocal box_reciprocal) box_reciprocal)
          (bounded_object_q_interval_mul_cv
            (bounded_object_q_interval_mul_cv
              box_reciprocal box_reciprocal) box_reciprocal)`
  >> qexists_tac
       `bounded_object_q_interval_neg_cv
          (bounded_object_q_interval_mul_cv
            center_reciprocal center_reciprocal)`
  >> rpt conj_tac
  >- (irule
        compute_boundedCase16594ObjectUnaryCompleteEvalTheory.bounded_case16594_object_state_unary_eval
      >> simp [bounded_case16594_object_inverse_outputs_encoded]
      >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_inverse_second_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_inverse_derivative_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_inverse_derivative_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
