(*****************************************************************************
 * Exact evaluator semantics for one component of the gradient of 4*x_i*delta.
 *
 * The theorem is generic in both coordinate indices and all six delta
 * derivatives.  The six-component constructor can therefore instantiate it
 * without re-proving any interval arithmetic.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductGradientEntryEval
Ancestors
  compute_boundedCase16594ObjectDeltaLinearEval
  compute_boundedCase16594ObjectGradientCompleteEval
  compute_boundedCase16594ObjectSpecializedStepControlEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_product_center_gradient_entry_body_def:
  bounded_case16594_object_delta_product_center_gradient_entry_body =
    Let «base»
      (App «candle_cv_q_interval_mul»
        [Var «coordinate_value»;
         App «candle_cv_q_interval_lookup»
           [Var «derivative_coordinate»;Var «delta_gradient»]])
      (Let «complete»
        (If (Binop Eq (Var «derivative_coordinate») (Var «coordinate»))
          (App «candle_cv_q_interval_add» [Var «base»;Var «delta_value»])
          (Var «base»))
        (App «candle_cv_q_packed_delta_scale4» [Var «complete»]))
End

Definition bounded_case16594_object_delta_product_center_gradient_entry_cv_def:
  bounded_case16594_object_delta_product_center_gradient_entry_cv
      coordinate coordinate_value delta_value delta_gradient
      derivative_coordinate =
    bounded_object_q_interval_scale4_cv
      (if derivative_coordinate = coordinate then
         bounded_object_q_interval_add_cv
           (bounded_object_q_interval_mul_cv coordinate_value
             (EL derivative_coordinate delta_gradient))
           delta_value
       else
         bounded_object_q_interval_mul_cv coordinate_value
           (EL derivative_coordinate delta_gradient))
End

Theorem bounded_case16594_object_delta_product_center_gradient_entry_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_product_center_gradient_entry» =
    SOME
      ([«coordinate»;«coordinate_value»;«delta_value»;«delta_gradient»;
        «derivative_coordinate»],
       bounded_case16594_object_delta_product_center_gradient_entry_body)
Proof
  rw [bounded_case16594_object_delta_product_center_gradient_entry_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_product_center_gradient_entry_eval:
  bounded_packed_q_interval_encoded coordinate_value /\
  bounded_packed_q_interval_encoded delta_value /\
  EVERY bounded_packed_q_interval_encoded delta_gradient /\
  LENGTH delta_gradient = 6 /\
  derivative_coordinate < 6 /\
  48 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_center_gradient_entry»
        [from_cv (compute_exec$Num coordinate);from_cv coordinate_value;
         from_cv delta_value;
         from_cv (bounded_object_q_cv_list delta_gradient);
         from_cv (compute_exec$Num derivative_coordinate)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_product_center_gradient_entry_cv
          coordinate coordinate_value delta_value delta_gradient
          derivative_coordinate)),refs)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded
        (EL derivative_coordinate delta_gradient)` by
       fs [EVERY_EL]
  >> `bounded_packed_q_interval_encoded
        (bounded_object_q_interval_mul_cv coordinate_value
          (EL derivative_coordinate delta_gradient))` by
       (irule
          compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
        >> irule
             compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded
        >> simp
             [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«coordinate»,from_cv (compute_exec$Num coordinate));
             («coordinate_value»,from_cv coordinate_value);
             («delta_value»,from_cv delta_value);
             («delta_gradient»,
               from_cv (bounded_object_q_cv_list delta_gradient));
             («derivative_coordinate»,
               from_cv (compute_exec$Num derivative_coordinate))]
            bounded_case16594_object_delta_product_center_gradient_entry_body)
          refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectRecompleteControlEvalTheory.bounded_case16594_object_compute_eval_literal_app5
      >> simp []
      >> ACCEPT_TAC
           bounded_case16594_object_delta_product_center_gradient_entry_lookup)
  >> simp
       [bounded_case16594_object_delta_product_center_gradient_entry_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_interval_mul_cv coordinate_value
          (EL derivative_coordinate delta_gradient)`
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_interval_mul»
                [from_cv coordinate_value;
                 from_cv (EL derivative_coordinate delta_gradient)]) refs`
      >> conj_tac
      >- (irule
            compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
          >> simp [compute_execProofTheory.compute_eval_from_cv]
          >> irule
               compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> irule
           compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_q_interval_mul_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `if derivative_coordinate = coordinate then
          bounded_object_q_interval_add_cv
            (bounded_object_q_interval_mul_cv coordinate_value
              (EL derivative_coordinate delta_gradient))
            delta_value
        else
          bounded_object_q_interval_mul_cv coordinate_value
            (EL derivative_coordinate delta_gradient)`
  >> conj_tac
  >- (Cases_on `derivative_coordinate = coordinate`
      >> simp
           [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_compute_eval_if_num_eq]
      >> TRY
           (irule
            compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_eval
          >> fs []
          >> intLib.ARITH_TAC)
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> rw
       [bounded_case16594_object_delta_product_center_gradient_entry_cv_def]
  >> irule
       compute_boundedCase16594ObjectDeltaLinearEvalTheory.bounded_case16594_object_delta_scale4_eval
  >> simp []
  >> Cases_on `derivative_coordinate = coordinate`
  >> simp []
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
