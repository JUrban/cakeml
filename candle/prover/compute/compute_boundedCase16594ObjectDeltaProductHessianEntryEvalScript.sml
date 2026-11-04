(*****************************************************************************
 * Exact evaluator semantics for one compact Hessian entry of 4*x_i*delta.
 *
 * The theorem is generic in the selected coordinate, row, column, the six
 * delta derivatives, and the supplied delta-Hessian entry.  The recursive
 * 21-entry constructor can therefore reuse it without numerical replay.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductHessianEntryEval
Ancestors
  compute_boundedCase16594ObjectDeltaProductGradientSixEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_product_hessian_entry_body_def:
  bounded_case16594_object_delta_product_hessian_entry_body =
    Let «base»
      (App «candle_cv_q_interval_mul»
        [Var «box_coordinate»;Var «delta_hessian»])
      (Let «with_row»
        (If (Binop Eq (Var «row_index») (Var «coordinate»))
          (App «candle_cv_q_interval_add»
            [Var «base»;
             App «candle_cv_q_interval_lookup»
               [Var «column_index»;Var «delta_gradient»]])
          (Var «base»))
        (Let «complete»
          (If (Binop Eq (Var «column_index») (Var «coordinate»))
            (App «candle_cv_q_interval_add»
              [Var «with_row»;
               App «candle_cv_q_interval_lookup»
                 [Var «row_index»;Var «delta_gradient»]])
            (Var «with_row»))
          (App «candle_cv_q_packed_delta_scale4» [Var «complete»])))
End

Definition bounded_case16594_object_delta_product_hessian_entry_cv_def:
  bounded_case16594_object_delta_product_hessian_entry_cv
      coordinate box_coordinate delta_gradient row column delta_hessian =
    let base = bounded_object_q_interval_mul_cv
          box_coordinate delta_hessian in
    let with_row =
          if row = coordinate then
            bounded_object_q_interval_add_cv base (EL column delta_gradient)
          else base in
    let complete =
          if column = coordinate then
            bounded_object_q_interval_add_cv with_row (EL row delta_gradient)
          else with_row in
      bounded_object_q_interval_scale4_cv complete
End

Theorem bounded_case16594_object_delta_product_hessian_entry_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_product_hessian_entry» =
    SOME
      ([«coordinate»;«box_coordinate»;«delta_gradient»;«row_index»;
        «column_index»;«delta_hessian»],
       bounded_case16594_object_delta_product_hessian_entry_body)
Proof
  rw [bounded_case16594_object_delta_product_hessian_entry_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_product_hessian_entry_eval:
  bounded_packed_q_interval_encoded box_coordinate /\
  EVERY bounded_packed_q_interval_encoded delta_gradient /\
  LENGTH delta_gradient = 6 /\
  row < 6 /\ column < 6 /\
  bounded_packed_q_interval_encoded delta_hessian /\
  64 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_hessian_entry»
        [from_cv (compute_exec$Num coordinate);from_cv box_coordinate;
         from_cv (bounded_object_q_cv_list delta_gradient);
         from_cv (compute_exec$Num row);from_cv (compute_exec$Num column);
         from_cv delta_hessian]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_product_hessian_entry_cv
          coordinate box_coordinate delta_gradient row column
          delta_hessian)),refs)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded (EL row delta_gradient) /\
      bounded_packed_q_interval_encoded (EL column delta_gradient)` by
       fs [EVERY_EL]
  >> `bounded_packed_q_interval_encoded
        (bounded_object_q_interval_mul_cv box_coordinate delta_hessian)` by
       (irule
          compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
        >> irule
             compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded
        >> simp
             [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded])
  >> `bounded_packed_q_interval_encoded
        (if row = coordinate then
           bounded_object_q_interval_add_cv
             (bounded_object_q_interval_mul_cv box_coordinate delta_hessian)
             (EL column delta_gradient)
         else
           bounded_object_q_interval_mul_cv box_coordinate delta_hessian)` by
       (Cases_on `row = coordinate`
        >> simp []
        >> irule
             compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
        >> irule
             compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded
        >> simp
             [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded])
  >> `bounded_packed_q_interval_encoded
        (if column = coordinate then
           bounded_object_q_interval_add_cv
             (if row = coordinate then
                bounded_object_q_interval_add_cv
                  (bounded_object_q_interval_mul_cv
                    box_coordinate delta_hessian)
                  (EL column delta_gradient)
              else
                bounded_object_q_interval_mul_cv
                  box_coordinate delta_hessian)
             (EL row delta_gradient)
         else
           if row = coordinate then
             bounded_object_q_interval_add_cv
               (bounded_object_q_interval_mul_cv
                 box_coordinate delta_hessian)
               (EL column delta_gradient)
           else
             bounded_object_q_interval_mul_cv
               box_coordinate delta_hessian)` by
       (Cases_on `column = coordinate`
        >> fs []
        >> irule
             compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
        >> irule
             compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded
        >> simp
             [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«coordinate»,from_cv (compute_exec$Num coordinate));
             («box_coordinate»,from_cv box_coordinate);
             («delta_gradient»,
               from_cv (bounded_object_q_cv_list delta_gradient));
             («row_index»,from_cv (compute_exec$Num row));
             («column_index»,from_cv (compute_exec$Num column));
             («delta_hessian»,from_cv delta_hessian)]
            bounded_case16594_object_delta_product_hessian_entry_body)
          refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
      >> simp []
      >> ACCEPT_TAC
           bounded_case16594_object_delta_product_hessian_entry_lookup)
  >> simp
       [bounded_case16594_object_delta_product_hessian_entry_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_interval_mul_cv box_coordinate delta_hessian`
  >> conj_tac
  >- (irule
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
       `if row = coordinate then
          bounded_object_q_interval_add_cv
            (bounded_object_q_interval_mul_cv box_coordinate delta_hessian)
            (EL column delta_gradient)
        else
          bounded_object_q_interval_mul_cv box_coordinate delta_hessian`
  >> conj_tac
  >- (Cases_on `row = coordinate`
      >> simp
           [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_compute_eval_if_num_eq]
      >> TRY
           (irule EQ_TRANS
            >> qexists_tac
                 `compute_eval (clock - 2)
                    bounded_case16594_object_dispatch_cell0_ceqs
                    (App «candle_cv_q_interval_add»
                      [from_cv
                         (bounded_object_q_interval_mul_cv
                           box_coordinate delta_hessian);
                       from_cv (EL column delta_gradient)]) refs`
            >> conj_tac
            >- (irule
                  compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
                >> simp [compute_execProofTheory.compute_eval_from_cv]
                >> irule
                     compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
                >> simp []
                >> intLib.ARITH_TAC)
            >> fs []
            >> irule
                 compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_eval
            >> fs []
            >> intLib.ARITH_TAC)
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `if column = coordinate then
          bounded_object_q_interval_add_cv
            (if row = coordinate then
               bounded_object_q_interval_add_cv
                 (bounded_object_q_interval_mul_cv
                   box_coordinate delta_hessian)
                 (EL column delta_gradient)
             else
               bounded_object_q_interval_mul_cv box_coordinate delta_hessian)
            (EL row delta_gradient)
        else
          if row = coordinate then
            bounded_object_q_interval_add_cv
              (bounded_object_q_interval_mul_cv box_coordinate delta_hessian)
              (EL column delta_gradient)
          else
            bounded_object_q_interval_mul_cv box_coordinate delta_hessian`
  >> conj_tac
  >- (Cases_on `column = coordinate`
      >> simp
           [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_compute_eval_if_num_eq]
      >> TRY
           (irule EQ_TRANS
            >> qexists_tac
                 `compute_eval (clock - 3)
                    bounded_case16594_object_dispatch_cell0_ceqs
                    (App «candle_cv_q_interval_add»
                      [from_cv
                         (if row = coordinate then
                            bounded_object_q_interval_add_cv
                              (bounded_object_q_interval_mul_cv
                                box_coordinate delta_hessian)
                              (EL column delta_gradient)
                          else
                            bounded_object_q_interval_mul_cv
                              box_coordinate delta_hessian);
                       from_cv (EL row delta_gradient)]) refs`
            >> conj_tac
            >- (irule
                  compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
                >> simp [compute_execProofTheory.compute_eval_from_cv]
                >> irule
                     compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
                >> simp []
                >> intLib.ARITH_TAC)
            >> fs []
            >> irule
                 compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_eval
            >> fs []
            >> intLib.ARITH_TAC)
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> rw [bounded_case16594_object_delta_product_hessian_entry_cv_def]
  >> irule
       compute_boundedCase16594ObjectDeltaLinearEvalTheory.bounded_case16594_object_delta_scale4_eval
  >> fs []
  >> TRY
       (irule
          compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
        >> irule
             compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded
        >> simp
             [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded])
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
