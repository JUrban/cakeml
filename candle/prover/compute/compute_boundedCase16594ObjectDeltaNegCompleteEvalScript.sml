(*****************************************************************************
 * Exact arbitrary-input evaluators for the production -d(delta)/dx_i source
 * family.  The final theorem composes the center jet, constant packed
 * Hessian, and the structural source-item wrapper.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaNegCompleteEval
Ancestors
  compute_boundedCase16594ObjectDeltaNegSourceItemEval
  compute_boundedCase16594ObjectDeltaProductSourceCompleteEval
  compute_boundedCase16594ObjectVariableEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_basis_six_cv_def:
  bounded_case16594_object_delta_basis_six_cv (coordinate:num) =
    [if coordinate = 0 then bounded_case16594_object_one_interval_cv
     else bounded_case16594_object_zero_interval_cv;
     if coordinate = 1 then bounded_case16594_object_one_interval_cv
     else bounded_case16594_object_zero_interval_cv;
     if coordinate = 2 then bounded_case16594_object_one_interval_cv
     else bounded_case16594_object_zero_interval_cv;
     if coordinate = 3 then bounded_case16594_object_one_interval_cv
     else bounded_case16594_object_zero_interval_cv;
     if coordinate = 4 then bounded_case16594_object_one_interval_cv
     else bounded_case16594_object_zero_interval_cv;
     if coordinate = 5 then bounded_case16594_object_one_interval_cv
     else bounded_case16594_object_zero_interval_cv]
End

Definition bounded_case16594_object_delta_basis_six_body_def:
  bounded_case16594_object_delta_basis_six_body =
    App «candle_cv_q_packed_delta_six»
      [If (Binop Eq (Var «coordinate») (Num 0))
         (App «candle_cv_q_one_interval» [])
         (App «candle_cv_q_zero_interval» []);
       If (Binop Eq (Var «coordinate») (Num 1))
         (App «candle_cv_q_one_interval» [])
         (App «candle_cv_q_zero_interval» []);
       If (Binop Eq (Var «coordinate») (Num 2))
         (App «candle_cv_q_one_interval» [])
         (App «candle_cv_q_zero_interval» []);
       If (Binop Eq (Var «coordinate») (Num 3))
         (App «candle_cv_q_one_interval» [])
         (App «candle_cv_q_zero_interval» []);
       If (Binop Eq (Var «coordinate») (Num 4))
         (App «candle_cv_q_one_interval» [])
         (App «candle_cv_q_zero_interval» []);
       If (Binop Eq (Var «coordinate») (Num 5))
         (App «candle_cv_q_one_interval» [])
         (App «candle_cv_q_zero_interval» [])]
End

Theorem bounded_case16594_object_delta_basis_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_basis_six» =
    SOME ([«coordinate»],bounded_case16594_object_delta_basis_six_body)
Proof
  rw [bounded_case16594_object_delta_basis_six_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_basis_six_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_basis_six»
        [from_cv (Num coordinate)]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«coordinate»,from_cv (Num coordinate))]
        bounded_case16594_object_delta_basis_six_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> simp [bounded_case16594_object_delta_basis_six_lookup]
QED

Theorem bounded_case16594_object_delta_basis_component_eval:
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (If (Binop Eq (Num coordinate) (Num index))
        (App «candle_cv_q_one_interval» [])
        (App «candle_cv_q_zero_interval» [])) (refs:hol_refs) =
    (M_success
      (from_cv
        (if coordinate = index then
           bounded_case16594_object_one_interval_cv
         else bounded_case16594_object_zero_interval_cv)),refs)
Proof
  strip_tac
  >> Cases_on `coordinate = index`
  >> simp
       [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_compute_eval_if_num_eq,
        compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_one_interval_eval,
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_zero_interval_eval,
        compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_one_interval_cv_def,
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_zero_interval_cv_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
        compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_delta_basis_six_eval:
  (coordinate:num) < 6 /\ 16 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_basis_six»
        [from_cv (Num coordinate)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_case16594_object_delta_basis_six_cv coordinate))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_delta_basis_six_unfold]
  >> simp
       [bounded_case16594_object_delta_basis_six_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_six»
            [from_cv
               (if coordinate = 0 then
                  bounded_case16594_object_one_interval_cv
                else bounded_case16594_object_zero_interval_cv);
             from_cv
               (if coordinate = 1 then
                  bounded_case16594_object_one_interval_cv
                else bounded_case16594_object_zero_interval_cv);
             from_cv
               (if coordinate = 2 then
                  bounded_case16594_object_one_interval_cv
                else bounded_case16594_object_zero_interval_cv);
             from_cv
               (if coordinate = 3 then
                  bounded_case16594_object_one_interval_cv
                else bounded_case16594_object_zero_interval_cv);
             from_cv
               (if coordinate = 4 then
                  bounded_case16594_object_one_interval_cv
                else bounded_case16594_object_zero_interval_cv);
             from_cv
               (if coordinate = 5 then
                  bounded_case16594_object_one_interval_cv
                else bounded_case16594_object_zero_interval_cv)]) refs`
  >> conj_tac
  >- (`1 < clock - 1` by intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
      >> simp
           [bounded_case16594_object_delta_basis_component_eval]
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [bounded_case16594_object_delta_basis_six_cv_def]
  >> irule
       compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_delta_six_eval
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_delta_neg_center_value_cv_def:
  bounded_case16594_object_delta_neg_center_value_cv coordinate
      x0 x1 x2 x3 x4 x5 =
    bounded_object_q_interval_neg_cv
      (EL coordinate
        (bounded_case16594_object_delta_gradient_six_cv
          x0 x1 x2 x3 x4 x5))
End

Definition bounded_case16594_object_delta_neg_center_value_body_def:
  bounded_case16594_object_delta_neg_center_value_body =
    App «candle_cv_q_interval_neg»
      [App «candle_cv_q_interval_lookup»
        [Var «coordinate»;
         App «candle_cv_q_packed_delta_gradient_six»
           [Var «x0»;Var «x1»;Var «x2»;Var «x3»;Var «x4»;Var «x5»]]]
End

Theorem bounded_case16594_object_delta_neg_center_value_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_neg_derivative_center_value» =
    SOME
      ([«coordinate»;«x0»;«x1»;«x2»;«x3»;«x4»;«x5»],
       bounded_case16594_object_delta_neg_center_value_body)
Proof
  rw [bounded_case16594_object_delta_neg_center_value_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_neg_center_value_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_center_value»
        [from_cv (Num coordinate);from_cv x0;from_cv x1;from_cv x2;
         from_cv x3;from_cv x4;from_cv x5]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«coordinate»,from_cv (Num coordinate));(«x0»,from_cv x0);
         («x1»,from_cv x1);(«x2»,from_cv x2);(«x3»,from_cv x3);
         («x4»,from_cv x4);(«x5»,from_cv x5)]
        bounded_case16594_object_delta_neg_center_value_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_literal_app7
  >> simp [bounded_case16594_object_delta_neg_center_value_lookup]
QED

Theorem bounded_case16594_object_delta_neg_center_value_eval:
  coordinate < 6 /\
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] /\
  65560 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_center_value»
        [from_cv (Num coordinate);from_cv x0;from_cv x1;from_cv x2;
         from_cv x3;from_cv x4;from_cv x5]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_neg_center_value_cv coordinate
          x0 x1 x2 x3 x4 x5)),refs)
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_gradient_six_cv
          x0 x1 x2 x3 x4 x5)` by
       (irule
          compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_packed_encoded
        >> simp [])
  >> `LENGTH
        (bounded_case16594_object_delta_gradient_six_cv
          x0 x1 x2 x3 x4 x5) = 6` by
       simp
         [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_length]
  >> `bounded_packed_q_interval_encoded
        (EL coordinate
          (bounded_case16594_object_delta_gradient_six_cv
            x0 x1 x2 x3 x4 x5))` by
       fs [listTheory.EVERY_EL]
  >> rw [bounded_case16594_object_delta_neg_center_value_unfold]
  >> simp
       [bounded_case16594_object_delta_neg_center_value_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_neg»
            [from_cv
              (EL coordinate
                (bounded_case16594_object_delta_gradient_six_cv
                  x0 x1 x2 x3 x4 x5))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaHessianSumsEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_interval_lookup»
                [from_cv (Num coordinate);
                 from_cv
                   (bounded_object_q_cv_list
                     (bounded_case16594_object_delta_gradient_six_cv
                       x0 x1 x2 x3 x4 x5))]) refs`
      >> conj_tac
      >- (irule
            compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
          >> simp
               [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
          >> irule
               compute_boundedCase16594ObjectDeltaGradientCompleteEvalTheory.bounded_case16594_object_delta_gradient_six_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> simp [compute_execTheory.from_cv_def]
      >> irule
           compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> rw [bounded_case16594_object_delta_neg_center_value_cv_def]
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_interval_neg_encoded_eval
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded
      >> asm_rewrite_tac [])
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_hessian6_row_cv_def:
  bounded_case16594_object_hessian6_row_cv coordinate packed =
    bounded_object_q_cv_list
      (EL coordinate (bounded_packed_q_source_hessian6_rows packed))
End

Definition bounded_case16594_object_hessian6_row_body_def:
  bounded_case16594_object_hessian6_row_body =
    App «candle_cv_q_interval_lookup»
      [Var «coordinate»;
       App «candle_cv_q_packed_hessian6_expand» [Var «packed»]]
End

Theorem bounded_case16594_object_hessian6_row_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_hessian6_row» =
    SOME
      ([«coordinate»;«packed»],
       bounded_case16594_object_hessian6_row_body)
Proof
  rw [bounded_case16594_object_hessian6_row_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_hessian6_row_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_hessian6_row»
        [from_cv (Num coordinate);
         from_cv (bounded_object_q_cv_list packed)]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«coordinate»,from_cv (Num coordinate));
         («packed»,from_cv (bounded_object_q_cv_list packed))]
        bounded_case16594_object_hessian6_row_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> simp [bounded_case16594_object_hessian6_row_lookup]
QED

Theorem bounded_case16594_object_hessian6_row_eval:
  coordinate < 6 /\ LENGTH packed = 21 /\ 68 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_hessian6_row»
        [from_cv (Num coordinate);
         from_cv (bounded_object_q_cv_list packed)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_hessian6_row_cv coordinate packed)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_hessian6_row_unfold]
  >> simp
       [bounded_case16594_object_hessian6_row_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_lookup»
            [from_cv (Num coordinate);
             from_cv
               (bounded_object_q_cv_list
                 (MAP bounded_object_q_cv_list
                   (bounded_packed_q_source_hessian6_rows packed)))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
      >> irule
           compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_hessian6_expand_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_execTheory.from_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `(M_success
          (from_cv
            (EL coordinate
              (MAP bounded_object_q_cv_list
                (bounded_packed_q_source_hessian6_rows packed)))),refs)`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
      >> simp
           [compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_hessian6_rows_def]
      >> intLib.ARITH_TAC)
  >> simp
       [bounded_case16594_object_hessian6_row_cv_def,
        listTheory.EL_MAP,
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_hessian6_rows_def]
QED

Theorem bounded_case16594_object_hessian6_selected_row_encoded_length:
  coordinate < 6 /\ LENGTH packed = 21 /\
  EVERY bounded_packed_q_interval_encoded packed ==>
  EVERY bounded_packed_q_interval_encoded
    (EL coordinate (bounded_packed_q_source_hessian6_rows packed)) /\
  LENGTH
    (EL coordinate (bounded_packed_q_source_hessian6_rows packed)) = 6
Proof
  strip_tac
  >> `EVERY (EVERY bounded_packed_q_interval_encoded)
        (bounded_packed_q_source_hessian6_rows packed)` by
       (irule
          compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_hessian6_rows_encoded
        >> simp [])
  >> `LENGTH (bounded_packed_q_source_hessian6_rows packed) = 6` by
       simp
         [compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_hessian6_rows_def]
  >> conj_tac >- fs [listTheory.EVERY_EL]
  >> `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
      coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` by
       intLib.ARITH_TAC
  >> fs
       [compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_hessian6_rows_def]
QED

Definition bounded_case16594_object_delta_neg_center_gradient_cv_def:
  bounded_case16594_object_delta_neg_center_gradient_cv coordinate
      x0 x1 x2 x3 x4 x5 =
    let packed_hessian =
          bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5;
        row =
          EL coordinate
            (bounded_packed_q_source_hessian6_rows packed_hessian)
    in
      bounded_object_q_cv_list
        (MAP bounded_object_q_interval_neg_cv row)
End

Definition bounded_case16594_object_delta_neg_center_gradient_body_def:
  bounded_case16594_object_delta_neg_center_gradient_body =
    App «candle_cv_q_dim_interval_list_neg»
      [App «candle_cv_q_packed_hessian6_row»
        [Var «coordinate»;
         App «candle_cv_q_packed_delta_hessian_six»
           [Var «x0»;Var «x1»;Var «x2»;
            Var «x3»;Var «x4»;Var «x5»]]]
End

Theorem bounded_case16594_object_delta_neg_center_gradient_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_neg_derivative_center_gradient» =
    SOME
      ([«coordinate»;«x0»;«x1»;«x2»;«x3»;«x4»;«x5»],
       bounded_case16594_object_delta_neg_center_gradient_body)
Proof
  rw [bounded_case16594_object_delta_neg_center_gradient_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_neg_center_gradient_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_center_gradient»
        [from_cv (Num coordinate);from_cv x0;from_cv x1;from_cv x2;
         from_cv x3;from_cv x4;from_cv x5]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«coordinate»,from_cv (Num coordinate));(«x0»,from_cv x0);
         («x1»,from_cv x1);(«x2»,from_cv x2);(«x3»,from_cv x3);
         («x4»,from_cv x4);(«x5»,from_cv x5)]
        bounded_case16594_object_delta_neg_center_gradient_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_literal_app7
  >> simp [bounded_case16594_object_delta_neg_center_gradient_lookup]
QED

Theorem bounded_case16594_object_delta_neg_center_gradient_eval:
  coordinate < 6 /\
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] /\
  131100 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_center_gradient»
        [from_cv (Num coordinate);from_cv x0;from_cv x1;from_cv x2;
         from_cv x3;from_cv x4;from_cv x5]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_neg_center_gradient_cv coordinate
          x0 x1 x2 x3 x4 x5)),refs)
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5) /\
      LENGTH
        (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5) = 21` by
       simp
         [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_packed_encoded,
          compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length]
  >> `EVERY bounded_packed_q_interval_encoded
        (EL coordinate
          (bounded_packed_q_source_hessian6_rows
            (bounded_object_q_delta_hessian_six_cv
              x0 x1 x2 x3 x4 x5))) /\
      LENGTH
        (EL coordinate
          (bounded_packed_q_source_hessian6_rows
            (bounded_object_q_delta_hessian_six_cv
              x0 x1 x2 x3 x4 x5))) = 6` by
       (irule bounded_case16594_object_hessian6_selected_row_encoded_length
        >> simp [])
  >> rw [bounded_case16594_object_delta_neg_center_gradient_unfold]
  >> simp
       [bounded_case16594_object_delta_neg_center_gradient_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_dim_interval_list_neg»
            [from_cv
              (bounded_case16594_object_hessian6_row_cv coordinate
                (bounded_object_q_delta_hessian_six_cv
                  x0 x1 x2 x3 x4 x5))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaHessianSumsEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_hessian6_row»
                [from_cv (Num coordinate);
                 from_cv
                   (bounded_object_q_cv_list
                     (bounded_object_q_delta_hessian_six_cv
                       x0 x1 x2 x3 x4 x5))]) refs`
      >> conj_tac
      >- (irule
            compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
          >> simp
               [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
          >> irule
               compute_boundedCase16594ObjectDeltaHessianSixEvalTheory.bounded_case16594_object_delta_hessian_six_eval
          >> simp [])
      >> irule bounded_case16594_object_hessian6_row_eval
      >> simp [])
  >> rw
       [bounded_case16594_object_delta_neg_center_gradient_cv_def,
        bounded_case16594_object_hessian6_row_cv_def]
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_interval_list_neg_encoded_eval
  >> simp []
  >> fs [listTheory.EVERY_MEM]
  >> metis_tac
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded]
QED

Theorem bounded_case16594_object_one_interval_packed_encoded[simp]:
  bounded_packed_q_interval_encoded
    bounded_case16594_object_one_interval_cv
Proof
  rw
    [compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_one_interval_cv_def]
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
  >> simp []
QED

Theorem bounded_case16594_object_named_zero_interval_packed_encoded[simp]:
  bounded_packed_q_interval_encoded
    bounded_case16594_object_zero_interval_cv
Proof
  PURE_REWRITE_TAC
    [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_zero_interval_identity]
  >> ACCEPT_TAC
       compute_boundedCase16594ObjectMulHessianEvalTheory.bounded_case16594_packed_zero_interval_encoded
QED

Theorem bounded_case16594_object_delta_basis_six_encoded_length:
  coordinate < 6 ==>
  EVERY bounded_packed_q_interval_encoded
    (bounded_case16594_object_delta_basis_six_cv coordinate) /\
  LENGTH (bounded_case16594_object_delta_basis_six_cv coordinate) = 6
Proof
  strip_tac
  >> `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
      coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` by
       intLib.ARITH_TAC
  >> fs
       [bounded_case16594_object_delta_basis_six_cv_def]
QED

Definition bounded_case16594_object_delta_neg_hessian_six_cv_def:
  bounded_case16594_object_delta_neg_hessian_six_cv coordinate =
    let basis = bounded_case16594_object_delta_basis_six_cv coordinate
    in
      bounded_object_q_cv_list
        (MAP bounded_object_q_interval_neg_cv
          (bounded_object_q_delta_hessian_six_cv
            (EL 0 basis) (EL 1 basis) (EL 2 basis)
            (EL 3 basis) (EL 4 basis) (EL 5 basis)))
End

Definition bounded_case16594_object_delta_neg_hessian_six_body_def:
  bounded_case16594_object_delta_neg_hessian_six_body =
    Let «basis»
      (App «candle_cv_q_packed_delta_basis_six» [Var «coordinate»])
      (App «candle_cv_q_dim_interval_list_neg»
        [App «candle_cv_q_packed_delta_hessian_six»
          [App «candle_cv_q_interval_lookup» [Num 0;Var «basis»];
           App «candle_cv_q_interval_lookup» [Num 1;Var «basis»];
           App «candle_cv_q_interval_lookup» [Num 2;Var «basis»];
           App «candle_cv_q_interval_lookup» [Num 3;Var «basis»];
           App «candle_cv_q_interval_lookup» [Num 4;Var «basis»];
           App «candle_cv_q_interval_lookup» [Num 5;Var «basis»]]])
End

Theorem bounded_case16594_object_delta_neg_hessian_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_neg_derivative_hessian_six» =
    SOME
      ([«coordinate»],bounded_case16594_object_delta_neg_hessian_six_body)
Proof
  rw [bounded_case16594_object_delta_neg_hessian_six_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_neg_hessian_six_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_hessian_six»
        [from_cv (Num coordinate)]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«coordinate»,from_cv (Num coordinate))]
        bounded_case16594_object_delta_neg_hessian_six_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> simp [bounded_case16594_object_delta_neg_hessian_six_lookup]
QED

Theorem bounded_case16594_object_delta_neg_hessian_six_eval:
  coordinate < 6 /\ 262200 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_hessian_six»
        [from_cv (Num coordinate)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_neg_hessian_six_cv coordinate)),refs)
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_basis_six_cv coordinate) /\
      LENGTH (bounded_case16594_object_delta_basis_six_cv coordinate) = 6` by
       simp [bounded_case16594_object_delta_basis_six_encoded_length]
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 (bounded_case16594_object_delta_basis_six_cv coordinate);
         EL 1 (bounded_case16594_object_delta_basis_six_cv coordinate);
         EL 2 (bounded_case16594_object_delta_basis_six_cv coordinate);
         EL 3 (bounded_case16594_object_delta_basis_six_cv coordinate);
         EL 4 (bounded_case16594_object_delta_basis_six_cv coordinate);
         EL 5 (bounded_case16594_object_delta_basis_six_cv coordinate)]` by
       fs [listTheory.EVERY_EL]
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_object_q_delta_hessian_six_cv
          (EL 0 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 1 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 2 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 3 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 4 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 5 (bounded_case16594_object_delta_basis_six_cv coordinate))) /\
      LENGTH
        (bounded_object_q_delta_hessian_six_cv
          (EL 0 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 1 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 2 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 3 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 4 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 5 (bounded_case16594_object_delta_basis_six_cv coordinate))) = 21` by
       simp
         [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_packed_encoded,
          compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length]
  >> rw [bounded_case16594_object_delta_neg_hessian_six_unfold]
  >> simp
       [bounded_case16594_object_delta_neg_hessian_six_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_cv_list
          (bounded_case16594_object_delta_basis_six_cv coordinate)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          bounded_case16594_object_delta_basis_six_eval)
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 2)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_dim_interval_list_neg»
            [from_cv
              (bounded_object_q_cv_list
                (bounded_object_q_delta_hessian_six_cv
                  (EL 0
                    (bounded_case16594_object_delta_basis_six_cv coordinate))
                  (EL 1
                    (bounded_case16594_object_delta_basis_six_cv coordinate))
                  (EL 2
                    (bounded_case16594_object_delta_basis_six_cv coordinate))
                  (EL 3
                    (bounded_case16594_object_delta_basis_six_cv coordinate))
                  (EL 4
                    (bounded_case16594_object_delta_basis_six_cv coordinate))
                  (EL 5
                    (bounded_case16594_object_delta_basis_six_cv coordinate))))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaHessianSumsEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectDeltaProductOuterHessianEvalTheory.bounded_case16594_object_delta_hessian_environment_eval
      >> simp [])
  >> rw [bounded_case16594_object_delta_neg_hessian_six_cv_def]
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_interval_list_neg_encoded_eval
  >> simp []
  >> fs [listTheory.EVERY_MEM]
  >> metis_tac
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded]
QED

Definition bounded_case16594_object_delta_neg_hessian_six_list_cv_def:
  bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate =
    let basis = bounded_case16594_object_delta_basis_six_cv coordinate
    in
      MAP bounded_object_q_interval_neg_cv
        (bounded_object_q_delta_hessian_six_cv
          (EL 0 basis) (EL 1 basis) (EL 2 basis)
          (EL 3 basis) (EL 4 basis) (EL 5 basis))
End

Theorem bounded_case16594_object_delta_neg_hessian_six_list_identity:
  bounded_case16594_object_delta_neg_hessian_six_cv coordinate =
    bounded_object_q_cv_list
      (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate)
Proof
  rw
    [bounded_case16594_object_delta_neg_hessian_six_cv_def,
     bounded_case16594_object_delta_neg_hessian_six_list_cv_def]
QED

Theorem bounded_case16594_object_delta_neg_hessian_six_encoded_length:
  coordinate < 6 ==>
  EVERY bounded_packed_q_interval_encoded
    (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) = 21
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_basis_six_cv coordinate) /\
      LENGTH (bounded_case16594_object_delta_basis_six_cv coordinate) = 6` by
       simp [bounded_case16594_object_delta_basis_six_encoded_length]
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 (bounded_case16594_object_delta_basis_six_cv coordinate);
         EL 1 (bounded_case16594_object_delta_basis_six_cv coordinate);
         EL 2 (bounded_case16594_object_delta_basis_six_cv coordinate);
         EL 3 (bounded_case16594_object_delta_basis_six_cv coordinate);
         EL 4 (bounded_case16594_object_delta_basis_six_cv coordinate);
         EL 5 (bounded_case16594_object_delta_basis_six_cv coordinate)]` by
       fs [listTheory.EVERY_EL]
  >> PURE_REWRITE_TAC
       [bounded_case16594_object_delta_neg_hessian_six_list_cv_def]
  >> simp
       [LET_THM,listTheory.EVERY_MAP,
        compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length]
  >> irule listTheory.EVERY_MONOTONIC
  >> qexists_tac `bounded_packed_q_interval_encoded`
  >> conj_tac
  >- simp
       [compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_neg_packed_encoded]
  >> irule
       compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_packed_encoded
  >> fs [listTheory.EL]
QED

Definition bounded_case16594_object_delta_neg_jet_six_cv_def:
  bounded_case16594_object_delta_neg_jet_six_cv coordinate
      x0 x1 x2 x3 x4 x5 =
    Pair
      (bounded_case16594_object_delta_neg_center_value_cv coordinate
        x0 x1 x2 x3 x4 x5)
      (Pair
        (bounded_case16594_object_delta_neg_center_gradient_cv coordinate
          x0 x1 x2 x3 x4 x5)
        (bounded_object_q_cv_list
          (MAP bounded_object_q_cv_list
            (bounded_packed_q_source_hessian6_rows
              (bounded_case16594_object_delta_neg_hessian_six_list_cv
                coordinate)))))
End

Definition bounded_case16594_object_delta_neg_jet_six_body_def:
  bounded_case16594_object_delta_neg_jet_six_body =
    App «candle_cv_q_dim_jet_make»
      [App «candle_cv_q_packed_delta_neg_derivative_center_value»
        [Var «coordinate»;Var «x0»;Var «x1»;Var «x2»;
         Var «x3»;Var «x4»;Var «x5»];
       App «candle_cv_q_packed_delta_neg_derivative_center_gradient»
        [Var «coordinate»;Var «x0»;Var «x1»;Var «x2»;
         Var «x3»;Var «x4»;Var «x5»];
       App «candle_cv_q_packed_hessian6_expand»
        [App «candle_cv_q_packed_delta_neg_derivative_hessian_six»
          [Var «coordinate»]]]
End

Theorem bounded_case16594_object_delta_neg_jet_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_neg_derivative_jet_six» =
    SOME
      ([«coordinate»;«x0»;«x1»;«x2»;«x3»;«x4»;«x5»],
       bounded_case16594_object_delta_neg_jet_six_body)
Proof
  rw [bounded_case16594_object_delta_neg_jet_six_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_neg_jet_six_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_jet_six»
        [from_cv (Num coordinate);from_cv x0;from_cv x1;from_cv x2;
         from_cv x3;from_cv x4;from_cv x5]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«coordinate»,from_cv (Num coordinate));(«x0»,from_cv x0);
         («x1»,from_cv x1);(«x2»,from_cv x2);(«x3»,from_cv x3);
         («x4»,from_cv x4);(«x5»,from_cv x5)]
        bounded_case16594_object_delta_neg_jet_six_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_literal_app7
  >> simp [bounded_case16594_object_delta_neg_jet_six_lookup]
QED

Theorem bounded_case16594_object_delta_neg_jet_six_eval:
  coordinate < 6 /\
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] /\
  262400 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_jet_six»
        [from_cv (Num coordinate);from_cv x0;from_cv x1;from_cv x2;
         from_cv x3;from_cv x4;from_cv x5]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_neg_jet_six_cv coordinate
          x0 x1 x2 x3 x4 x5)),refs)
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) /\
      LENGTH
        (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) = 21` by
       simp [bounded_case16594_object_delta_neg_hessian_six_encoded_length]
  >> rw [bounded_case16594_object_delta_neg_jet_six_unfold]
  >> simp
       [bounded_case16594_object_delta_neg_jet_six_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_dim_jet_make»
            [from_cv
              (bounded_case16594_object_delta_neg_center_value_cv coordinate
                x0 x1 x2 x3 x4 x5);
             from_cv
              (bounded_case16594_object_delta_neg_center_gradient_cv coordinate
                x0 x1 x2 x3 x4 x5);
             from_cv
              (bounded_object_q_cv_list
                (MAP bounded_object_q_cv_list
                  (bounded_packed_q_source_hessian6_rows
                    (bounded_case16594_object_delta_neg_hessian_six_list_cv
                      coordinate))))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_app3_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              bounded_case16594_object_delta_neg_center_value_eval)
          >> simp [])
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              bounded_case16594_object_delta_neg_center_gradient_eval)
          >> simp [])
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_hessian6_expand»
                [from_cv
                  (bounded_object_q_cv_list
                    (bounded_case16594_object_delta_neg_hessian_six_list_cv
                      coordinate))]) refs`
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectDeltaHessianSumsEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
          >> conj_tac >- intLib.ARITH_TAC
          >> irule
               (SIMP_RULE std_ss
                 [compute_execTheory.from_cv_def,
                  bounded_case16594_object_delta_neg_hessian_six_list_identity]
                 bounded_case16594_object_delta_neg_hessian_six_eval)
          >> intLib.ARITH_TAC)
      >> irule
           compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_hessian6_expand_eval
      >> simp [])
  >> rw [bounded_case16594_object_delta_neg_jet_six_cv_def]
  >> irule
       compute_boundedCase16594ObjectDeltaProductJetCompleteEvalTheory.bounded_case16594_object_q_dim_jet_make_eval
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_delta_neg_jet_environment_body_def:
  bounded_case16594_object_delta_neg_jet_environment_body =
    App «candle_cv_q_packed_delta_neg_derivative_jet_six»
      [Var «coordinate»;
       App «candle_cv_q_interval_lookup» [Num 0;Var «environment»];
       App «candle_cv_q_interval_lookup» [Num 1;Var «environment»];
       App «candle_cv_q_interval_lookup» [Num 2;Var «environment»];
       App «candle_cv_q_interval_lookup» [Num 3;Var «environment»];
       App «candle_cv_q_interval_lookup» [Num 4;Var «environment»];
       App «candle_cv_q_interval_lookup» [Num 5;Var «environment»]]
End

Theorem bounded_case16594_object_delta_neg_jet_environment_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_neg_derivative_jet_environment» =
    SOME
      ([«coordinate»;«environment»],
       bounded_case16594_object_delta_neg_jet_environment_body)
Proof
  rw [bounded_case16594_object_delta_neg_jet_environment_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_neg_jet_environment_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_jet_environment»
        [from_cv (Num coordinate);
         from_cv (bounded_object_q_cv_list environment)]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«coordinate»,from_cv (Num coordinate));
         («environment»,from_cv (bounded_object_q_cv_list environment))]
        bounded_case16594_object_delta_neg_jet_environment_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> simp [bounded_case16594_object_delta_neg_jet_environment_lookup]
QED

Theorem bounded_case16594_object_delta_neg_jet_environment_eval:
  coordinate < 6 /\ LENGTH environment = 6 /\
  EVERY bounded_packed_q_interval_encoded environment /\
  262420 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_jet_environment»
        [from_cv (Num coordinate);
         from_cv (bounded_object_q_cv_list environment)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_neg_jet_six_cv coordinate
          (EL 0 environment) (EL 1 environment) (EL 2 environment)
          (EL 3 environment) (EL 4 environment) (EL 5 environment))),refs)
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 environment;EL 1 environment;EL 2 environment;
         EL 3 environment;EL 4 environment;EL 5 environment]` by
       fs [listTheory.EVERY_EL]
  >> rw [bounded_case16594_object_delta_neg_jet_environment_unfold]
  >> simp
       [bounded_case16594_object_delta_neg_jet_environment_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_neg_derivative_jet_six»
            [from_cv (Num coordinate);from_cv (HD environment);
             from_cv (EL 1 environment);from_cv (EL 2 environment);
             from_cv (EL 3 environment);from_cv (EL 4 environment);
             from_cv (EL 5 environment)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_app7_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp
           [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
      >> conj_tac
      >- (irule EQ_TRANS
          >> qexists_tac `(M_success (from_cv (EL 0 environment)),refs)`
          >> conj_tac
          >- (irule
                compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
              >> simp [] >> intLib.ARITH_TAC)
          >> simp [listTheory.EL])
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> irule
           compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_delta_neg_jet_six_eval
  >> fs [listTheory.EL]
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_delta_neg_center_gradient_list_cv_def:
  bounded_case16594_object_delta_neg_center_gradient_list_cv coordinate
      x0 x1 x2 x3 x4 x5 =
    let packed_hessian =
          bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5;
        row =
          EL coordinate
            (bounded_packed_q_source_hessian6_rows packed_hessian)
    in
      MAP bounded_object_q_interval_neg_cv row
End

Theorem bounded_case16594_object_delta_neg_center_gradient_list_identity:
  bounded_case16594_object_delta_neg_center_gradient_cv coordinate
      x0 x1 x2 x3 x4 x5 =
    bounded_object_q_cv_list
      (bounded_case16594_object_delta_neg_center_gradient_list_cv coordinate
        x0 x1 x2 x3 x4 x5)
Proof
  rw
    [bounded_case16594_object_delta_neg_center_gradient_cv_def,
     bounded_case16594_object_delta_neg_center_gradient_list_cv_def]
QED

Theorem bounded_case16594_object_delta_neg_center_components_encoded:
  coordinate < 6 /\
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] ==>
  bounded_packed_q_interval_encoded
    (bounded_case16594_object_delta_neg_center_value_cv coordinate
      x0 x1 x2 x3 x4 x5) /\
  EVERY bounded_packed_q_interval_encoded
    (bounded_case16594_object_delta_neg_center_gradient_list_cv coordinate
      x0 x1 x2 x3 x4 x5) /\
  LENGTH
    (bounded_case16594_object_delta_neg_center_gradient_list_cv coordinate
      x0 x1 x2 x3 x4 x5) = 6
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_gradient_six_cv
          x0 x1 x2 x3 x4 x5) /\
      LENGTH
        (bounded_case16594_object_delta_gradient_six_cv
          x0 x1 x2 x3 x4 x5) = 6` by
       simp
         [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_packed_encoded,
          compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_length]
  >> `bounded_packed_q_interval_encoded
        (EL coordinate
          (bounded_case16594_object_delta_gradient_six_cv
            x0 x1 x2 x3 x4 x5))` by
       fs [listTheory.EVERY_EL]
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5) /\
      LENGTH
        (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5) = 21` by
       simp
         [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_packed_encoded,
          compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length]
  >> `EVERY bounded_packed_q_interval_encoded
        (EL coordinate
          (bounded_packed_q_source_hessian6_rows
            (bounded_object_q_delta_hessian_six_cv
              x0 x1 x2 x3 x4 x5))) /\
      LENGTH
        (EL coordinate
          (bounded_packed_q_source_hessian6_rows
            (bounded_object_q_delta_hessian_six_cv
              x0 x1 x2 x3 x4 x5))) = 6` by
       (irule bounded_case16594_object_hessian6_selected_row_encoded_length
        >> simp [])
  >> conj_tac
  >- (rw [bounded_case16594_object_delta_neg_center_value_cv_def]
      >> irule
           compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_neg_packed_encoded
      >> asm_rewrite_tac [])
  >> PURE_REWRITE_TAC
       [bounded_case16594_object_delta_neg_center_gradient_list_cv_def]
  >> simp [LET_THM,listTheory.EVERY_MAP]
  >> irule listTheory.EVERY_MONOTONIC
  >> qexists_tac `bounded_packed_q_interval_encoded`
  >> simp
       [compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_neg_packed_encoded]
QED

Definition bounded_case16594_object_delta_neg_center_value_environment_cv_def:
  bounded_case16594_object_delta_neg_center_value_environment_cv
      center_boxes coordinate =
    bounded_case16594_object_delta_neg_center_value_cv coordinate
      (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
      (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes)
End

Definition bounded_case16594_object_delta_neg_center_gradient_environment_cv_def:
  bounded_case16594_object_delta_neg_center_gradient_environment_cv
      center_boxes coordinate =
    bounded_case16594_object_delta_neg_center_gradient_list_cv coordinate
      (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
      (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes)
End

Definition bounded_case16594_object_delta_neg_center_hessian_cv_def:
  bounded_case16594_object_delta_neg_center_hessian_cv coordinate =
    bounded_object_q_cv_list
      (MAP bounded_object_q_cv_list
        (bounded_packed_q_source_hessian6_rows
          (bounded_case16594_object_delta_neg_hessian_six_list_cv
            coordinate)))
End

Theorem bounded_case16594_object_delta_neg_center_jet_decomposition:
  LENGTH center_boxes = 6 ==>
  bounded_case16594_object_delta_neg_jet_six_cv coordinate
      (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
      (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes) =
    Pair
      (bounded_case16594_object_delta_neg_center_value_environment_cv
        center_boxes coordinate)
      (Pair
        (bounded_object_q_cv_list
          (bounded_case16594_object_delta_neg_center_gradient_environment_cv
            center_boxes coordinate))
        (bounded_case16594_object_delta_neg_center_hessian_cv coordinate))
Proof
  strip_tac
  >> rw
       [bounded_case16594_object_delta_neg_jet_six_cv_def,
        bounded_case16594_object_delta_neg_center_value_environment_cv_def,
        bounded_case16594_object_delta_neg_center_gradient_environment_cv_def,
        bounded_case16594_object_delta_neg_center_hessian_cv_def,
        bounded_case16594_object_delta_neg_center_gradient_list_identity]
QED

Definition bounded_case16594_object_delta_neg_source_state_cv_def:
  bounded_case16594_object_delta_neg_source_state_cv
      radii center_boxes coordinate =
    let center_value =
          bounded_case16594_object_delta_neg_center_value_environment_cv
            center_boxes coordinate;
        center_gradient =
          bounded_case16594_object_delta_neg_center_gradient_environment_cv
            center_boxes coordinate;
        packed_hessian =
          bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate
    in
      bounded_case16594_object_state_cv
        (Num 1) center_value
        (bounded_object_q_cv_list center_gradient)
        (bounded_packed_q_source_value_bound6_cv
          radii center_value center_gradient packed_hessian)
        (bounded_object_q_cv_list
          (bounded_packed_q_source_gradient_complete6_cv
            radii center_gradient packed_hessian))
        (bounded_object_q_cv_list packed_hessian)
End

Theorem bounded_case16594_object_delta_neg_source_state_eval:
  coordinate < 6 /\
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_boxes /\
  LENGTH center_boxes = 6 /\ 262500 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (Num coordinate)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_neg_source_state_cv
          radii center_boxes coordinate)),refs)
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 center_boxes;EL 1 center_boxes;EL 2 center_boxes;
         EL 3 center_boxes;EL 4 center_boxes;EL 5 center_boxes]` by
       fs [listTheory.EVERY_EL]
  >> `bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_neg_center_value_environment_cv
          center_boxes coordinate) /\
      EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_neg_center_gradient_environment_cv
          center_boxes coordinate) /\
      LENGTH
        (bounded_case16594_object_delta_neg_center_gradient_environment_cv
          center_boxes coordinate) = 6` by
       (PURE_REWRITE_TAC
          [bounded_case16594_object_delta_neg_center_value_environment_cv_def,
           bounded_case16594_object_delta_neg_center_gradient_environment_cv_def]
        >> irule bounded_case16594_object_delta_neg_center_components_encoded
        >> simp [])
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) /\
      LENGTH
        (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) = 21` by
       simp [bounded_case16594_object_delta_neg_hessian_six_encoded_length]
  >> PURE_REWRITE_TAC
       [bounded_case16594_object_delta_neg_source_state_cv_def,LET_THM]
  >> BETA_TAC
  >> irule
       compute_boundedCase16594ObjectDeltaNegSourceItemEvalTheory.bounded_case16594_object_delta_neg_source_item_state_eval
  >> simp []
  >> conj_tac
  >- (qexists_tac
        `bounded_case16594_object_delta_neg_center_hessian_cv coordinate`
      >> irule EQ_TRANS
      >> qexists_tac
           `(M_success
              (from_cv
                (bounded_case16594_object_delta_neg_jet_six_cv coordinate
                  (EL 0 center_boxes) (EL 1 center_boxes)
                  (EL 2 center_boxes) (EL 3 center_boxes)
                  (EL 4 center_boxes) (EL 5 center_boxes))),refs)`
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              bounded_case16594_object_delta_neg_jet_environment_eval)
          >> simp [])
      >> simp [bounded_case16594_object_delta_neg_center_jet_decomposition])
  >> irule
       (SIMP_RULE std_ss
         [compute_execTheory.from_cv_def,
          bounded_case16594_object_delta_neg_hessian_six_list_identity]
         bounded_case16594_object_delta_neg_hessian_six_eval)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
