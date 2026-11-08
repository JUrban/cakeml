(*****************************************************************************
 * Exact evaluator semantics for the six-component gradient of 4*x_i*delta.
 *
 * This composes the generic entry theorem at derivative coordinates 0..5
 * and then authenticates the production six-element packed constructor.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductGradientSixEval
Ancestors
  compute_boundedCase16594ObjectDeltaProductGradientEntryEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_product_center_gradient_six_body_def:
  bounded_case16594_object_delta_product_center_gradient_six_body =
    App «candle_cv_q_packed_delta_six»
      [App «candle_cv_q_packed_delta_product_center_gradient_entry»
        [Var «coordinate»;Var «coordinate_value»;Var «delta_value»;
         Var «delta_gradient»;Num 0];
       App «candle_cv_q_packed_delta_product_center_gradient_entry»
        [Var «coordinate»;Var «coordinate_value»;Var «delta_value»;
         Var «delta_gradient»;Num 1];
       App «candle_cv_q_packed_delta_product_center_gradient_entry»
        [Var «coordinate»;Var «coordinate_value»;Var «delta_value»;
         Var «delta_gradient»;Num 2];
       App «candle_cv_q_packed_delta_product_center_gradient_entry»
        [Var «coordinate»;Var «coordinate_value»;Var «delta_value»;
         Var «delta_gradient»;Num 3];
       App «candle_cv_q_packed_delta_product_center_gradient_entry»
        [Var «coordinate»;Var «coordinate_value»;Var «delta_value»;
         Var «delta_gradient»;Num 4];
       App «candle_cv_q_packed_delta_product_center_gradient_entry»
        [Var «coordinate»;Var «coordinate_value»;Var «delta_value»;
         Var «delta_gradient»;Num 5]]
End

Definition bounded_case16594_object_delta_product_center_gradient_six_cv_def:
  bounded_case16594_object_delta_product_center_gradient_six_cv
      coordinate coordinate_value delta_value delta_gradient =
    bounded_object_q_cv_list
      [bounded_case16594_object_delta_product_center_gradient_entry_cv
         coordinate coordinate_value delta_value delta_gradient 0;
       bounded_case16594_object_delta_product_center_gradient_entry_cv
         coordinate coordinate_value delta_value delta_gradient 1;
       bounded_case16594_object_delta_product_center_gradient_entry_cv
         coordinate coordinate_value delta_value delta_gradient 2;
       bounded_case16594_object_delta_product_center_gradient_entry_cv
         coordinate coordinate_value delta_value delta_gradient 3;
       bounded_case16594_object_delta_product_center_gradient_entry_cv
         coordinate coordinate_value delta_value delta_gradient 4;
       bounded_case16594_object_delta_product_center_gradient_entry_cv
         coordinate coordinate_value delta_value delta_gradient 5]
End

Theorem bounded_case16594_object_delta_product_center_gradient_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_product_center_gradient_six» =
    SOME
      ([«coordinate»;«coordinate_value»;«delta_value»;«delta_gradient»],
       bounded_case16594_object_delta_product_center_gradient_six_body)
Proof
  rw [bounded_case16594_object_delta_product_center_gradient_six_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_product_center_gradient_six_eval:
  bounded_packed_q_interval_encoded coordinate_value /\
  bounded_packed_q_interval_encoded delta_value /\
  EVERY bounded_packed_q_interval_encoded delta_gradient /\
  LENGTH delta_gradient = 6 /\
  50 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_center_gradient_six»
        [from_cv (compute_exec$Num coordinate);from_cv coordinate_value;
         from_cv delta_value;
         from_cv (bounded_object_q_cv_list delta_gradient)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_product_center_gradient_six_cv
          coordinate coordinate_value delta_value delta_gradient)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«coordinate»,from_cv (compute_exec$Num coordinate));
             («coordinate_value»,from_cv coordinate_value);
             («delta_value»,from_cv delta_value);
             («delta_gradient»,
               from_cv (bounded_object_q_cv_list delta_gradient))]
            bounded_case16594_object_delta_product_center_gradient_six_body)
          refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectInverseControlEvalTheory.bounded_case16594_object_compute_eval_literal_app4
      >> simp []
      >> ACCEPT_TAC
           bounded_case16594_object_delta_product_center_gradient_six_lookup)
  >> simp
       [bounded_case16594_object_delta_product_center_gradient_six_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_execTheory.from_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_six»
            [from_cv
               (bounded_case16594_object_delta_product_center_gradient_entry_cv
                 coordinate coordinate_value delta_value delta_gradient 0);
             from_cv
               (bounded_case16594_object_delta_product_center_gradient_entry_cv
                 coordinate coordinate_value delta_value delta_gradient 1);
             from_cv
               (bounded_case16594_object_delta_product_center_gradient_entry_cv
                 coordinate coordinate_value delta_value delta_gradient 2);
             from_cv
               (bounded_case16594_object_delta_product_center_gradient_entry_cv
                 coordinate coordinate_value delta_value delta_gradient 3);
             from_cv
               (bounded_case16594_object_delta_product_center_gradient_entry_cv
                 coordinate coordinate_value delta_value delta_gradient 4);
             from_cv
               (bounded_case16594_object_delta_product_center_gradient_entry_cv
                 coordinate coordinate_value delta_value delta_gradient 5)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
      >> simp
           [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              compute_boundedCase16594ObjectDeltaProductGradientEntryEvalTheory.bounded_case16594_object_delta_product_center_gradient_entry_eval]
      >> intLib.ARITH_TAC)
  >> rw
       [bounded_case16594_object_delta_product_center_gradient_six_cv_def]
  >> irule
       compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_delta_six_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
