(*****************************************************************************
 * Production evaluator semantics for a successful genuine object atan step.
 * The expensive authentic guard and the unary state constructor are kept in
 * separate preceding theories; this layer authenticates the exact step body
 * and packages the successful state/stack result.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanStepEval
Ancestors
  compute_boundedCase16594ObjectAtanStateEval
  compute_boundedCase16594ObjectCertificateListEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_atan_step_body_def:
  bounded_case16594_object_atan_step_body =
    If (Uop Ispair (Var «stack»))
      (If (App «candle_cv_cval_list_has» [Num 8;Var «certificates»])
        (Let «item» (Uop Fst (Var «stack»))
          (Let «center_input»
            (App «candle_cv_cval_list_nth» [Num 0;Var «certificates»])
            (Let «box_input»
              (App «candle_cv_cval_list_nth» [Num 1;Var «certificates»])
              (Let «center_result»
                (App «candle_cv_cval_list_nth» [Num 2;Var «certificates»])
                (Let «center_square»
                  (App «candle_cv_cval_list_nth» [Num 3;Var «certificates»])
                  (Let «center_derivative»
                    (App «candle_cv_cval_list_nth» [Num 4;Var «certificates»])
                    (Let «box_square»
                      (App «candle_cv_cval_list_nth» [Num 5;Var «certificates»])
                      (Let «box_derivative»
                        (App «candle_cv_cval_list_nth» [Num 6;Var «certificates»])
                        (Let «box_derivative_square»
                          (App «candle_cv_cval_list_nth» [Num 7;Var «certificates»])
                          (Let «certificate_rest»
                            (App «candle_cv_cval_list_drop»
                              [Num 8;Var «certificates»])
                            (If
                              (App «candle_cv_bool_and»
                                [App «candle_cv_q_interval_atn_outer_certificate»
                                   [App
                                      «candle_cv_q_packed_object_state_center_value»
                                      [Var «item»];
                                    Var «center_input»;
                                    Var «center_result»];
                                 App «candle_cv_bool_and»
                                   [App
                                      «candle_cv_q_interval_square_outer_certificate»
                                      [App
                                         «candle_cv_q_packed_object_state_center_value»
                                         [Var «item»];
                                       Var «center_input»;
                                       Var «center_square»];
                                    App «candle_cv_bool_and»
                                      [App «candle_cv_q_interval_inv_certificate»
                                         [App
                                            «candle_cv_q_packed_object_atn_denominator»
                                            [Var «center_square»];
                                          Var «center_derivative»];
                                       App «candle_cv_bool_and»
                                         [App
                                            «candle_cv_q_interval_square_outer_certificate»
                                            [App
                                               «candle_cv_q_packed_object_state_value_bound»
                                               [Var «item»];
                                             Var «box_input»;
                                             Var «box_square»];
                                          App «candle_cv_bool_and»
                                            [App
                                               «candle_cv_q_interval_inv_certificate»
                                               [App
                                                  «candle_cv_q_packed_object_atn_denominator»
                                                  [Var «box_square»];
                                                Var «box_derivative»];
                                             App
                                               «candle_cv_q_interval_square_outer_certificate»
                                               [Var «box_derivative»;
                                                Var «box_derivative»;
                                                Var
                                                  «box_derivative_square»]]]]]])
                              (Pair (Num 1)
                                (Pair
                                  (Pair
                                    (App
                                      «candle_cv_q_packed_object_state_atn»
                                      [Var «radii»;Var «center_result»;
                                       Var «center_derivative»;
                                       Var «box_derivative»;
                                       Var «box_derivative_square»;
                                       Var «item»])
                                    (Uop Snd (Var «stack»)))
                                  (Var «certificate_rest»)))
                              (Pair (Num 0)
                                (Pair (Var «stack»)
                                  (Var «certificates»))))))))))))))
        (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
      (Pair (Num 0) (Pair (Var «stack») (Var «certificates»)))
End

Definition bounded_case16594_object_atan_step_success_expression_def:
  bounded_case16594_object_atan_step_success_expression radii item
      stack_rest center_result center_derivative box_derivative
      box_derivative_square certificate_rest =
    Pair (Num 1)
      (Pair
        (Pair
          (App «candle_cv_q_packed_object_state_atn»
            [from_cv radii;from_cv center_result;from_cv center_derivative;
             from_cv box_derivative;from_cv box_derivative_square;
             from_cv item])
          (from_cv stack_rest))
        (from_cv certificate_rest))
End

Theorem bounded_case16594_object_atan_step_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_atn_step» =
    SOME
      ([«radii»;«certificates»;«stack»],
       bounded_case16594_object_atan_step_body)
Proof
  rw [bounded_case16594_object_atan_step_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_atan_step_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_atn_step»
        [from_cv radii;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);(«certificates»,from_cv certificates);
         («stack»,from_cv stack)]
        bounded_case16594_object_atan_step_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> simp [bounded_case16594_object_atan_step_lookup]
QED

Theorem bounded_case16594_object_atan_step_success_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_result /\
  bounded_packed_q_interval_encoded center_derivative /\
  bounded_packed_q_interval_encoded box_derivative /\
  bounded_packed_q_interval_encoded box_derivative_square /\
  bounded_packed_q_interval_encoded value_bound /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  8194 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (bounded_case16594_object_atan_step_success_expression
        (bounded_object_q_cv_list radii)
        (bounded_case16594_object_state_cv domain_cv center_value
          (bounded_object_q_cv_list center_gradient) value_bound
          (bounded_object_q_cv_list gradient_bounds)
          (bounded_object_q_cv_list packed_hessian))
        stack_rest center_result center_derivative box_derivative
        box_derivative_square certificate_rest) (refs:hol_refs) =
    (M_success
      (Pair (Num 1)
        (Pair
          (Pair
            (from_cv
              (bounded_case16594_object_state_unary_cv radii domain_cv
                center_result center_derivative box_derivative
                (bounded_object_q_atan_second_cv
                  value_bound box_derivative_square)
                center_gradient gradient_bounds packed_hessian))
            (from_cv stack_rest))
          (from_cv certificate_rest))),refs)
Proof
  strip_tac
  >> rewrite_tac
       [bounded_case16594_object_atan_step_success_expression_def]
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
            compute_boundedCase16594ObjectAtanStateEvalTheory.bounded_case16594_object_state_atan_eval
          >> simp [])
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

val _ = export_theory ();
