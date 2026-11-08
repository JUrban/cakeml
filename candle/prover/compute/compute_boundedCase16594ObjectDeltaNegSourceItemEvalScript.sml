(*****************************************************************************
 * Structural evaluator semantics for one -d(delta)/dx_i source-item state.
 *
 * The numerical center jet and packed Hessian remain premises.  This proves
 * the authenticated production wrapper and state recompletion once, so the
 * complete arbitrary-input evaluator only has to supply those two components.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaNegSourceItemEval
Ancestors
  compute_boundedCase16594ObjectDeltaProductSourceItemEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_neg_source_item_state_body_def:
  bounded_case16594_object_delta_neg_source_item_state_body =
    Let «center_jet»
      (App «candle_cv_q_packed_delta_neg_derivative_jet_environment»
        [Var «coordinate»;Var «center_boxes»])
      (Let «packed_hessian»
        (App «candle_cv_q_packed_delta_neg_derivative_hessian_six»
          [Var «coordinate»])
        (App «candle_cv_q_packed_object_state_recomplete»
          [Var «radii»;Num 1;
           App «candle_cv_q_dim_jet_f» [Var «center_jet»];
           App «candle_cv_q_dim_jet_gradient» [Var «center_jet»];
           Var «packed_hessian»]))
End

Theorem bounded_case16594_object_delta_neg_source_item_state_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_delta_neg_derivative_item_state» =
    SOME
      ([«radii»;«center_boxes»;«coordinate»],
       bounded_case16594_object_delta_neg_source_item_state_body)
Proof
  rw [bounded_case16594_object_delta_neg_source_item_state_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_neg_source_item_state_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv radii;from_cv center_boxes;from_cv coordinate])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);(«center_boxes»,from_cv center_boxes);
         («coordinate»,from_cv coordinate)]
        bounded_case16594_object_delta_neg_source_item_state_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> simp [bounded_case16594_object_delta_neg_source_item_state_lookup]
QED

Theorem bounded_case16594_object_delta_neg_source_item_state_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  4100 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_jet_environment»
        [from_cv coordinate;from_cv center_boxes]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair center_value
          (Pair (bounded_object_q_cv_list center_gradient) center_hessian))),
     refs) /\
  compute_eval (clock - 2) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_hessian_six»
        [from_cv coordinate]) refs =
    (M_success
      (from_cv (bounded_object_q_cv_list packed_hessian)),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv (bounded_object_q_cv_list radii);from_cv center_boxes;
         from_cv coordinate]) refs =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv
          (Num 1) center_value
          (bounded_object_q_cv_list center_gradient)
          (bounded_packed_q_source_value_bound6_cv
            radii center_value center_gradient packed_hessian)
          (bounded_object_q_cv_list
            (bounded_packed_q_source_gradient_complete6_cv
              radii center_gradient packed_hessian))
          (bounded_object_q_cv_list packed_hessian))),refs)
Proof
  strip_tac
  >> `0 < clock` by intLib.ARITH_TAC
  >> PURE_ONCE_REWRITE_TAC
       [MATCH_MP
          (Q.SPECL
            [`refs`,`bounded_object_q_cv_list radii`,`coordinate`,`clock`,
             `center_boxes`]
            (GEN_ALL
              bounded_case16594_object_delta_neg_source_item_state_unfold))
          (ASSUME ``0:num < clock``)]
  >> simp
       [bounded_case16594_object_delta_neg_source_item_state_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `Pair center_value
          (Pair (bounded_object_q_cv_list center_gradient) center_hessian)`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_object_q_cv_list packed_hessian`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 3)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_recomplete»
            [from_cv (bounded_object_q_cv_list radii);from_cv (Num 1);
             from_cv center_value;
             from_cv (bounded_object_q_cv_list center_gradient);
             from_cv (bounded_object_q_cv_list packed_hessian)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyTraceEvalTheory.bounded_case16594_object_compute_eval_app5_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_execTheory.from_cv_def]
      >> conj_tac
      >- simp
           [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              compute_boundedCase16594ObjectDeltaProductSourceItemEvalTheory.bounded_case16594_object_q_dim_jet_f_eval)
          >> intLib.ARITH_TAC)
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_boundedCase16594ObjectDeltaProductSourceItemEvalTheory.bounded_case16594_object_q_dim_jet_gradient_eval)
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectStateRecompleteEvalTheory.bounded_case16594_object_state_recomplete_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
