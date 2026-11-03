(*****************************************************************************
 * Complete production evaluator semantics for object-state recompletion.
 *
 * This composes the already-proved packed value bound with the production
 * six-row gradient traversal.  The result is the exact six-field state used
 * by every subsequent object instruction; no genuine certificate data are
 * expanded in this theory.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectStateRecompleteEval
Ancestors
  compute_boundedCase16594ObjectRecompleteControlEval
  compute_boundedCase16594ObjectGradientCompleteEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_value_bound6_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  113 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_value_bound6»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv center_value;
         from_cv (bounded_object_q_cv_list center_gradient);
         from_cv (bounded_object_q_cv_list packed_hessian)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_value_bound6_cv
          radii center_value center_gradient packed_hessian)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_packed_object_value_bound6»
            [from_cv (bounded_object_q_cv_list radii);
             from_cv center_value;
             from_cv (bounded_object_q_cv_list center_gradient);
             from_cv (bounded_object_q_cv_list packed_hessian)]) refs`
  >> conj_tac
  >- (sym_tac
      >> irule
           compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_eval_cong
      >> simp
           [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
            compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_def,
            compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_uses_only_from_cv]
      >> EVAL_TAC)
  >> irule
       compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_value_bound6_eval
  >> simp []
QED

Theorem bounded_case16594_object_state_recomplete_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  4097 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_recomplete»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv domain_cv;
         from_cv center_value;
         from_cv (bounded_object_q_cv_list center_gradient);
         from_cv (bounded_object_q_cv_list packed_hessian)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv
          domain_cv
          center_value
          (bounded_object_q_cv_list center_gradient)
          (bounded_packed_q_source_value_bound6_cv
            radii center_value center_gradient packed_hessian)
          (bounded_object_q_cv_list
            (bounded_packed_q_source_gradient_complete6_cv
              radii center_gradient packed_hessian))
          (bounded_object_q_cv_list packed_hessian))),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_state_recomplete_eval_from_bounds
  >> conj_tac
  >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_gradient_complete6_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_value_bound6_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
