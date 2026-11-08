(*****************************************************************************
 * Complete evaluator and semantic bridge for a production variable state.
 *
 * This composes the authenticated coordinate lookup, recursive unit-vector
 * constructor, zero Hessian, and six-field Taylor-state constructor.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectVariableStateEval
Ancestors
  compute_boundedCase16594ObjectVariableEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_variable_state_body_def:
  bounded_case16594_object_variable_state_body =
    App «candle_cv_q_packed_object_state_make»
      [Num 1;
       App «candle_cv_q_interval_lookup»
         [Var «variable»;Var «center_boxes»];
       App «candle_cv_q_dim_interval_unit»
         [Var «variable»;
          App «candle_cv_q_packed_object_zero_gradient6» []];
       App «candle_cv_q_interval_lookup»
         [Var «variable»;Var «outer_boxes»];
       App «candle_cv_q_dim_interval_unit»
         [Var «variable»;
          App «candle_cv_q_packed_object_zero_gradient6» []];
       App «candle_cv_q_packed_object_zero_hessian21» []]
End

Definition bounded_case16594_object_variable_state_cv_def:
  bounded_case16594_object_variable_state_cv
      center_boxes outer_boxes variable =
    bounded_case16594_object_state_cv
      (Num 1)
      (EL variable center_boxes)
      (bounded_object_q_cv_list (bounded_object_q_unit_vector variable))
      (EL variable outer_boxes)
      (bounded_object_q_cv_list (bounded_object_q_unit_vector variable))
      bounded_case16594_object_zero_hessian21_cv
End

Theorem bounded_case16594_object_variable_state_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_variable_state» =
    SOME
      ([«center_boxes»;«outer_boxes»;«variable»],
       bounded_case16594_object_variable_state_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_variable_state_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_variable_state»
        [from_cv center_boxes;from_cv outer_boxes;from_cv variable])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);
         («variable»,from_cv variable)]
        bounded_case16594_object_variable_state_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> asm_rewrite_tac [bounded_case16594_object_variable_state_lookup]
QED

Theorem bounded_case16594_object_variable_gradient_eval:
  variable < 6 /\ 56 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_unit»
        [Num variable;
         App «candle_cv_q_packed_object_zero_gradient6» []])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_unit_vector variable))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_dim_interval_unit»
            [from_cv (Num variable);
             from_cv bounded_case16594_object_zero_gradient6_cv]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num,
            compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_zero_gradient6_eval]
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_zero_gradient6_cv_def,
        compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_cv_list_identity]
  >> mp_tac
       (Q.SPECL
         [`REPLICATE 6 bounded_case16594_object_zero_interval_cv`,
          `variable`,`clock`,`refs`]
         compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_interval_unit_eval)
  >> impl_tac
  >- (simp [] >> intLib.ARITH_TAC)
  >> simp
       [compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_interval_unit_six]
QED

Theorem bounded_case16594_object_variable_state_arguments_eval:
  LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
  variable < 6 /\ 57 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_make»
        [Num 1;
         App «candle_cv_q_interval_lookup»
           [Num variable;from_cv (bounded_object_q_cv_list center_boxes)];
         App «candle_cv_q_dim_interval_unit»
           [Num variable;
            App «candle_cv_q_packed_object_zero_gradient6» []];
         App «candle_cv_q_interval_lookup»
           [Num variable;from_cv (bounded_object_q_cv_list outer_boxes)];
         App «candle_cv_q_dim_interval_unit»
           [Num variable;
            App «candle_cv_q_packed_object_zero_gradient6» []];
         App «candle_cv_q_packed_object_zero_hessian21» []])
      (refs:hol_refs) =
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_make»
        [from_cv (Num 1);from_cv (EL variable center_boxes);
         from_cv
           (bounded_object_q_cv_list
             (bounded_object_q_unit_vector variable));
         from_cv (EL variable outer_boxes);
         from_cv
           (bounded_object_q_cv_list
             (bounded_object_q_unit_vector variable));
         from_cv bounded_case16594_object_zero_hessian21_cv]) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
  >> simp
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num,
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval,
        bounded_case16594_object_variable_gradient_eval,
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_zero_hessian21_eval]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_variable_state_subst:
  subst
      [(«center_boxes»,from_cv (bounded_object_q_cv_list center_boxes));
       («outer_boxes»,from_cv (bounded_object_q_cv_list outer_boxes));
       («variable»,from_cv (Num variable))]
      bounded_case16594_object_variable_state_body =
    App «candle_cv_q_packed_object_state_make»
      [Num 1;
       App «candle_cv_q_interval_lookup»
         [Num variable;from_cv (bounded_object_q_cv_list center_boxes)];
       App «candle_cv_q_dim_interval_unit»
         [Num variable;
          App «candle_cv_q_packed_object_zero_gradient6» []];
       App «candle_cv_q_interval_lookup»
         [Num variable;from_cv (bounded_object_q_cv_list outer_boxes)];
       App «candle_cv_q_dim_interval_unit»
         [Num variable;
          App «candle_cv_q_packed_object_zero_gradient6» []];
       App «candle_cv_q_packed_object_zero_hessian21» []]
Proof
  simp
    [bounded_case16594_object_variable_state_body_def,
     compute_evalTheory.subst_def]
QED

Theorem bounded_case16594_object_variable_state_eval:
  LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
  variable < 6 /\ 58 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_variable_state»
        [from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (bounded_object_q_cv_list outer_boxes);
         from_cv (Num variable)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_variable_state_cv
          center_boxes outer_boxes variable)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«center_boxes»,from_cv (bounded_object_q_cv_list center_boxes));
             («outer_boxes»,from_cv (bounded_object_q_cv_list outer_boxes));
             («variable»,from_cv (Num variable))]
            bounded_case16594_object_variable_state_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_variable_state_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [bounded_case16594_object_variable_state_subst]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_make»
            [from_cv (Num 1);from_cv (EL variable center_boxes);
             from_cv
               (bounded_object_q_cv_list
                 (bounded_object_q_unit_vector variable));
             from_cv (EL variable outer_boxes);
             from_cv
               (bounded_object_q_cv_list
                 (bounded_object_q_unit_vector variable));
             from_cv bounded_case16594_object_zero_hessian21_cv]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_variable_state_arguments_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [bounded_case16594_object_variable_state_cv_def]
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_make_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_nth_el:
  !items variable.
    variable < LENGTH items ==>
    bounded_object_q_nth items variable = SOME (EL variable items)
Proof
  Induct_on `items`
  >> Cases_on `variable`
  >> simp
       [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_nth_def]
QED

Theorem bounded_case16594_object_variable_state_runtime_semantic_equiv:
  LENGTH runtime_center_boxes = 6 /\
  LENGTH runtime_outer_boxes = 6 /\
  variable < 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_boxes semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_outer_boxes semantic_outer_boxes ==>
  bounded_object_q_taylor_runtime_equiv
    (bounded_case16594_object_variable_state_cv
      runtime_center_boxes runtime_outer_boxes variable)
    (THE
      (bounded_object_q_taylor_variable
        semantic_center_boxes semantic_outer_boxes variable))
Proof
  strip_tac
  >> `LENGTH semantic_center_boxes = 6 /\
      LENGTH semantic_outer_boxes = 6` by
       metis_tac [LIST_REL_LENGTH]
  >> `bounded_object_q_nth semantic_center_boxes variable =
        SOME (EL variable semantic_center_boxes) /\
      bounded_object_q_nth semantic_outer_boxes variable =
        SOME (EL variable semantic_outer_boxes)` by
       (conj_tac
        >> irule bounded_case16594_object_nth_el
        >> intLib.ARITH_TAC)
  >> `bounded_object_q_interval_cv_equiv
        (EL variable runtime_center_boxes)
        (EL variable semantic_center_boxes) /\
      bounded_object_q_interval_cv_equiv
        (EL variable runtime_outer_boxes)
        (EL variable semantic_outer_boxes)` by
       fs [LIST_REL_EL_EQN]
  >> rewrite_tac
       [bounded_case16594_object_variable_state_cv_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_variable_def]
  >> asm_rewrite_tac []
  >> simp_tac (srw_ss()) []
  >> rewrite_tac
       [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_selectors]
  >> simp
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_domain_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_gradient_bounds_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_cv_equiv_encoded,
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_zero_hessian21_cv_def,
        compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_cv_list_identity,
        compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_zero_interval_identity]
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_list_rel_refl
      >> simp
           [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_unit_vector_def]
      >> rpt COND_CASES_TAC
      >> simp
           [compute_boundedObjectTaylorZeroAlgebraTheory.bounded_analytic_source_q_interval_cv_encoded])
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_list_rel_refl
      >> simp
           [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_unit_vector_def]
      >> rpt COND_CASES_TAC
      >> simp
           [compute_boundedObjectTaylorZeroAlgebraTheory.bounded_analytic_source_q_interval_cv_encoded])
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_list_rel_refl
  >> simp
       [compute_boundedObjectTaylorZeroAlgebraTheory.bounded_analytic_source_q_interval_cv_encoded]
QED

val _ = export_theory ();
