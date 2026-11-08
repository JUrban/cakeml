(*****************************************************************************
 * Structural evaluator semantics for one 4*x_i*delta source-item state.
 *
 * The numerical center jet and packed Hessian remain premises.  This theory
 * proves the production wrapper, jet projections, and Taylor-state
 * recompletion once, exposing exactly the two component evaluator results
 * that the arbitrary-cell semantic bridge still has to supply.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductSourceItemEval
Ancestors
  compute_boundedCase16594ObjectStateRecompleteEval
  compute_boundedCase16594ObjectRecompleteRelation
  compute_boundedCase16594ObjectPolyTraceEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_product_source_item_state_body_def:
  bounded_case16594_object_delta_product_source_item_state_body =
    Let «center_jet»
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [Var «coordinate»;Var «center_boxes»])
      (Let «packed_hessian»
        (App «candle_cv_q_packed_object_delta_product_hessian»
          [Var «radii»;Var «center_boxes»;Var «outer_boxes»;
           Var «coordinate»])
        (App «candle_cv_q_packed_object_state_recomplete»
          [Var «radii»;Num 1;
           App «candle_cv_q_dim_jet_f» [Var «center_jet»];
           App «candle_cv_q_dim_jet_gradient» [Var «center_jet»];
           Var «packed_hessian»]))
End

Theorem bounded_case16594_object_delta_product_source_item_state_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_delta_product_source_item_state» =
    SOME
      ([«radii»;«center_boxes»;«outer_boxes»;«coordinate»],
       bounded_case16594_object_delta_product_source_item_state_body)
Proof
  rw [bounded_case16594_object_delta_product_source_item_state_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_product_source_item_state_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv radii;from_cv center_boxes;from_cv outer_boxes;
         from_cv coordinate]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«coordinate»,from_cv coordinate)]
        bounded_case16594_object_delta_product_source_item_state_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectInverseControlEvalTheory.bounded_case16594_object_compute_eval_literal_app4
  >> simp
       [bounded_case16594_object_delta_product_source_item_state_lookup]
QED

Theorem bounded_case16594_object_q_dim_jet_f_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_dim_jet_f» =
    SOME ([«jet»],Uop Fst (Var «jet»))
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_q_dim_jet_gradient_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_dim_jet_gradient» =
    SOME ([«jet»],Uop Fst (Uop Snd (Var «jet»)))
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_q_dim_jet_f_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_jet_f»
        [from_cv (Pair center_value (Pair gradient hessian))])
      (refs:hol_refs) =
    (M_success (from_cv center_value),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«jet»,from_cv (Pair center_value (Pair gradient hessian)))]
            (Uop Fst (Var «jet»))) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
      >> simp [bounded_case16594_object_q_dim_jet_f_lookup])
  >> simp
       [compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_q_dim_jet_gradient_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_jet_gradient»
        [from_cv (Pair center_value (Pair gradient hessian))])
      (refs:hol_refs) =
    (M_success (from_cv gradient),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«jet»,from_cv (Pair center_value (Pair gradient hessian)))]
            (Uop Fst (Uop Snd (Var «jet»)))) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
      >> simp [bounded_case16594_object_q_dim_jet_gradient_lookup])
  >> simp
       [compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_delta_product_source_item_state_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  4100 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [from_cv coordinate;from_cv center_boxes]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair center_value
          (Pair (bounded_object_q_cv_list center_gradient) center_hessian))),
     refs) /\
  compute_eval (clock - 2) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv (bounded_object_q_cv_list radii);from_cv center_boxes;
         from_cv outer_boxes;from_cv coordinate]) refs =
    (M_success
      (from_cv (bounded_object_q_cv_list packed_hessian)),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv (bounded_object_q_cv_list radii);from_cv center_boxes;
         from_cv outer_boxes;from_cv coordinate]) refs =
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
            [`refs`,`bounded_object_q_cv_list radii`,`outer_boxes`,
             `coordinate`,`clock`,`center_boxes`]
            (GEN_ALL
              bounded_case16594_object_delta_product_source_item_state_unfold))
          (ASSUME ``0:num < clock``)]
  >> simp
       [bounded_case16594_object_delta_product_source_item_state_body_def,
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
              bounded_case16594_object_q_dim_jet_f_eval)
          >> intLib.ARITH_TAC)
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_case16594_object_q_dim_jet_gradient_eval)
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectStateRecompleteEvalTheory.bounded_case16594_object_state_recomplete_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_delta_product_source_item_state_semantic:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_packed_q_interval_encoded runtime_center /\
  EVERY bounded_packed_q_interval_encoded runtime_center_gradient /\
  LENGTH runtime_center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded runtime_hessian /\
  LENGTH runtime_hessian = 21 /\
  4100 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [from_cv coordinate;from_cv center_boxes]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair runtime_center
          (Pair (bounded_object_q_cv_list runtime_center_gradient)
            center_hessian))),refs) /\
  compute_eval (clock - 2) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv center_boxes;from_cv outer_boxes;from_cv coordinate]) refs =
    (M_success (from_cv (bounded_object_q_cv_list runtime_hessian)),refs) /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_interval_cv_equiv runtime_center semantic_center /\
  bounded_packed_q_interval_valid_cv semantic_center /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_gradient semantic_center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_gradient /\
  LENGTH semantic_center_gradient = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_hessian semantic_hessian /\
  EVERY bounded_packed_q_interval_valid_cv semantic_hessian /\
  LENGTH semantic_hessian = 21 ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv center_boxes;from_cv outer_boxes;from_cv coordinate]) refs =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv
          (Num 1) runtime_center
          (bounded_object_q_cv_list runtime_center_gradient)
          (bounded_packed_q_source_value_bound6_cv
            runtime_radii runtime_center runtime_center_gradient
            runtime_hessian)
          (bounded_object_q_cv_list
            (bounded_packed_q_source_gradient_complete6_cv
              runtime_radii runtime_center_gradient runtime_hessian))
          (bounded_object_q_cv_list runtime_hessian))),refs) /\
  bounded_object_q_taylor_runtime_equiv
    (bounded_case16594_object_state_cv
      (Num 1) runtime_center
      (bounded_object_q_cv_list runtime_center_gradient)
      (bounded_packed_q_source_value_bound6_cv
        runtime_radii runtime_center runtime_center_gradient runtime_hessian)
      (bounded_object_q_cv_list
        (bounded_packed_q_source_gradient_complete6_cv
          runtime_radii runtime_center_gradient runtime_hessian))
      (bounded_object_q_cv_list runtime_hessian))
    (BoundedObjectQTaylor T semantic_center semantic_center_gradient
      (bounded_object_q_taylor_value_complete_cv semantic_center
        (bounded_object_q_taylor_error_cv semantic_radii
          semantic_center_gradient weights semantic_hessian))
      (bounded_object_q_taylor_gradient_complete_cv semantic_radii
        semantic_center_gradient semantic_hessian)
      semantic_hessian)
Proof
  strip_tac
  >> conj_tac
  >- (irule bounded_case16594_object_delta_product_source_item_state_eval
      >> simp []
      >> qexists_tac `center_hessian`
      >> simp [])
  >> irule
       (SIMP_RULE std_ss []
         (Q.SPEC `T`
         compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_case16594_object_recomplete_runtime_semantic_equiv)
       )
  >> simp []
QED

val _ = export_theory ();
