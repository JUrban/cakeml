(*****************************************************************************
 * Exact arbitrary-input evaluator for the production outer Hessian of
 * 4*x_i*delta.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductOuterHessianEval
Ancestors
  compute_boundedCase16594ObjectDeltaProductJetEnvironmentEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_product_outer_hessian_cv_def:
  bounded_case16594_object_delta_product_outer_hessian_cv
      radii center_boxes outer_boxes coordinate =
    let delta_hessian =
      bounded_object_q_delta_hessian_six_cv
        (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
        (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes);
        center_delta_gradient =
      bounded_case16594_object_delta_gradient_six_cv
        (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
        (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes);
        delta_gradient =
      bounded_packed_q_source_gradient_complete6_cv
        radii center_delta_gradient delta_hessian
    in
      bounded_case16594_object_delta_product_hessian_cv coordinate
        (EL coordinate outer_boxes) delta_gradient
        bounded_case16594_object_delta_product_indices6 delta_hessian
End

Definition bounded_case16594_object_delta_product_outer_hessian_body_def:
  bounded_case16594_object_delta_product_outer_hessian_body =
    Let «delta_hessian»
      (App «candle_cv_q_packed_delta_hessian_six»
        [App «candle_cv_q_interval_lookup» [Num 0;Var «outer_boxes»];
         App «candle_cv_q_interval_lookup» [Num 1;Var «outer_boxes»];
         App «candle_cv_q_interval_lookup» [Num 2;Var «outer_boxes»];
         App «candle_cv_q_interval_lookup» [Num 3;Var «outer_boxes»];
         App «candle_cv_q_interval_lookup» [Num 4;Var «outer_boxes»];
         App «candle_cv_q_interval_lookup» [Num 5;Var «outer_boxes»]])
      (Let «delta_gradient»
        (App «candle_cv_q_packed_object_gradient_complete6»
          [Var «radii»;
           App «candle_cv_q_packed_delta_gradient_six»
             [App «candle_cv_q_interval_lookup» [Num 0;Var «center_boxes»];
              App «candle_cv_q_interval_lookup» [Num 1;Var «center_boxes»];
              App «candle_cv_q_interval_lookup» [Num 2;Var «center_boxes»];
              App «candle_cv_q_interval_lookup» [Num 3;Var «center_boxes»];
              App «candle_cv_q_interval_lookup» [Num 4;Var «center_boxes»];
              App «candle_cv_q_interval_lookup» [Num 5;Var «center_boxes»]];
           Var «delta_hessian»])
        (App «candle_cv_q_packed_delta_product_hessian_six»
          [Var «coordinate»;
           App «candle_cv_q_interval_lookup»
             [Var «coordinate»;Var «outer_boxes»];
           Var «delta_gradient»;Var «delta_hessian»]))
End

Theorem bounded_case16594_object_delta_product_outer_hessian_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_delta_product_hessian» =
    SOME
      ([«radii»;«center_boxes»;«outer_boxes»;«coordinate»],
       bounded_case16594_object_delta_product_outer_hessian_body)
Proof
  rw [bounded_case16594_object_delta_product_outer_hessian_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_product_outer_hessian_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv radii;from_cv center_boxes;from_cv outer_boxes;
         from_cv coordinate]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«coordinate»,from_cv coordinate)]
        bounded_case16594_object_delta_product_outer_hessian_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectInverseControlEvalTheory.bounded_case16594_object_compute_eval_literal_app4
  >> simp [bounded_case16594_object_delta_product_outer_hessian_lookup]
QED

Theorem bounded_case16594_object_gradient_rows_complete_encoded_length:
  !center_gradient interval_rows.
    EVERY bounded_object_q_encoded radii /\
    EVERY bounded_packed_q_interval_encoded center_gradient /\
    EVERY (EVERY bounded_packed_q_interval_encoded) interval_rows /\
    LENGTH center_gradient = LENGTH interval_rows ==>
    EVERY bounded_packed_q_interval_encoded
      (bounded_packed_q_source_gradient_rows_complete_cv
        radii center_gradient interval_rows) /\
    LENGTH
      (bounded_packed_q_source_gradient_rows_complete_cv
        radii center_gradient interval_rows) = LENGTH center_gradient
Proof
  Induct
  >> Cases_on `interval_rows`
  >> simp
       [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_packed_q_source_gradient_rows_complete_cv_def]
  >> metis_tac
       [compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_gradient_row_complete_cv_encoded]
QED

Theorem bounded_case16594_object_gradient_complete6_encoded_length:
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 ==>
  EVERY bounded_packed_q_interval_encoded
    (bounded_packed_q_source_gradient_complete6_cv
      radii center_gradient packed_hessian) /\
  LENGTH
    (bounded_packed_q_source_gradient_complete6_cv
      radii center_gradient packed_hessian) = 6
Proof
  strip_tac
  >> `bounded_hessian64_rows packed_hessian =
      SOME (bounded_packed_q_source_hessian6_rows packed_hessian)` by
       metis_tac
         [compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_hessian6_rows_exact]
  >> simp
       [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_packed_q_source_gradient_complete6_cv_def]
  >> mp_tac
       (Q.SPECL
         [`center_gradient`,
          `bounded_packed_q_source_hessian6_rows packed_hessian`]
         bounded_case16594_object_gradient_rows_complete_encoded_length)
  >> simp
       [compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_hessian6_rows_def,
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_hessian6_rows_encoded]
QED

Theorem bounded_case16594_object_delta_hessian_environment_eval:
  LENGTH environment = 6 /\
  EVERY bounded_packed_q_interval_encoded environment /\
  262160 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_hessian_six»
        [App «candle_cv_q_interval_lookup»
           [Num 0;from_cv (bounded_object_q_cv_list environment)];
         App «candle_cv_q_interval_lookup»
           [Num 1;from_cv (bounded_object_q_cv_list environment)];
         App «candle_cv_q_interval_lookup»
           [Num 2;from_cv (bounded_object_q_cv_list environment)];
         App «candle_cv_q_interval_lookup»
           [Num 3;from_cv (bounded_object_q_cv_list environment)];
         App «candle_cv_q_interval_lookup»
           [Num 4;from_cv (bounded_object_q_cv_list environment)];
         App «candle_cv_q_interval_lookup»
           [Num 5;from_cv (bounded_object_q_cv_list environment)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_delta_hessian_six_cv
            (EL 0 environment) (EL 1 environment) (EL 2 environment)
            (EL 3 environment) (EL 4 environment) (EL 5 environment)))),refs)
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 environment;EL 1 environment;EL 2 environment;
         EL 3 environment;EL 4 environment;EL 5 environment]` by
       fs [listTheory.EVERY_EL]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_hessian_six»
            [from_cv (EL 0 environment);from_cv (EL 1 environment);
             from_cv (EL 2 environment);from_cv (EL 3 environment);
             from_cv (EL 4 environment);from_cv (EL 5 environment)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
      >> conj_tac >- intLib.ARITH_TAC
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
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> irule
           compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectDeltaHessianSixEvalTheory.bounded_case16594_object_delta_hessian_six_eval
  >> fs [listTheory.EL]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_delta_gradient_environment_eval:
  LENGTH environment = 6 /\
  EVERY bounded_packed_q_interval_encoded environment /\
  262160 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_gradient_six»
        [App «candle_cv_q_interval_lookup»
           [Num 0;from_cv (bounded_object_q_cv_list environment)];
         App «candle_cv_q_interval_lookup»
           [Num 1;from_cv (bounded_object_q_cv_list environment)];
         App «candle_cv_q_interval_lookup»
           [Num 2;from_cv (bounded_object_q_cv_list environment)];
         App «candle_cv_q_interval_lookup»
           [Num 3;from_cv (bounded_object_q_cv_list environment)];
         App «candle_cv_q_interval_lookup»
           [Num 4;from_cv (bounded_object_q_cv_list environment)];
         App «candle_cv_q_interval_lookup»
           [Num 5;from_cv (bounded_object_q_cv_list environment)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_case16594_object_delta_gradient_six_cv
            (EL 0 environment) (EL 1 environment) (EL 2 environment)
            (EL 3 environment) (EL 4 environment) (EL 5 environment)))),refs)
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 environment;EL 1 environment;EL 2 environment;
         EL 3 environment;EL 4 environment;EL 5 environment]` by
       fs [listTheory.EVERY_EL]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_gradient_six»
            [from_cv (EL 0 environment);from_cv (EL 1 environment);
             from_cv (EL 2 environment);from_cv (EL 3 environment);
             from_cv (EL 4 environment);from_cv (EL 5 environment)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
      >> conj_tac >- intLib.ARITH_TAC
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
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> irule
           compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectDeltaGradientCompleteEvalTheory.bounded_case16594_object_delta_gradient_six_eval
  >> fs [listTheory.EL]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_delta_product_outer_hessian_eval:
  coordinate < 6 /\
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_boxes /\
  LENGTH center_boxes = 6 /\
  EVERY bounded_packed_q_interval_encoded outer_boxes /\
  LENGTH outer_boxes = 6 /\
  524400 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (bounded_object_q_cv_list outer_boxes);
         from_cv (Num coordinate)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_case16594_object_delta_product_outer_hessian_cv
            radii center_boxes outer_boxes coordinate))),refs)
Proof
  strip_tac
  >> qabbrev_tac
       `delta_hessian = bounded_object_q_delta_hessian_six_cv
          (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
          (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)`
  >> qabbrev_tac
       `center_delta_gradient = bounded_case16594_object_delta_gradient_six_cv
          (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
          (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes)`
  >> qabbrev_tac
       `delta_gradient = bounded_packed_q_source_gradient_complete6_cv
          radii center_delta_gradient delta_hessian`
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 outer_boxes;EL 1 outer_boxes;EL 2 outer_boxes;
         EL 3 outer_boxes;EL 4 outer_boxes;EL 5 outer_boxes]` by
       fs [listTheory.EVERY_EL]
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 center_boxes;EL 1 center_boxes;EL 2 center_boxes;
         EL 3 center_boxes;EL 4 center_boxes;EL 5 center_boxes]` by
       fs [listTheory.EVERY_EL]
  >> `EVERY bounded_packed_q_interval_encoded delta_hessian /\
      LENGTH delta_hessian = 21` by
       (qunabbrev_tac `delta_hessian`
        >> simp
             [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_packed_encoded,
              compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length])
  >> `EVERY bounded_packed_q_interval_encoded center_delta_gradient /\
      LENGTH center_delta_gradient = 6` by
       (qunabbrev_tac `center_delta_gradient`
        >> simp
             [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_packed_encoded,
              compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_length])
  >> `EVERY bounded_packed_q_interval_encoded delta_gradient /\
      LENGTH delta_gradient = 6` by
       (qunabbrev_tac `delta_gradient`
        >> irule bounded_case16594_object_gradient_complete6_encoded_length
        >> simp [])
  >> rw [bounded_case16594_object_delta_product_outer_hessian_unfold]
  >> simp
       [bounded_case16594_object_delta_product_outer_hessian_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_object_q_cv_list delta_hessian`
  >> conj_tac
  >- (qunabbrev_tac `delta_hessian`
      >> irule bounded_case16594_object_delta_hessian_environment_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_object_q_cv_list delta_gradient`
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 2)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_object_gradient_complete6»
                [from_cv (bounded_object_q_cv_list radii);
                 from_cv (bounded_object_q_cv_list center_delta_gradient);
                 from_cv (bounded_object_q_cv_list delta_hessian)]) refs`
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_app3_argument_results
          >> simp [compute_execProofTheory.compute_eval_from_cv]
          >> qunabbrev_tac `center_delta_gradient`
          >> irule bounded_case16594_object_delta_gradient_environment_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> qunabbrev_tac `delta_gradient`
      >> irule
           compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_gradient_complete6_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> rw [bounded_case16594_object_delta_product_outer_hessian_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 3)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_product_hessian_six»
            [from_cv (Num coordinate);from_cv (EL coordinate outer_boxes);
             from_cv (bounded_object_q_cv_list delta_gradient);
             from_cv (bounded_object_q_cv_list delta_hessian)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectQuadraticTermAtEvalTheory.bounded_packed_compute_eval_app4_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> conj_tac
      >- simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> irule
           compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_hessian_six_eval
  >> fs [listTheory.EVERY_EL]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
