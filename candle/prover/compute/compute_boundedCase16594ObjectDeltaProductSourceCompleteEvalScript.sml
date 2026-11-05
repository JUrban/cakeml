(*****************************************************************************
 * Complete arbitrary-input evaluator for one production 4*x_i*delta source
 * item.  This joins the generic center jet and outer Hessian to the existing
 * structural recompletion theorem.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductSourceCompleteEval
Ancestors
  compute_boundedCase16594ObjectDeltaProductOuterHessianEval
  compute_boundedCase16594ObjectDeltaProductSourceItemEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_interval_add_packed_encoded:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_add_cv left right)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded]
QED

Theorem bounded_case16594_object_interval_scale4_packed_encoded:
  bounded_packed_q_interval_encoded value ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_scale4_cv value)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_object_q_interval_scale4_cv_def]
  >> simp [bounded_case16594_object_interval_add_packed_encoded]
QED

Theorem bounded_case16594_object_delta_product_center_gradient_entry_packed_encoded:
  bounded_packed_q_interval_encoded coordinate_value /\
  bounded_packed_q_interval_encoded delta_value /\
  EVERY bounded_packed_q_interval_encoded delta_gradient /\
  derivative_coordinate < LENGTH delta_gradient ==>
  bounded_packed_q_interval_encoded
    (bounded_case16594_object_delta_product_center_gradient_entry_cv
      coordinate coordinate_value delta_value delta_gradient
      derivative_coordinate)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded
        (EL derivative_coordinate delta_gradient)` by
       fs [listTheory.EVERY_EL]
  >> rw
       [compute_boundedCase16594ObjectDeltaProductGradientEntryEvalTheory.bounded_case16594_object_delta_product_center_gradient_entry_cv_def]
  >> Cases_on `derivative_coordinate = coordinate`
  >> simp
       [bounded_case16594_object_interval_scale4_packed_encoded,
        bounded_case16594_object_interval_add_packed_encoded,
        compute_boundedCase16594ObjectDeltaGradientCompleteEvalTheory.bounded_case16594_object_delta_pair_product_packed_encoded]
QED

Theorem bounded_case16594_object_delta_product_hessian_entry_packed_encoded:
  bounded_packed_q_interval_encoded box_coordinate /\
  EVERY bounded_packed_q_interval_encoded delta_gradient /\
  row < LENGTH delta_gradient /\ column < LENGTH delta_gradient /\
  bounded_packed_q_interval_encoded delta_hessian ==>
  bounded_packed_q_interval_encoded
    (bounded_case16594_object_delta_product_hessian_entry_cv coordinate
      box_coordinate delta_gradient row column delta_hessian)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded (EL row delta_gradient) /\
      bounded_packed_q_interval_encoded (EL column delta_gradient)` by
       fs [listTheory.EVERY_EL]
  >> rw
       [compute_boundedCase16594ObjectDeltaProductHessianEntryEvalTheory.bounded_case16594_object_delta_product_hessian_entry_cv_def]
  >> Cases_on `row = (coordinate:num)`
  >> Cases_on `column = (coordinate:num)`
  >> simp
       [bounded_case16594_object_interval_scale4_packed_encoded,
        bounded_case16594_object_interval_add_packed_encoded,
        compute_boundedCase16594ObjectDeltaGradientCompleteEvalTheory.bounded_case16594_object_delta_pair_product_packed_encoded]
QED

Theorem bounded_case16594_object_delta_product_hessian_packed_encoded_length:
  !(indices:(num # num) list) entries.
    bounded_packed_q_interval_encoded box_coordinate /\
    EVERY bounded_packed_q_interval_encoded delta_gradient /\
    EVERY
      (\index.
        FST index < LENGTH delta_gradient /\
        SND index < LENGTH delta_gradient) indices /\
    EVERY bounded_packed_q_interval_encoded entries /\
    LENGTH indices = LENGTH entries ==>
    EVERY bounded_packed_q_interval_encoded
      (bounded_case16594_object_delta_product_hessian_cv coordinate
        box_coordinate delta_gradient indices entries) /\
    LENGTH
      (bounded_case16594_object_delta_product_hessian_cv coordinate
        box_coordinate delta_gradient indices entries) = LENGTH indices
Proof
  Induct_on `indices`
  >- (gen_tac
      >> Cases_on `entries`
      >> simp
           [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_hessian_cv_def])
  >> gen_tac
  >> PairCases_on `h`
  >> gen_tac
  >> Cases_on `entries`
  >> simp
       [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_hessian_cv_def]
  >> strip_tac
  >> irule
       bounded_case16594_object_delta_product_hessian_entry_packed_encoded
  >> simp []
QED

Definition bounded_case16594_object_delta_product_center_delta_value_cv_def:
  bounded_case16594_object_delta_product_center_delta_value_cv center_boxes =
    bounded_object_q_delta_value_six_cv
      (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
      (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes)
End

Definition bounded_case16594_object_delta_product_center_delta_gradient_cv_def:
  bounded_case16594_object_delta_product_center_delta_gradient_cv center_boxes =
    bounded_case16594_object_delta_gradient_six_cv
      (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
      (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes)
End

Definition bounded_case16594_object_delta_product_center_delta_hessian_cv_def:
  bounded_case16594_object_delta_product_center_delta_hessian_cv center_boxes =
    bounded_object_q_delta_hessian_six_cv
      (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
      (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes)
End

Definition bounded_case16594_object_delta_product_center_coordinate_cv_def:
  bounded_case16594_object_delta_product_center_coordinate_cv
      center_boxes coordinate =
    EL coordinate center_boxes
End

Definition bounded_case16594_object_delta_product_center_value_cv_def:
  bounded_case16594_object_delta_product_center_value_cv
      center_boxes coordinate =
    bounded_object_q_interval_scale4_cv
      (bounded_object_q_interval_mul_cv
        (bounded_case16594_object_delta_product_center_coordinate_cv
          center_boxes coordinate)
        (bounded_case16594_object_delta_product_center_delta_value_cv
          center_boxes))
End

Definition bounded_case16594_object_delta_product_center_gradient_cv_def:
  bounded_case16594_object_delta_product_center_gradient_cv
      center_boxes coordinate =
    [bounded_case16594_object_delta_product_center_gradient_entry_cv
       coordinate
       (bounded_case16594_object_delta_product_center_coordinate_cv
         center_boxes coordinate)
       (bounded_case16594_object_delta_product_center_delta_value_cv
         center_boxes)
       (bounded_case16594_object_delta_product_center_delta_gradient_cv
         center_boxes) 0;
     bounded_case16594_object_delta_product_center_gradient_entry_cv
       coordinate
       (bounded_case16594_object_delta_product_center_coordinate_cv
         center_boxes coordinate)
       (bounded_case16594_object_delta_product_center_delta_value_cv
         center_boxes)
       (bounded_case16594_object_delta_product_center_delta_gradient_cv
         center_boxes) 1;
     bounded_case16594_object_delta_product_center_gradient_entry_cv
       coordinate
       (bounded_case16594_object_delta_product_center_coordinate_cv
         center_boxes coordinate)
       (bounded_case16594_object_delta_product_center_delta_value_cv
         center_boxes)
       (bounded_case16594_object_delta_product_center_delta_gradient_cv
         center_boxes) 2;
     bounded_case16594_object_delta_product_center_gradient_entry_cv
       coordinate
       (bounded_case16594_object_delta_product_center_coordinate_cv
         center_boxes coordinate)
       (bounded_case16594_object_delta_product_center_delta_value_cv
         center_boxes)
       (bounded_case16594_object_delta_product_center_delta_gradient_cv
         center_boxes) 3;
     bounded_case16594_object_delta_product_center_gradient_entry_cv
       coordinate
       (bounded_case16594_object_delta_product_center_coordinate_cv
         center_boxes coordinate)
       (bounded_case16594_object_delta_product_center_delta_value_cv
         center_boxes)
       (bounded_case16594_object_delta_product_center_delta_gradient_cv
         center_boxes) 4;
     bounded_case16594_object_delta_product_center_gradient_entry_cv
       coordinate
       (bounded_case16594_object_delta_product_center_coordinate_cv
         center_boxes coordinate)
       (bounded_case16594_object_delta_product_center_delta_value_cv
         center_boxes)
       (bounded_case16594_object_delta_product_center_delta_gradient_cv
         center_boxes) 5]
End

Definition bounded_case16594_object_delta_product_center_packed_hessian_cv_def:
  bounded_case16594_object_delta_product_center_packed_hessian_cv
      center_boxes coordinate =
    bounded_case16594_object_delta_product_hessian_cv coordinate
      (bounded_case16594_object_delta_product_center_coordinate_cv
        center_boxes coordinate)
      (bounded_case16594_object_delta_product_center_delta_gradient_cv
        center_boxes)
      bounded_case16594_object_delta_product_indices6
      (bounded_case16594_object_delta_product_center_delta_hessian_cv
        center_boxes)
End

Definition bounded_case16594_object_delta_product_center_hessian_cv_def:
  bounded_case16594_object_delta_product_center_hessian_cv
      center_boxes coordinate =
    bounded_object_q_cv_list
      (MAP bounded_object_q_cv_list
        (bounded_packed_q_source_hessian6_rows
          (bounded_case16594_object_delta_product_center_packed_hessian_cv
            center_boxes coordinate)))
End

Theorem bounded_case16594_object_six_el_identity:
  LENGTH values = 6 ==>
  [EL 0 values;EL 1 values;EL 2 values;
   EL 3 values;EL 4 values;EL 5 values] = values
Proof
  Cases_on `values` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
QED

Theorem bounded_case16594_object_delta_product_center_jet_decomposition:
  LENGTH center_boxes = 6 ==>
  bounded_case16594_object_delta_product_jet_six_cv coordinate
      (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
      (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes) =
    Pair
      (bounded_case16594_object_delta_product_center_value_cv
        center_boxes coordinate)
      (Pair
        (bounded_object_q_cv_list
          (bounded_case16594_object_delta_product_center_gradient_cv
            center_boxes coordinate))
        (bounded_case16594_object_delta_product_center_hessian_cv
          center_boxes coordinate))
Proof
  strip_tac
  >> ` [EL 0 center_boxes;EL 1 center_boxes;EL 2 center_boxes;
         EL 3 center_boxes;EL 4 center_boxes;EL 5 center_boxes] =
       center_boxes` by
       simp [bounded_case16594_object_six_el_identity]
  >> rw
    [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_product_jet_six_cv_def,
     compute_boundedCase16594ObjectDeltaProductGradientSixEvalTheory.bounded_case16594_object_delta_product_center_gradient_six_cv_def,
     bounded_case16594_object_delta_product_center_delta_value_cv_def,
     bounded_case16594_object_delta_product_center_delta_gradient_cv_def,
     bounded_case16594_object_delta_product_center_delta_hessian_cv_def,
     bounded_case16594_object_delta_product_center_coordinate_cv_def,
     bounded_case16594_object_delta_product_center_value_cv_def,
     bounded_case16594_object_delta_product_center_gradient_cv_def,
     bounded_case16594_object_delta_product_center_packed_hessian_cv_def,
     bounded_case16594_object_delta_product_center_hessian_cv_def]
QED

Theorem bounded_case16594_object_delta_product_center_components_encoded:
  coordinate < 6 /\ LENGTH center_boxes = 6 /\
  EVERY bounded_packed_q_interval_encoded center_boxes ==>
  bounded_packed_q_interval_encoded
    (bounded_case16594_object_delta_product_center_value_cv
      center_boxes coordinate) /\
  EVERY bounded_packed_q_interval_encoded
    (bounded_case16594_object_delta_product_center_gradient_cv
      center_boxes coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_product_center_gradient_cv
      center_boxes coordinate) = 6
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 center_boxes;EL 1 center_boxes;EL 2 center_boxes;
         EL 3 center_boxes;EL 4 center_boxes;EL 5 center_boxes]` by
       fs [listTheory.EVERY_EL]
  >> `bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_product_center_coordinate_cv
          center_boxes coordinate)` by
       fs
         [bounded_case16594_object_delta_product_center_coordinate_cv_def,
          listTheory.EVERY_EL]
  >> `bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_product_center_delta_value_cv
          center_boxes)` by
       (PURE_REWRITE_TAC
          [bounded_case16594_object_delta_product_center_delta_value_cv_def]
        >> irule
             compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_value_six_packed_encoded
        >> asm_rewrite_tac [])
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_product_center_delta_gradient_cv
          center_boxes) /\
      LENGTH
        (bounded_case16594_object_delta_product_center_delta_gradient_cv
          center_boxes) = 6` by
       (PURE_REWRITE_TAC
          [bounded_case16594_object_delta_product_center_delta_gradient_cv_def]
        >> conj_tac
        >- (irule
              compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_packed_encoded
            >> asm_rewrite_tac [])
        >> simp
             [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_length])
  >> simp
       [bounded_case16594_object_delta_product_center_value_cv_def,
        bounded_case16594_object_delta_product_center_gradient_cv_def,
        bounded_case16594_object_interval_scale4_packed_encoded,
        compute_boundedCase16594ObjectDeltaGradientCompleteEvalTheory.bounded_case16594_object_delta_pair_product_packed_encoded,
        bounded_case16594_object_delta_product_center_gradient_entry_packed_encoded]
QED

Theorem bounded_case16594_object_delta_product_outer_hessian_encoded:
  coordinate < 6 /\
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_boxes /\
  LENGTH center_boxes = 6 /\
  EVERY bounded_packed_q_interval_encoded outer_boxes /\
  LENGTH outer_boxes = 6 ==>
  EVERY bounded_packed_q_interval_encoded
    (bounded_case16594_object_delta_product_outer_hessian_cv
      radii center_boxes outer_boxes coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_product_outer_hessian_cv
      radii center_boxes outer_boxes coordinate) = 21
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 outer_boxes;EL 1 outer_boxes;EL 2 outer_boxes;
         EL 3 outer_boxes;EL 4 outer_boxes;EL 5 outer_boxes]` by
       fs [listTheory.EVERY_EL]
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 center_boxes;EL 1 center_boxes;EL 2 center_boxes;
         EL 3 center_boxes;EL 4 center_boxes;EL 5 center_boxes]` by
       fs [listTheory.EVERY_EL]
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
        >> irule
             compute_boundedCase16594ObjectDeltaProductOuterHessianEvalTheory.bounded_case16594_object_gradient_complete6_encoded_length
        >> simp [])
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_product_hessian_cv coordinate
          (EL coordinate outer_boxes) delta_gradient
          bounded_case16594_object_delta_product_indices6 delta_hessian) /\
      LENGTH
        (bounded_case16594_object_delta_product_hessian_cv coordinate
          (EL coordinate outer_boxes) delta_gradient
          bounded_case16594_object_delta_product_indices6 delta_hessian) =
        LENGTH bounded_case16594_object_delta_product_indices6` by
       (irule
          bounded_case16594_object_delta_product_hessian_packed_encoded_length
        >> conj_tac
        >- fs [listTheory.EVERY_EL]
        >> simp
             [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_indices6_def])
  >> rw
       [compute_boundedCase16594ObjectDeltaProductOuterHessianEvalTheory.bounded_case16594_object_delta_product_outer_hessian_cv_def]
  >> fs
       [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_indices6_def]
QED

Definition bounded_case16594_object_delta_product_source_state_cv_def:
  bounded_case16594_object_delta_product_source_state_cv
      radii center_boxes outer_boxes coordinate =
    let center_value =
      bounded_case16594_object_delta_product_center_value_cv
        center_boxes coordinate;
        center_gradient =
      bounded_case16594_object_delta_product_center_gradient_cv
        center_boxes coordinate;
        packed_hessian =
      bounded_case16594_object_delta_product_outer_hessian_cv
        radii center_boxes outer_boxes coordinate
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

Theorem bounded_case16594_object_delta_product_source_state_eval:
  coordinate < 6 /\
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_boxes /\
  LENGTH center_boxes = 6 /\
  EVERY bounded_packed_q_interval_encoded outer_boxes /\
  LENGTH outer_boxes = 6 /\ 524403 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (bounded_object_q_cv_list outer_boxes);
         from_cv (Num coordinate)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_product_source_state_cv
          radii center_boxes outer_boxes coordinate)),refs)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_product_center_value_cv
          center_boxes coordinate) /\
      EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_product_center_gradient_cv
          center_boxes coordinate) /\
      LENGTH
        (bounded_case16594_object_delta_product_center_gradient_cv
          center_boxes coordinate) = 6` by
       (irule
          bounded_case16594_object_delta_product_center_components_encoded
        >> simp [])
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_product_outer_hessian_cv
          radii center_boxes outer_boxes coordinate) /\
      LENGTH
        (bounded_case16594_object_delta_product_outer_hessian_cv
          radii center_boxes outer_boxes coordinate) = 21` by
       (irule
          bounded_case16594_object_delta_product_outer_hessian_encoded
        >> simp [])
  >> PURE_REWRITE_TAC
       [bounded_case16594_object_delta_product_source_state_cv_def,LET_THM]
  >> BETA_TAC
  >> irule
       compute_boundedCase16594ObjectDeltaProductSourceItemEvalTheory.bounded_case16594_object_delta_product_source_item_state_eval
  >> simp []
  >> conj_tac
  >- (qexists_tac
        `bounded_case16594_object_delta_product_center_hessian_cv
           center_boxes coordinate`
      >> irule EQ_TRANS
      >> qexists_tac
           `(M_success
              (from_cv
                (bounded_case16594_object_delta_product_jet_six_cv coordinate
                  (EL 0 center_boxes) (EL 1 center_boxes)
                  (EL 2 center_boxes) (EL 3 center_boxes)
                  (EL 4 center_boxes) (EL 5 center_boxes))),refs)`
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              compute_boundedCase16594ObjectDeltaProductJetEnvironmentEvalTheory.bounded_case16594_object_delta_product_jet_environment_eval)
          >> simp []
          >> intLib.ARITH_TAC)
      >> simp [bounded_case16594_object_delta_product_center_jet_decomposition])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_boundedCase16594ObjectDeltaProductOuterHessianEvalTheory.bounded_case16594_object_delta_product_outer_hessian_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_delta_product_source0_state_eval:
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_boxes /\
  LENGTH center_boxes = 6 /\
  EVERY bounded_packed_q_interval_encoded outer_boxes /\
  LENGTH outer_boxes = 6 /\ 524403 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (bounded_object_q_cv_list outer_boxes);
         from_cv (Num 0)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_product_source_state_cv
          radii center_boxes outer_boxes 0)),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_delta_product_source_state_eval
  >> simp []
QED

Theorem bounded_case16594_object_delta_product_source1_state_eval:
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_boxes /\
  LENGTH center_boxes = 6 /\
  EVERY bounded_packed_q_interval_encoded outer_boxes /\
  LENGTH outer_boxes = 6 /\ 524403 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (bounded_object_q_cv_list outer_boxes);
         from_cv (Num 1)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_product_source_state_cv
          radii center_boxes outer_boxes 1)),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_delta_product_source_state_eval
  >> simp []
QED

Theorem bounded_case16594_object_delta_product_source2_state_eval:
  EVERY bounded_object_q_encoded radii /\ LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_boxes /\
  LENGTH center_boxes = 6 /\
  EVERY bounded_packed_q_interval_encoded outer_boxes /\
  LENGTH outer_boxes = 6 /\ 524403 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (bounded_object_q_cv_list outer_boxes);
         from_cv (Num 2)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_product_source_state_cv
          radii center_boxes outer_boxes 2)),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_delta_product_source_state_eval
  >> simp []
QED

val _ = export_theory ();
