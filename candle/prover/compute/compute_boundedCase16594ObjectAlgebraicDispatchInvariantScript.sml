(*****************************************************************************
 * Generic production-dispatch preservation for the four certificate-free
 * outer algebraic instructions.  The numerical Taylor operations are
 * already covered by the polynomial-step invariant; this theory proves once
 * that the ordinary outer dispatcher reuses those operations and preserves
 * the exact runtime/semantic relation.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAlgebraicDispatchInvariant
Ancestors
  compute_boundedCase16594ObjectPiHalfInvariant
  compute_boundedCase16594ObjectPolyStackInvariant
  compute_boundedCase16594ObjectDispatchStepControlEval
Libs
  bossLib preamble intLib

val bounded_case16594_object_nonpoly_algebraic_control_tac =
  strip_tac
  >> rw
       [compute_boundedCase16594ObjectPiHalfInvariantTheory.bounded_case16594_object_nonpoly_step_unfold]
  >> simp
       [compute_boundedCase16594ObjectPiHalfInvariantTheory.bounded_case16594_object_nonpoly_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_ispair_num,
        compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_compute_eval_if_num_eq]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (simp
      [Once compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
      >> fs
           [compute_execTheory.from_cv_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_fst_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (simp
      [Once compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
      >> fs
           [compute_execTheory.from_cv_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> simp [compute_execProofTheory.compute_eval_from_cv]

Theorem bounded_case16594_object_nonpoly_neg_control_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_poly_step»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
       from_cv (Num 2);from_cv stack]) (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 1) next_stack)),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_nonpoly_step»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
       from_cv (Num 2);from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv (Pair (Num 1) (Pair next_stack certificates))),refs)
Proof
  bounded_case16594_object_nonpoly_algebraic_control_tac
QED

Theorem bounded_case16594_object_nonpoly_add_control_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_poly_step»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
       from_cv (Num 3);from_cv stack]) (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 1) next_stack)),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_nonpoly_step»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
       from_cv (Num 3);from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv (Pair (Num 1) (Pair next_stack certificates))),refs)
Proof
  bounded_case16594_object_nonpoly_algebraic_control_tac
QED

Theorem bounded_case16594_object_nonpoly_mul_control_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_poly_step»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
       from_cv (Num 4);from_cv stack]) (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 1) next_stack)),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_nonpoly_step»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
       from_cv (Num 4);from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv (Pair (Num 1) (Pair next_stack certificates))),refs)
Proof
  bounded_case16594_object_nonpoly_algebraic_control_tac
QED

Theorem bounded_case16594_object_nonpoly_square_control_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_poly_step»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
       from_cv (Num 5);from_cv stack]) (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 1) next_stack)),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_nonpoly_step»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
       from_cv (Num 5);from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv (Pair (Num 1) (Pair next_stack certificates))),refs)
Proof
  bounded_case16594_object_nonpoly_algebraic_control_tac
QED

Theorem bounded_case16594_object_neg_dispatch_eval_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_runtime_refines runtime_state semantic_state /\
  4106 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 2);from_cv certificates;
         from_cv (Pair runtime_state stack_rest)]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair (Pair result_state stack_rest) certificates))),refs) /\
    bounded_object_q_taylor_runtime_refines result_state
      (bounded_object_q_taylor_neg semantic_radii weights semantic_state)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 3`, `refs` |-> `refs`,
          `runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`,
          `weights` |-> `weights`,
          `runtime_state` |-> `runtime_state`,
          `semantic_state` |-> `semantic_state`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `rest` |-> `stack_rest`]
         compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_case16594_object_poly_step_neg_eval_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `result_state` strip_assume_tac)
  >> qexists_tac `result_state`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_nonpair_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule bounded_case16594_object_nonpoly_neg_control_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> `clock - 1 - 1 - 1 = clock - 3` by intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_add_dispatch_eval_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_runtime_refines
    runtime_left_state semantic_left_state /\
  bounded_object_q_taylor_runtime_refines
    runtime_right_state semantic_right_state /\
  4106 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 3);from_cv certificates;
         from_cv
           (Pair runtime_right_state
             (Pair runtime_left_state stack_rest))]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair (Pair result_state stack_rest) certificates))),refs) /\
    bounded_object_q_taylor_runtime_refines result_state
      (bounded_object_q_taylor_add semantic_radii weights
        semantic_left_state semantic_right_state)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 3`, `refs` |-> `refs`,
          `runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`,
          `weights` |-> `weights`,
          `runtime_left_state` |-> `runtime_left_state`,
          `semantic_left_state` |-> `semantic_left_state`,
          `runtime_right_state` |-> `runtime_right_state`,
          `semantic_right_state` |-> `semantic_right_state`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `rest` |-> `stack_rest`]
         compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_case16594_object_poly_step_add_eval_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `result_state` strip_assume_tac)
  >> qexists_tac `result_state`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_nonpair_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule bounded_case16594_object_nonpoly_add_control_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> `clock - 1 - 1 - 1 = clock - 3` by intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_mul_dispatch_eval_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_runtime_refines
    runtime_left_state semantic_left_state /\
  bounded_object_q_taylor_runtime_refines
    runtime_right_state semantic_right_state /\
  4106 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 4);from_cv certificates;
         from_cv
           (Pair runtime_right_state
             (Pair runtime_left_state stack_rest))]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair (Pair result_state stack_rest) certificates))),refs) /\
    bounded_object_q_taylor_runtime_refines result_state
      (bounded_object_q_taylor_mul semantic_radii weights
        semantic_left_state semantic_right_state)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 3`, `refs` |-> `refs`,
          `runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`,
          `weights` |-> `weights`,
          `runtime_left_state` |-> `runtime_left_state`,
          `semantic_left_state` |-> `semantic_left_state`,
          `runtime_right_state` |-> `runtime_right_state`,
          `semantic_right_state` |-> `semantic_right_state`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `rest` |-> `stack_rest`]
         compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_case16594_object_poly_step_mul_eval_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `result_state` strip_assume_tac)
  >> qexists_tac `result_state`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_nonpair_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule bounded_case16594_object_nonpoly_mul_control_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> `clock - 1 - 1 - 1 = clock - 3` by intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_square_dispatch_eval_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_runtime_refines runtime_state semantic_state /\
  4106 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 5);from_cv certificates;
         from_cv (Pair runtime_state stack_rest)]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair (Pair result_state stack_rest) certificates))),refs) /\
    bounded_object_q_taylor_runtime_refines result_state
      (bounded_object_q_taylor_mul semantic_radii weights
        semantic_state semantic_state)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 3`, `refs` |-> `refs`,
          `runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`,
          `weights` |-> `weights`,
          `runtime_state` |-> `runtime_state`,
          `semantic_state` |-> `semantic_state`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `rest` |-> `stack_rest`]
         compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_case16594_object_poly_step_square_eval_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `result_state` strip_assume_tac)
  >> qexists_tac `result_state`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_nonpair_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule bounded_case16594_object_nonpoly_square_control_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> `clock - 1 - 1 - 1 = clock - 3` by intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
