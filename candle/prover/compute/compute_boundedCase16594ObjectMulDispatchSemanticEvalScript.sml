(*****************************************************************************
 * Production-dispatch semantic bridge for genuine case-16594 source eight.
 *
 * Source eight is the first outer-stack multiplication.  The numerical
 * multiplication refinement already exists; this theory lifts it through the
 * actual non-polynomial, ordinary, and top-level production wrappers.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectMulDispatchSemanticEval
Ancestors
  compute_boundedCase16594ObjectSource8Identity
  compute_boundedCase16594ObjectPrefix8SemanticEval
  compute_boundedCase16594ObjectPolyStackInvariant
  compute_boundedCase16594ObjectDispatchStepControlEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_source8_result_def:
  bounded_case16594_object_source8_result =
    bounded_object_q_taylor_mul
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      bounded_case16594_object_source4_result
      bounded_case16594_object_source7_result
End

Theorem bounded_case16594_object_nonpoly_mul_control_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_poly_step»
      [from_cv center_boxes;
       from_cv outer_boxes;
       from_cv radii;
       from_cv (Num 4);
       from_cv (Pair runtime_right (Pair runtime_left stack_rest))])
    (refs:hol_refs) =
      (M_success
        (from_cv (Pair (Num 1) (Pair runtime_result stack_rest))),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_nonpoly_step»
      [from_cv center_boxes;
       from_cv outer_boxes;
       from_cv radii;
       from_cv (Num 4);
       from_cv certificates;
       from_cv (Pair runtime_right (Pair runtime_left stack_rest))])
    refs =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair (Pair runtime_result stack_rest) certificates))),refs)
Proof
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
QED

Theorem bounded_case16594_object_genuine_mul_nonpoly_eval_semantic:
  bounded_object_q_taylor_runtime_refines runtime_left
      bounded_case16594_object_source4_result /\
  bounded_object_q_taylor_runtime_refines runtime_right
      bounded_case16594_object_source7_result /\
  4104 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_nonpoly_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_source8_cv;
         from_cv bounded_case16594_object_cell0_after_inverse_certificates_cv;
         from_cv
           (Pair runtime_right (Pair runtime_left stack_rest))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair runtime_result stack_rest)
            bounded_case16594_object_cell0_after_inverse_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      bounded_case16594_object_source8_result
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 1`, `refs` |-> `refs`,
          `runtime_radii` |->
            `bounded_case16594_object_cell0_runtime_radii`,
          `semantic_radii` |->
            `bounded_case16594_object_cell0_word_radii`,
          `weights` |-> `bounded_case16594_object_cell0_weights`,
          `runtime_left_state` |-> `runtime_left`,
          `semantic_left_state` |->
            `bounded_case16594_object_source4_result`,
          `runtime_right_state` |-> `runtime_right`,
          `semantic_right_state` |->
            `bounded_case16594_object_source7_result`,
          `center_boxes` |->
            `bounded_case16594_object_cell0_center_boxes_cv`,
          `outer_boxes` |->
            `bounded_case16594_object_cell0_outer_boxes_cv`,
          `rest` |-> `stack_rest`]
         compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_case16594_object_poly_step_mul_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> simp
           [compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encoded,
            compute_boundedCase16594ObjectFirstPolyRunBridgeTheory.bounded_case16594_object_source0_runtime_radii_length,
            compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs,
            compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_equivalent]
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (PURE_REWRITE_TAC
        [compute_boundedCase16594ObjectSource8IdentityTheory.bounded_case16594_object_cell0_source8_identity,
         GSYM
           compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encode]
      >> irule bounded_case16594_object_nonpoly_mul_control_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac
       [bounded_case16594_object_source8_result_def]
QED

Theorem bounded_case16594_object_genuine_mul_ordinary_eval_semantic:
  bounded_object_q_taylor_runtime_refines runtime_left
      bounded_case16594_object_source4_result /\
  bounded_object_q_taylor_runtime_refines runtime_right
      bounded_case16594_object_source7_result /\
  4105 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_ordinary_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_source8_cv;
         from_cv bounded_case16594_object_cell0_after_inverse_certificates_cv;
         from_cv
           (Pair runtime_right (Pair runtime_left stack_rest))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair runtime_result stack_rest)
            bounded_case16594_object_cell0_after_inverse_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      bounded_case16594_object_source8_result
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 1`, `refs` |-> `refs`]
          bounded_case16594_object_genuine_mul_nonpoly_eval_semantic)
  >> impl_tac
  >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (PURE_REWRITE_TAC
        [compute_boundedCase16594ObjectSource8IdentityTheory.bounded_case16594_object_cell0_source8_identity]
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_nonpair_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> fs
           [compute_boundedCase16594ObjectSource8IdentityTheory.bounded_case16594_object_cell0_source8_identity])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_genuine_mul_dispatch_eval_semantic:
  bounded_object_q_taylor_runtime_refines runtime_left
      bounded_case16594_object_source4_result /\
  bounded_object_q_taylor_runtime_refines runtime_right
      bounded_case16594_object_source7_result /\
  4106 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_code8_cv;
         from_cv bounded_case16594_object_cell0_source8_cv;
         from_cv bounded_case16594_object_cell0_after_inverse_certificates_cv;
         from_cv
           (Pair runtime_right (Pair runtime_left stack_rest))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair runtime_result stack_rest)
            bounded_case16594_object_cell0_after_inverse_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      bounded_case16594_object_source8_result
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 1`, `refs` |-> `refs`]
          bounded_case16594_object_genuine_mul_ordinary_eval_semantic)
  >> impl_tac
  >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (PURE_REWRITE_TAC
        [compute_boundedCase16594ObjectSource8IdentityTheory.bounded_case16594_object_cell0_code8_identity]
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
