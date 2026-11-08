(*****************************************************************************
 * Production-dispatch lift for the first genuine atan instruction.
 *
 * The underlying evaluator and semantic refinement are proved in
 * compute_boundedCase16594ObjectAtanStepSemanticEval.  This theory proves
 * that the real non-polynomial, ordinary, and top-level dispatch wrappers
 * select that evaluator for the authenticated source-9 descriptor.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanDispatchSemanticEval
Ancestors
  compute_boundedCase16594ObjectAtanStepSemanticEval
  compute_boundedCase16594ObjectDispatchStepControlEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_nonpoly_atan_control_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_atn_step»
      [from_cv radii;
       from_cv certificates;
       from_cv stack]) (refs:hol_refs) = result ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_nonpoly_step»
      [from_cv center_boxes;
       from_cv outer_boxes;
       from_cv radii;
       from_cv (Num 7);
       from_cv certificates;
       from_cv stack]) refs = result
Proof
  strip_tac
  >> rw
       [compute_boundedCase16594ObjectPiHalfInvariantTheory.bounded_case16594_object_nonpoly_step_unfold]
  >> simp
       [compute_boundedCase16594ObjectPiHalfInvariantTheory.bounded_case16594_object_nonpoly_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> simp
       [compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_ispair_num,
        compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_compute_eval_if_num_eq]
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_genuine_atan_nonpoly_eval_semantic:
  bounded_object_q_taylor_runtime_refines runtime_item
      bounded_case16594_object_source8_result /\
  16385 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_nonpoly_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_source9_cv;
         from_cv bounded_case16594_object_cell0_after_inverse_certificates_cv;
         from_cv (Pair runtime_item stack_rest)]) (refs:hol_refs) =
    (M_success
      (Pair (Num 1)
        (Pair
          (Pair (from_cv runtime_result) (from_cv stack_rest))
          (from_cv
            bounded_case16594_object_cell0_after_atan_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      bounded_case16594_object_source9_result
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 1`, `refs` |-> `refs`]
          compute_boundedCase16594ObjectAtanStepSemanticEvalTheory.bounded_case16594_object_genuine_atan_step_eval_semantic)
  >> impl_tac
  >- (simp [] >> intLib.ARITH_TAC)
  >> strip_tac
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (PURE_REWRITE_TAC
        [compute_boundedCase16594ObjectSource9IdentityTheory.bounded_case16594_object_cell0_source9_cv_def]
      >> irule bounded_case16594_object_nonpoly_atan_control_eval
      >> conj_tac
      >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_genuine_atan_ordinary_eval_semantic:
  bounded_object_q_taylor_runtime_refines runtime_item
      bounded_case16594_object_source8_result /\
  16386 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_ordinary_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_source9_cv;
         from_cv bounded_case16594_object_cell0_after_inverse_certificates_cv;
         from_cv (Pair runtime_item stack_rest)]) (refs:hol_refs) =
    (M_success
      (Pair (Num 1)
        (Pair
          (Pair (from_cv runtime_result) (from_cv stack_rest))
          (from_cv
            bounded_case16594_object_cell0_after_atan_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      bounded_case16594_object_source9_result
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 1`, `refs` |-> `refs`]
          bounded_case16594_object_genuine_atan_nonpoly_eval_semantic)
  >> impl_tac
  >- (simp [] >> intLib.ARITH_TAC)
  >> strip_tac
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (PURE_REWRITE_TAC
        [compute_boundedCase16594ObjectSource9IdentityTheory.bounded_case16594_object_cell0_source9_cv_def]
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_nonpair_eval
      >> conj_tac
      >- intLib.ARITH_TAC
      >> fs
           [compute_boundedCase16594ObjectSource9IdentityTheory.bounded_case16594_object_cell0_source9_cv_def])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_genuine_atan_dispatch_eval_semantic:
  bounded_object_q_taylor_runtime_refines runtime_item
      bounded_case16594_object_source8_result /\
  16387 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv (Num 0);
         from_cv bounded_case16594_object_cell0_source9_cv;
         from_cv bounded_case16594_object_cell0_after_inverse_certificates_cv;
         from_cv (Pair runtime_item stack_rest)]) (refs:hol_refs) =
    (M_success
      (Pair (Num 1)
        (Pair
          (Pair (from_cv runtime_result) (from_cv stack_rest))
          (from_cv
            bounded_case16594_object_cell0_after_atan_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      bounded_case16594_object_source9_result
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 1`, `refs` |-> `refs`]
          bounded_case16594_object_genuine_atan_ordinary_eval_semantic)
  >> impl_tac
  >- (simp [] >> intLib.ARITH_TAC)
  >> strip_tac
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> conj_tac
      >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
