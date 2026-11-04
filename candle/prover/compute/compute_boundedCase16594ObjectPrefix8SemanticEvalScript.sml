(*****************************************************************************
 * Linked genuine execution of case 16594 instructions zero through seven.
 *
 * The expensive 0--6 trace is reused as a theorem.  Its authenticated
 * post-sqrt state is then fed directly to the production dispatch theorem
 * for source 7.  This gives a cheap cumulative probe without duplicating
 * the earlier seven-step evaluator proof.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPrefix8SemanticEval
Ancestors
  compute_boundedCase16594ObjectPrefix7SemanticEval
  compute_boundedCase16594ObjectInverseDispatchSemanticEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_prefix0_through7_linked_runtime_refines:
  8226 < clock ==>
  ?runtime6 runtime_tail runtime7.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_program»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv
           (bounded_object_q_cv_list
             [Num 0;Num 0;Num 0;Num 0;Num 0;Num 0;Num 0]);
         from_cv
           (bounded_object_q_cv_list
             [bounded_case16594_object_cell0_source0_cv;
              bounded_case16594_object_cell0_source1_cv;
              bounded_case16594_object_cell0_source2_cv;
              bounded_case16594_object_cell0_source3_cv;
              bounded_case16594_object_cell0_source4_cv;
              bounded_case16594_object_cell0_source5_cv;
              bounded_case16594_object_cell0_source6_cv]);
         from_cv bounded_case16594_object_cell0_full_certificates_cv;
         from_cv (Num 0)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list (runtime6::runtime_tail))
            bounded_case16594_object_cell0_after_sqrt_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime6::runtime_tail)
      [bounded_case16594_object_source6_result;
       bounded_case16594_object_source4_result;
       bounded_case16594_object_pi_half_semantic;
       bounded_case16594_object_source2_result;
       bounded_case16594_object_source1_result;
       bounded_case16594_object_source0_result] /\
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv (Num 0);
         from_cv bounded_case16594_object_cell0_source7_cv;
         from_cv bounded_case16594_object_cell0_after_sqrt_certificates_cv;
         from_cv
           (bounded_object_q_cv_list (runtime6::runtime_tail))]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list (runtime7::runtime_tail))
            bounded_case16594_object_cell0_after_inverse_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime7::runtime_tail)
      [bounded_case16594_object_source7_result;
       bounded_case16594_object_source4_result;
       bounded_case16594_object_pi_half_semantic;
       bounded_case16594_object_source2_result;
       bounded_case16594_object_source1_result;
       bounded_case16594_object_source0_result]
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock`, `refs` |-> `refs`]
          compute_boundedCase16594ObjectPrefix7SemanticEvalTheory.bounded_case16594_object_prefix0_through6_dispatch_runtime_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `runtime_stack` strip_assume_tac)
  >> Cases_on `runtime_stack`
  >- fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock`, `runtime_item` |-> `h`,
          `stack_rest` |-> `bounded_object_q_cv_list t`,
          `refs` |-> `refs`]
         compute_boundedCase16594ObjectInverseDispatchSemanticEvalTheory.bounded_case16594_object_genuine_inverse_dispatch_eval_semantic)
  >> impl_tac
  >- (fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime7` strip_assume_tac)
  >> qexists_tac `h`
  >> qexists_tac `t`
  >> qexists_tac `runtime7`
  >> asm_rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_execTheory.from_cv_def]
  >> conj_tac
  >- (qpat_x_assum
        `compute_eval clock _
           (App «candle_cv_q_packed_object_dispatch_step» _) _ = _`
        mp_tac
      >> simp
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            compute_execTheory.from_cv_def])
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

val _ = export_theory ();
