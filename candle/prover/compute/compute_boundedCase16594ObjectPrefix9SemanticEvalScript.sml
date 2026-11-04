(*****************************************************************************
 * Linked genuine execution of case 16594 instructions zero through eight.
 *
 * The existing 0--7 theorem supplies an authenticated post-inverse stack.
 * The newly reusable production multiplication bridge then consumes the exact
 * top two semantic operands for source eight.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPrefix9SemanticEval
Ancestors
  compute_boundedCase16594ObjectMulDispatchSemanticEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_prefix0_through8_linked_runtime_refines:
  8226 < clock ==>
  ?runtime6 runtime4 runtime_rest runtime7 runtime8.
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
          (Pair
            (bounded_object_q_cv_list
              (runtime6::runtime4::runtime_rest))
            bounded_case16594_object_cell0_after_sqrt_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime6::runtime4::runtime_rest)
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
           (bounded_object_q_cv_list
             (runtime6::runtime4::runtime_rest))]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (bounded_object_q_cv_list
              (runtime7::runtime4::runtime_rest))
            bounded_case16594_object_cell0_after_inverse_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime7::runtime4::runtime_rest)
      [bounded_case16594_object_source7_result;
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
         from_cv bounded_case16594_object_cell0_code8_cv;
         from_cv bounded_case16594_object_cell0_source8_cv;
         from_cv bounded_case16594_object_cell0_after_inverse_certificates_cv;
         from_cv
           (bounded_object_q_cv_list
             (runtime7::runtime4::runtime_rest))]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (bounded_object_q_cv_list (runtime8::runtime_rest))
            bounded_case16594_object_cell0_after_inverse_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime8::runtime_rest)
      [bounded_case16594_object_source8_result;
       bounded_case16594_object_pi_half_semantic;
       bounded_case16594_object_source2_result;
       bounded_case16594_object_source1_result;
       bounded_case16594_object_source0_result]
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock`, `refs` |-> `refs`]
          compute_boundedCase16594ObjectPrefix8SemanticEvalTheory.bounded_case16594_object_prefix0_through7_linked_runtime_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `runtime6`
         (qx_choose_then `runtime_tail`
           (qx_choose_then `runtime7` strip_assume_tac)))
  >> Cases_on `runtime_tail`
  >- fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock`,
          `runtime_left` |-> `h`,
          `runtime_right` |-> `runtime7`,
          `stack_rest` |->
            `bounded_object_q_cv_list t`,
          `refs` |-> `refs`]
         compute_boundedCase16594ObjectMulDispatchSemanticEvalTheory.bounded_case16594_object_genuine_mul_dispatch_eval_semantic)
  >> impl_tac
  >- (fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime8` strip_assume_tac)
  >> qexists_tac `runtime6`
  >> qexists_tac `h`
  >> qexists_tac `t`
  >> qexists_tac `runtime7`
  >> qexists_tac `runtime8`
  >> asm_rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_execTheory.from_cv_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
