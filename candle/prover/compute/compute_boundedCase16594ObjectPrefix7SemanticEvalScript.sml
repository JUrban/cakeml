(*****************************************************************************
 * Genuine semantic execution of case 16594 instructions zero through six.
 *
 * This is the first authentic multi-instruction object-dispatch prefix: it
 * starts with the production empty stack, runs the real polynomial, pi/2,
 * and sqrt sources, consumes the genuine sqrt certificate packet, and
 * retains a semantic refinement relation for the resulting stack.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPrefix7SemanticEval
Ancestors
  compute_boundedCase16594ObjectSqrtStepSemanticEval
  compute_boundedCase16594ObjectDispatchProgramTraceEval
  compute_boundedCase16594ObjectFirstPolyDispatchBridge
  compute_boundedCase16594ObjectPrefixPolynomialInvariant
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_prefix0_through6_dispatch_runtime_refines:
  8226 < clock ==>
  ?runtime_stack.
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
          (Pair (bounded_object_q_cv_list runtime_stack)
            bounded_case16594_object_cell0_after_sqrt_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_stack_runtime_refines runtime_stack
      [bounded_case16594_object_source6_result;
       bounded_case16594_object_source4_result;
       bounded_case16594_object_pi_half_semantic;
       bounded_case16594_object_source2_result;
       bounded_case16594_object_source1_result;
       bounded_case16594_object_source0_result]
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 1`,
          `certificates` |->
            `bounded_case16594_object_cell0_full_certificates_cv`,
          `stack` |-> `Num 0`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectFirstPolyDispatchBridgeTheory.bounded_case16594_object_source0_exact_dispatch_runtime_refines)
  >> impl_tac >- intLib.ARITH_TAC
  >> disch_then (qx_choose_then `runtime0` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 3`, `runtime_stack` |-> `[runtime0]`,
          `semantic_stack` |->
            `[bounded_case16594_object_source0_result]`,
          `certificates` |->
            `bounded_case16594_object_cell0_full_certificates_cv`,
          `refs` |-> `refs`]
         compute_boundedCase16594ObjectPrefixPolynomialInvariantTheory.bounded_case16594_object_source1_dispatch_runtime_refines)
  >> impl_tac
  >- (simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime1` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 5`,
          `runtime_stack` |-> `[runtime1;runtime0]`,
          `semantic_stack` |->
            `[bounded_case16594_object_source1_result;
              bounded_case16594_object_source0_result]`,
          `certificates` |->
            `bounded_case16594_object_cell0_full_certificates_cv`,
          `refs` |-> `refs`]
         compute_boundedCase16594ObjectPrefixPolynomialInvariantTheory.bounded_case16594_object_source2_dispatch_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime2` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 7`,
          `center_boxes` |->
            `bounded_case16594_object_cell0_center_boxes_cv`,
          `outer_boxes` |->
            `bounded_case16594_object_cell0_outer_boxes_cv`,
          `radii` |-> `bounded_case16594_object_cell0_radii_cv`,
          `runtime_stack` |-> `[runtime2;runtime1;runtime0]`,
          `semantic_stack` |->
            `[bounded_case16594_object_source2_result;
              bounded_case16594_object_source1_result;
              bounded_case16594_object_source0_result]`,
          `certificates` |->
            `bounded_case16594_object_cell0_full_certificates_cv`,
          `refs` |-> `refs`]
         compute_boundedCase16594ObjectPiHalfInvariantTheory.bounded_case16594_object_dispatch_pi_half_eval_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 9`,
          `runtime_stack` |->
            `[bounded_case16594_object_pi_half_runtime_cv;
              runtime2;runtime1;runtime0]`,
          `semantic_stack` |->
            `[bounded_case16594_object_pi_half_semantic;
              bounded_case16594_object_source2_result;
              bounded_case16594_object_source1_result;
              bounded_case16594_object_source0_result]`,
          `certificates` |->
            `bounded_case16594_object_cell0_full_certificates_cv`,
          `refs` |-> `refs`]
         compute_boundedCase16594ObjectPrefixPolynomialInvariantTheory.bounded_case16594_object_source4_dispatch_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime4` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 11`,
          `runtime_stack` |->
            `[runtime4;bounded_case16594_object_pi_half_runtime_cv;
              runtime2;runtime1;runtime0]`,
          `semantic_stack` |->
            `[bounded_case16594_object_source4_result;
              bounded_case16594_object_pi_half_semantic;
              bounded_case16594_object_source2_result;
              bounded_case16594_object_source1_result;
              bounded_case16594_object_source0_result]`,
          `certificates` |->
            `bounded_case16594_object_cell0_full_certificates_cv`,
          `refs` |-> `refs`]
         compute_boundedCase16594ObjectPrefixPolynomialInvariantTheory.bounded_case16594_object_source5_dispatch_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime5` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 13`, `runtime_item` |-> `runtime5`,
          `stack_rest` |->
            `bounded_object_q_cv_list
              [runtime4;bounded_case16594_object_pi_half_runtime_cv;
               runtime2;runtime1;runtime0]`,
          `refs` |-> `refs`]
         compute_boundedCase16594ObjectSqrtStepSemanticEvalTheory.bounded_case16594_object_genuine_sqrt_dispatch_eval_semantic)
  >> impl_tac
  >- (fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime6` strip_assume_tac)
  >> qexists_tac
       `[runtime6;runtime4;bounded_case16594_object_pi_half_runtime_cv;
         runtime2;runtime1;runtime0]`
  >> conj_tac
  >- (PURE_REWRITE_TAC
       [compute_execTheory.from_cv_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
      >> irule
           (SIMP_RULE std_ss
             [compute_execTheory.from_cv_def,
              compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
             (Q.INST
               [`clock` |-> `clock`,
                `center_boxes` |->
                  `bounded_case16594_object_cell0_center_boxes_cv`,
                `outer_boxes` |->
                  `bounded_case16594_object_cell0_outer_boxes_cv`,
                `radii` |-> `bounded_case16594_object_cell0_radii_cv`,
                `code` |-> `Num 0`,
                `codes` |->
                  `bounded_object_q_cv_list
                    [Num 0;Num 0;Num 0;Num 0;Num 0;Num 0]`,
                `source` |->
                  `bounded_case16594_object_cell0_source0_cv`,
                `sources` |->
                  `bounded_object_q_cv_list
                    [bounded_case16594_object_cell0_source1_cv;
                     bounded_case16594_object_cell0_source2_cv;
                     bounded_case16594_object_cell0_source3_cv;
                     bounded_case16594_object_cell0_source4_cv;
                     bounded_case16594_object_cell0_source5_cv;
                     bounded_case16594_object_cell0_source6_cv]`,
                `certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `stack` |-> `Num 0`,
                `next_stack` |-> `Pair runtime0 (Num 0)`,
                `next_certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `final_state` |->
                  `Pair (Num 1)
                    (Pair
                      (bounded_object_q_cv_list
                        [runtime6;runtime4;
                         bounded_case16594_object_pi_half_runtime_cv;
                         runtime2;runtime1;runtime0])
                      bounded_case16594_object_cell0_after_sqrt_certificates_cv)`,
                `refs` |-> `refs`]
               compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_cons_eval))
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- fs
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
      >> irule
           (SIMP_RULE std_ss
             [compute_execTheory.from_cv_def,
              compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
             (Q.INST
               [`clock` |-> `clock - 2`,
                `center_boxes` |->
                  `bounded_case16594_object_cell0_center_boxes_cv`,
                `outer_boxes` |->
                  `bounded_case16594_object_cell0_outer_boxes_cv`,
                `radii` |-> `bounded_case16594_object_cell0_radii_cv`,
                `code` |-> `Num 0`,
                `codes` |->
                  `bounded_object_q_cv_list
                    [Num 0;Num 0;Num 0;Num 0;Num 0]`,
                `source` |->
                  `bounded_case16594_object_cell0_source1_cv`,
                `sources` |->
                  `bounded_object_q_cv_list
                    [bounded_case16594_object_cell0_source2_cv;
                     bounded_case16594_object_cell0_source3_cv;
                     bounded_case16594_object_cell0_source4_cv;
                     bounded_case16594_object_cell0_source5_cv;
                     bounded_case16594_object_cell0_source6_cv]`,
                `certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `stack` |-> `bounded_object_q_cv_list [runtime0]`,
                `next_stack` |->
                  `bounded_object_q_cv_list [runtime1;runtime0]`,
                `next_certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `final_state` |->
                  `Pair (Num 1)
                    (Pair
                      (bounded_object_q_cv_list
                        [runtime6;runtime4;
                         bounded_case16594_object_pi_half_runtime_cv;
                         runtime2;runtime1;runtime0])
                      bounded_case16594_object_cell0_after_sqrt_certificates_cv)`,
                `refs` |-> `refs`]
               compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_cons_eval))
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (`clock - 2 - 1 = clock - 3` by intLib.ARITH_TAC
          >> qpat_x_assum `compute_eval (clock - 3) _ _ _ = _` mp_tac
          >> simp
               [compute_execTheory.from_cv_def,
                compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
      >> irule
           (SIMP_RULE std_ss
             [compute_execTheory.from_cv_def,
              compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
             (Q.INST
               [`clock` |-> `clock - 2 - 2`,
                `center_boxes` |->
                  `bounded_case16594_object_cell0_center_boxes_cv`,
                `outer_boxes` |->
                  `bounded_case16594_object_cell0_outer_boxes_cv`,
                `radii` |-> `bounded_case16594_object_cell0_radii_cv`,
                `code` |-> `Num 0`,
                `codes` |->
                  `bounded_object_q_cv_list [Num 0;Num 0;Num 0;Num 0]`,
                `source` |->
                  `bounded_case16594_object_cell0_source2_cv`,
                `sources` |->
                  `bounded_object_q_cv_list
                    [bounded_case16594_object_cell0_source3_cv;
                     bounded_case16594_object_cell0_source4_cv;
                     bounded_case16594_object_cell0_source5_cv;
                     bounded_case16594_object_cell0_source6_cv]`,
                `certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `stack` |->
                  `bounded_object_q_cv_list [runtime1;runtime0]`,
                `next_stack` |->
                  `bounded_object_q_cv_list [runtime2;runtime1;runtime0]`,
                `next_certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `final_state` |->
                  `Pair (Num 1)
                    (Pair
                      (bounded_object_q_cv_list
                        [runtime6;runtime4;
                         bounded_case16594_object_pi_half_runtime_cv;
                         runtime2;runtime1;runtime0])
                      bounded_case16594_object_cell0_after_sqrt_certificates_cv)`,
                `refs` |-> `refs`]
               compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_cons_eval))
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (`clock - 2 - 2 - 1 = clock - 5` by intLib.ARITH_TAC
          >> qpat_x_assum `compute_eval (clock - 5) _ _ _ = _` mp_tac
          >> simp
               [compute_execTheory.from_cv_def,
                compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
      >> irule
           (SIMP_RULE std_ss
             [compute_execTheory.from_cv_def,
              compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
             (Q.INST
               [`clock` |-> `clock - 2 - 2 - 2`,
                `center_boxes` |->
                  `bounded_case16594_object_cell0_center_boxes_cv`,
                `outer_boxes` |->
                  `bounded_case16594_object_cell0_outer_boxes_cv`,
                `radii` |-> `bounded_case16594_object_cell0_radii_cv`,
                `code` |-> `Num 0`,
                `codes` |->
                  `bounded_object_q_cv_list [Num 0;Num 0;Num 0]`,
                `source` |->
                  `bounded_case16594_object_cell0_source3_cv`,
                `sources` |->
                  `bounded_object_q_cv_list
                    [bounded_case16594_object_cell0_source4_cv;
                     bounded_case16594_object_cell0_source5_cv;
                     bounded_case16594_object_cell0_source6_cv]`,
                `certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `stack` |->
                  `bounded_object_q_cv_list [runtime2;runtime1;runtime0]`,
                `next_stack` |->
                  `bounded_object_q_cv_list
                    [bounded_case16594_object_pi_half_runtime_cv;
                     runtime2;runtime1;runtime0]`,
                `next_certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `final_state` |->
                  `Pair (Num 1)
                    (Pair
                      (bounded_object_q_cv_list
                        [runtime6;runtime4;
                         bounded_case16594_object_pi_half_runtime_cv;
                         runtime2;runtime1;runtime0])
                      bounded_case16594_object_cell0_after_sqrt_certificates_cv)`,
                `refs` |-> `refs`]
               compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_cons_eval))
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (`clock - 2 - 2 - 2 - 1 = clock - 7` by intLib.ARITH_TAC
          >> qpat_x_assum `compute_eval (clock - 7) _ _ _ = _` mp_tac
          >> simp
               [compute_execTheory.from_cv_def,
                compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
                compute_boundedCase16594ObjectPrefix8IdentityTheory.bounded_case16594_object_cell0_source3_cv_def])
      >> irule
           (SIMP_RULE std_ss
             [compute_execTheory.from_cv_def,
              compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
             (Q.INST
               [`clock` |-> `clock - 2 - 2 - 2 - 2`,
                `center_boxes` |->
                  `bounded_case16594_object_cell0_center_boxes_cv`,
                `outer_boxes` |->
                  `bounded_case16594_object_cell0_outer_boxes_cv`,
                `radii` |-> `bounded_case16594_object_cell0_radii_cv`,
                `code` |-> `Num 0`,
                `codes` |-> `bounded_object_q_cv_list [Num 0;Num 0]`,
                `source` |->
                  `bounded_case16594_object_cell0_source4_cv`,
                `sources` |->
                  `bounded_object_q_cv_list
                    [bounded_case16594_object_cell0_source5_cv;
                     bounded_case16594_object_cell0_source6_cv]`,
                `certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `stack` |->
                  `bounded_object_q_cv_list
                    [bounded_case16594_object_pi_half_runtime_cv;
                     runtime2;runtime1;runtime0]`,
                `next_stack` |->
                  `bounded_object_q_cv_list
                    [runtime4;bounded_case16594_object_pi_half_runtime_cv;
                     runtime2;runtime1;runtime0]`,
                `next_certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `final_state` |->
                  `Pair (Num 1)
                    (Pair
                      (bounded_object_q_cv_list
                        [runtime6;runtime4;
                         bounded_case16594_object_pi_half_runtime_cv;
                         runtime2;runtime1;runtime0])
                      bounded_case16594_object_cell0_after_sqrt_certificates_cv)`,
                `refs` |-> `refs`]
               compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_cons_eval))
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (`clock - 2 - 2 - 2 - 2 - 1 = clock - 9` by intLib.ARITH_TAC
          >> qpat_x_assum `compute_eval (clock - 9) _ _ _ = _` mp_tac
          >> simp
               [compute_execTheory.from_cv_def,
                compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
      >> irule
           (SIMP_RULE std_ss
             [compute_execTheory.from_cv_def,
              compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
             (Q.INST
               [`clock` |-> `clock - 2 - 2 - 2 - 2 - 2`,
                `center_boxes` |->
                  `bounded_case16594_object_cell0_center_boxes_cv`,
                `outer_boxes` |->
                  `bounded_case16594_object_cell0_outer_boxes_cv`,
                `radii` |-> `bounded_case16594_object_cell0_radii_cv`,
                `code` |-> `Num 0`,
                `codes` |-> `bounded_object_q_cv_list [Num 0]`,
                `source` |->
                  `bounded_case16594_object_cell0_source5_cv`,
                `sources` |->
                  `bounded_object_q_cv_list
                    [bounded_case16594_object_cell0_source6_cv]`,
                `certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `stack` |->
                  `bounded_object_q_cv_list
                    [runtime4;bounded_case16594_object_pi_half_runtime_cv;
                     runtime2;runtime1;runtime0]`,
                `next_stack` |->
                  `bounded_object_q_cv_list
                    [runtime5;runtime4;
                     bounded_case16594_object_pi_half_runtime_cv;
                     runtime2;runtime1;runtime0]`,
                `next_certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `final_state` |->
                  `Pair (Num 1)
                    (Pair
                      (bounded_object_q_cv_list
                        [runtime6;runtime4;
                         bounded_case16594_object_pi_half_runtime_cv;
                         runtime2;runtime1;runtime0])
                      bounded_case16594_object_cell0_after_sqrt_certificates_cv)`,
                `refs` |-> `refs`]
               compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_cons_eval))
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `runtime5`
      >> conj_tac
      >- (`clock - 2 - 2 - 2 - 2 - 2 - 1 = clock - 11` by
            intLib.ARITH_TAC
          >> qpat_x_assum `compute_eval (clock - 11) _ _ _ = _` mp_tac
          >> simp
               [compute_execTheory.from_cv_def,
                compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
      >> `clock - 2 - 2 - 2 - 2 - 2 - 2 = clock - 12` by
           intLib.ARITH_TAC
      >> asm_rewrite_tac []
      >> irule
           (SIMP_RULE std_ss
             [compute_execTheory.from_cv_def,
              compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
             (Q.INST
               [`clock` |-> `clock - 12`,
                `center_boxes` |->
                  `bounded_case16594_object_cell0_center_boxes_cv`,
                `outer_boxes` |->
                  `bounded_case16594_object_cell0_outer_boxes_cv`,
                `radii` |-> `bounded_case16594_object_cell0_radii_cv`,
                `code` |-> `Num 0`, `codes` |-> `Num 0`,
                `source` |->
                  `bounded_case16594_object_cell0_source6_cv`,
                `sources` |-> `Num 0`,
                `certificates` |->
                  `bounded_case16594_object_cell0_full_certificates_cv`,
                `stack` |->
                  `bounded_object_q_cv_list
                    [runtime5;runtime4;
                     bounded_case16594_object_pi_half_runtime_cv;
                     runtime2;runtime1;runtime0]`,
                `next_stack` |->
                  `bounded_object_q_cv_list
                    [runtime6;runtime4;
                     bounded_case16594_object_pi_half_runtime_cv;
                     runtime2;runtime1;runtime0]`,
                `next_certificates` |->
                  `bounded_case16594_object_cell0_after_sqrt_certificates_cv`,
                `final_state` |->
                  `Pair (Num 1)
                    (Pair
                      (bounded_object_q_cv_list
                        [runtime6;runtime4;
                         bounded_case16594_object_pi_half_runtime_cv;
                         runtime2;runtime1;runtime0])
                      bounded_case16594_object_cell0_after_sqrt_certificates_cv)`,
                `refs` |-> `refs`]
               compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_cons_eval))
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (`clock - 12 - 1 = clock - 13` by intLib.ARITH_TAC
          >> qpat_x_assum `compute_eval (clock - 13) _ _ _ = _` mp_tac
          >> simp
               [compute_execTheory.from_cv_def,
                compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
      >> `clock - 12 - 2 = clock - 14` by intLib.ARITH_TAC
      >> asm_rewrite_tac []
      >> irule
           (SIMP_RULE std_ss
             [compute_execTheory.from_cv_def,
              compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
             (Q.INST
               [`clock` |-> `clock - 14`,
                `center_boxes` |->
                  `bounded_case16594_object_cell0_center_boxes_cv`,
                `outer_boxes` |->
                  `bounded_case16594_object_cell0_outer_boxes_cv`,
                `radii` |-> `bounded_case16594_object_cell0_radii_cv`,
                `codes_nil` |-> `0`, `sources_nil` |-> `0`,
                `certificates` |->
                  `bounded_case16594_object_cell0_after_sqrt_certificates_cv`,
                `stack` |->
                  `bounded_object_q_cv_list
                    [runtime6;runtime4;
                     bounded_case16594_object_pi_half_runtime_cv;
                     runtime2;runtime1;runtime0]`,
                `refs` |-> `refs`]
               compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_empty_eval))
      >> intLib.ARITH_TAC)
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

val _ = export_theory ();
