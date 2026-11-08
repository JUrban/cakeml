(*****************************************************************************
 * Authenticated production-dispatch bridge for genuine instruction zero.
 *
 * The polynomial evaluator now returns an existential runtime state related
 * to the symbolic object-q result.  This theory threads that fact through
 * the real ordinary-step and dispatch-step control flow while retaining the
 * relation needed by the following instruction.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectFirstPolyDispatchBridge
Ancestors
  compute_boundedCase16594ObjectFirstPolyEnvironmentBridge
  compute_boundedCase16594ObjectDispatchStepControlEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_eval_snd_poly_source:
  compute_eval clock ceqs
      (Uop Snd (from_cv (Pair (Num 0) program))) (refs:hol_refs) =
    (M_success (from_cv program),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_poly_source_arguments_normalize:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         Uop Snd (from_cv (Pair (Num 0) program));
         Pair (Num 1) (Num 0)]) (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv program;from_cv (Pair (Num 1) (Num 0))]) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyTraceEvalTheory.bounded_case16594_object_compute_eval_app5_argument_results
  >> simp
       [bounded_case16594_object_eval_snd_poly_source,
        compute_execProofTheory.compute_eval_from_cv]
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> simp
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
QED

Theorem bounded_case16594_object_source0_exact_ordinary_runtime_refines:
  4108 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_ordinary_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_source0_cv;
         from_cv certificates;from_cv stack]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair (Pair runtime_result stack) certificates))),refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      bounded_case16594_object_source0_result
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 1`, `refs` |-> `refs`]
          bounded_case16594_object_source0_exact_environment_runtime_refines)
  >> impl_tac >- intLib.ARITH_TAC
  >> disch_then
       (qx_choose_then `runtime_result_stack` strip_assume_tac)
  >> Cases_on `runtime_result_stack`
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> qexists_tac `h`
  >> conj_tac
  >- (PURE_ONCE_REWRITE_TAC
        [compute_boundedCase16594ObjectFirstPolyRunBridgeTheory.bounded_case16594_object_source0_payload_split]
      >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_poly_success_eval)
      >> conj_tac >- intLib.ARITH_TAC
      >> sg `0:num < clock - 1` >- intLib.ARITH_TAC
      >> PURE_ONCE_REWRITE_TAC
           [MATCH_MP
              (Q.INST
                [`clock` |-> `clock - 1`,
                 `center_boxes` |->
                   `bounded_case16594_object_cell0_center_boxes_cv`,
                 `outer_boxes` |->
                   `bounded_case16594_object_cell0_outer_boxes_cv`,
                 `radii` |-> `bounded_case16594_object_cell0_radii_cv`,
                 `program` |->
                   `bounded_case16594_object_source0_program_cv`,
                 `refs` |-> `refs`]
                (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                  bounded_case16594_object_poly_source_arguments_normalize))
              (ASSUME ``0:num < clock - 1``)]
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_source0_exact_dispatch_runtime_refines:
  4109 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv (Num 0);
         from_cv bounded_case16594_object_cell0_source0_cv;
         from_cv certificates;from_cv stack]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair (Pair runtime_result stack) certificates))),refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      bounded_case16594_object_source0_result
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 1`, `refs` |-> `refs`]
          bounded_case16594_object_source0_exact_ordinary_runtime_refines)
  >> impl_tac >- intLib.ARITH_TAC
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
