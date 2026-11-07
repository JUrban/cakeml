(*****************************************************************************
 * Refinement of successful direct compact-topology transitions to the       *
 * ordinary cexp transition embedded in the unchanged Flyspeck whole call.   *
 *****************************************************************************)
Theory compute_boundedCase16594WordDirectTopologyTransitionRefinement
Ancestors
  compute_boundedCase16594WordDirectTopologyRefinement
Libs
  bossLib preamble intLib

Theorem bounded_case16594_direct_split_preserves_lengths:
  !current_index axis_index roots left_boxes right_boxes.
    bounded_case16594_direct_boxes_split_exact_from current_index axis_index
      roots left_boxes right_boxes ==>
    bounded_case16594_direct_cv_list_length left_boxes =
      bounded_case16594_direct_cv_list_length roots /\
    bounded_case16594_direct_cv_list_length right_boxes =
      bounded_case16594_direct_cv_list_length roots
Proof
  Induct_on `roots`
  >> simp
       [compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_boxes_split_exact_from_def,
        compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_cv_list_length_def]
  >> rpt gen_tac
  >> BasicProvers.EVERY_CASE_TAC
  >> fs
       [compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_boxes_split_exact_from_def,
        compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_cv_list_length_def]
  >> metis_tac []
QED

Theorem bounded_case16594_direct_leaf_transition_eval:
  !dimension ignored_outer ignored_center source_boxes remaining_jobs
    active_stack clock refs.
    bounded_case16594_direct_cv_list_length source_boxes = dimension /\
    dimension + 12 < clock ==>
    compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App
        «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition»
        [from_cv (Num dimension);from_cv (Num 0);
         from_cv
           (Pair (Pair ignored_outer (Pair ignored_center source_boxes))
             remaining_jobs);
         from_cv active_stack]) refs =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair remaining_jobs (Pair source_boxes active_stack)))),refs)
Proof
  rpt strip_tac
  >> rw
       [compute_boundedCase16594Cell0WholeTopologyEvalTheory.bounded_case16594_cell0_whole_compact_transition_unfold]
  >> simp
       [compute_boundedCase16594Cell0WholeTopologyEvalTheory.bounded_case16594_cell0_whole_compact_transition_body_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv,
        compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_num]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `source_boxes`
  >> conj_tac
  >- simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `Num 1`,
            `right_result` |->
              `Pair remaining_jobs (Pair source_boxes active_stack)`]
           compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results))
  >> conj_tac
  >- (irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_true_one_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp
           [Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_binop_def,compute_evalTheory.do_eq_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> irule
           compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_true_one_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp
           [Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> irule
           compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_binop_eq_num_same
      >> irule bounded_case16594_direct_cv_list_length_eval
      >> intLib.ARITH_TAC)
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
