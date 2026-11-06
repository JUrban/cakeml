(*****************************************************************************
 * Evaluator semantics for the genuine singleton topology trace.             *
 *                                                                            *
 * The imported whole call contains one leaf token, one job, and six boxes.  *
 * This theory proves that small control computation without replaying the    *
 * separately authenticated numerical job.                                   *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholeTopologyEval
Ancestors
  compute_boundedCase16594Cell0WholeJobsEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_cell0_whole_list_length_body_def:
  bounded_case16594_cell0_whole_list_length_body =
    If (Uop Ispair (Var «items»))
      (Binop Add (Num 1)
        (App «candle_cv_list_length» [Uop Snd (Var «items»)]))
      (Num 0)
End

Definition bounded_case16594_cell0_whole_compact_transition_body_def:
  bounded_case16594_cell0_whole_compact_transition_body =
    If (Uop Ispair (Var «token»))
      (Let «axis» (Uop Fst (Var «token»))
        (Let «marker» (Uop Snd (Var «token»))
          (Let «right» (Uop Fst (Var «stack»))
            (Let «after_right» (Uop Snd (Var «stack»))
              (Let «left» (Uop Fst (Var «after_right»))
                (Let «remaining_stack» (Uop Snd (Var «after_right»))
                  (Let «parent»
                    (App «candle_cv_q_boxes_compact_join»
                      [Var «left»;Var «right»])
                    (Pair
                      (App «candle_cv_bool_and»
                        [Binop Eq (Var «marker») (Num 0);
                         App «candle_cv_bool_and»
                          [Uop Ispair (Var «stack»);
                           App «candle_cv_bool_and»
                            [Uop Ispair (Var «after_right»);
                             App «candle_cv_bool_and»
                              [Binop Eq
                                (App «candle_cv_list_length»
                                  [Var «parent»])
                                (Var «tree_dim»);
                               App «candle_cv_bool_and»
                                [Binop Less (Num 0) (Var «axis»);
                                 App «candle_cv_bool_and»
                                  [Binop Less (Var «axis»)
                                    (Binop Add (Var «tree_dim») (Num 1));
                                   App «candle_cv_q_boxes_split_exact_from»
                                    [Num 1;Var «axis»;Var «parent»;
                                     Var «left»;Var «right»]]]]]]])
                      (Pair (Var «jobs»)
                        (Pair (Var «parent»)
                          (Var «remaining_stack»)))))))))))
      (Let «boxes» (Uop Snd (Uop Snd (Uop Fst (Var «jobs»))))
        (Pair
          (App «candle_cv_bool_and»
            [Binop Eq (Var «token») (Num 0);
             App «candle_cv_bool_and»
              [Uop Ispair (Var «jobs»);
               Binop Eq
                (App «candle_cv_list_length» [Var «boxes»])
                (Var «tree_dim»)]])
          (Pair (Uop Snd (Var «jobs»))
            (Pair (Var «boxes») (Var «stack»)))))
End

Theorem bounded_case16594_cell0_whole_list_length_named_lookup:
  ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_list_length» =
    SOME ([«items»],bounded_case16594_cell0_whole_list_length_body)
Proof
  rw
    [compute_boundedCase16594Cell0WholeCombinedLookupsTheory.bounded_case16594_cell0_whole_combined_list_length_lookup,
     bounded_case16594_cell0_whole_list_length_body_def]
QED

Theorem bounded_case16594_cell0_whole_compact_transition_named_lookup:
  ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition» =
    SOME
      ([«tree_dim»;«token»;«jobs»;«stack»],
       bounded_case16594_cell0_whole_compact_transition_body)
Proof
  rw
    [compute_boundedCase16594Cell0WholeCombinedLookupsTheory.bounded_case16594_cell0_whole_combined_compact_transition_lookup,
     bounded_case16594_cell0_whole_compact_transition_body_def]
QED

Theorem bounded_case16594_cell0_compute_eval_literal_app1:
  0 < clock /\
  ALOOKUP ceqs function_name = SOME ([argument_name],body) ==>
  compute_eval clock ceqs
      (App function_name [from_cv argument]) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst [(argument_name,from_cv argument)] body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_list_length_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_list_length» [from_cv items]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_cell0_whole_combined_ceqs
      (subst [(«items»,from_cv items)]
        bounded_case16594_cell0_whole_list_length_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_cell0_compute_eval_literal_app1
  >> simp [bounded_case16594_cell0_whole_list_length_named_lookup]
QED

Theorem bounded_case16594_cell0_whole_compute_eval_binop_add_num_results:
  compute_eval clock ceqs left (refs:hol_refs) =
      (M_success (Num left_result),refs) /\
  compute_eval clock ceqs right refs =
      (M_success (Num right_result),refs) ==>
  compute_eval clock ceqs (Binop Add left right) refs =
    (M_success (Num (left_result + right_result)),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_binop_def,compute_evalTheory.do_arith_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_list_length_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_list_length» [from_cv (Num 0)]) (refs:hol_refs) =
    (M_success (Num 0),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_cell0_whole_list_length_unfold]
  >> simp
       [bounded_case16594_cell0_whole_list_length_body_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_list_length_cons_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_list_length» [from_cv items]) (refs:hol_refs) =
    (M_success (Num result_length),refs) ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_list_length» [from_cv (Pair item items)]) refs =
    (M_success (Num (SUC result_length)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_cell0_whole_list_length_unfold]
  >> simp
       [bounded_case16594_cell0_whole_list_length_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
        compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair]
  >> irule EQ_TRANS
  >> qexists_tac `(M_success (Num (1 + result_length)),refs)`
  >> conj_tac
  >- (irule bounded_case16594_cell0_whole_compute_eval_binop_add_num_results
      >> conj_tac
      >- simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_cell0_whole_combined_ceqs
              (App «candle_cv_list_length» [from_cv items]) refs`
      >> conj_tac
      >- (irule
            compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app1_argument_result
          >> simp
               [compute_evalTheory.compute_eval_def,
                compute_execProofTheory.compute_eval_from_cv,
                compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
                ml_monadBaseTheory.st_ex_bind_def,
                ml_monadBaseTheory.st_ex_return_def]
          >> intLib.ARITH_TAC)
      >> simp [])
  >> simp []
QED

Theorem bounded_case16594_cell0_whole_metadata_length_eval:
  7 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_list_length»
        [from_cv bounded_case16594_cell0_whole_job_metadata])
      (refs:hol_refs) =
    (M_success (Num 6),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC
       [compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_job_metadata_def]
  >> irule
       (Q.INST [`result_length` |-> `5`]
          bounded_case16594_cell0_whole_list_length_cons_eval
        |> SIMP_RULE arith_ss [])
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (Q.INST [`result_length` |-> `4`]
          bounded_case16594_cell0_whole_list_length_cons_eval
        |> SIMP_RULE arith_ss [])
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (Q.INST [`result_length` |-> `3`]
          bounded_case16594_cell0_whole_list_length_cons_eval
        |> SIMP_RULE arith_ss [])
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (Q.INST [`result_length` |-> `2`]
          bounded_case16594_cell0_whole_list_length_cons_eval
        |> SIMP_RULE arith_ss [])
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (Q.INST [`result_length` |-> `1`]
          bounded_case16594_cell0_whole_list_length_cons_eval
        |> SIMP_RULE arith_ss [])
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (Q.INST [`result_length` |-> `0`]
          bounded_case16594_cell0_whole_list_length_cons_eval
        |> SIMP_RULE arith_ss [])
  >> conj_tac >- intLib.ARITH_TAC
  >> irule bounded_case16594_cell0_whole_list_length_nil_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_cell0_whole_compact_transition_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition»
      [from_cv tree_dim;from_cv token;from_cv jobs;from_cv stack])
    (refs:hol_refs) =
  compute_eval (clock - 1) bounded_case16594_cell0_whole_combined_ceqs
    (subst
      [(«tree_dim»,from_cv tree_dim);(«token»,from_cv token);
       («jobs»,from_cv jobs);(«stack»,from_cv stack)]
      bounded_case16594_cell0_whole_compact_transition_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_compute_eval_literal_app4
  >> simp [bounded_case16594_cell0_whole_compact_transition_named_lookup]
QED

Theorem bounded_case16594_cell0_whole_leaf_boxes_eval:
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (Uop Snd (Uop Snd (Uop Fst
        (from_cv bounded_case16594_cell0_whole_encoded_jobs))))
      (refs:hol_refs) =
    (M_success (from_cv bounded_case16594_cell0_whole_job_metadata),refs)
Proof
  simp
    [compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_encoded_jobs_shape,
     compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_job_shape,
     compute_execTheory.from_cv_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_leaf_jobs_tail_eval:
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (Uop Snd (from_cv bounded_case16594_cell0_whole_encoded_jobs))
      (refs:hol_refs) = (M_success (Num 0),refs)
Proof
  simp
    [compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_encoded_jobs_shape,
     compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_nil_tails,
     compute_execTheory.from_cv_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_leaf_jobs_ispair_eval:
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (Uop Ispair (from_cv bounded_case16594_cell0_whole_encoded_jobs))
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  simp
    [compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_encoded_jobs_shape,
     compute_execTheory.from_cv_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_leaf_eq_zero_eval:
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (Binop Eq (Num 0) (Num 0)) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_binop_def,compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_leaf_length_eq_eval:
  7 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (Binop Eq
        (App «candle_cv_list_length»
          [from_cv bounded_case16594_cell0_whole_job_metadata])
        (from_cv bounded_case16594_cell0_whole_tree_dim)) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp
       [compute_boundedCase16594Cell0WholePayloadsTheory.bounded_case16594_cell0_whole_tree_dim_def]
  >> irule
       compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_binop_eq_num_same
  >> irule bounded_case16594_cell0_whole_metadata_length_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_cell0_whole_leaf_inner_guard_eval:
  7 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_bool_and»
        [Uop Ispair (from_cv bounded_case16594_cell0_whole_encoded_jobs);
         Binop Eq
           (App «candle_cv_list_length»
             [from_cv bounded_case16594_cell0_whole_job_metadata])
           (from_cv bounded_case16594_cell0_whole_tree_dim)])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_true_one_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> simp
       [bounded_case16594_cell0_whole_leaf_jobs_ispair_eval,
        bounded_case16594_cell0_whole_leaf_length_eq_eval]
QED

Theorem bounded_case16594_cell0_whole_leaf_guard_eval:
  7 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_bool_and»
        [Binop Eq (Num 0) (Num 0);
         App «candle_cv_bool_and»
           [Uop Ispair (from_cv bounded_case16594_cell0_whole_encoded_jobs);
            Binop Eq
              (App «candle_cv_list_length»
                [from_cv bounded_case16594_cell0_whole_job_metadata])
              (from_cv bounded_case16594_cell0_whole_tree_dim)]])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_true_one_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> simp
       [bounded_case16594_cell0_whole_leaf_eq_zero_eval,
        bounded_case16594_cell0_whole_leaf_inner_guard_eval]
QED

Theorem bounded_case16594_cell0_whole_leaf_result_eval:
  7 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (Pair
        (App «candle_cv_bool_and»
          [Binop Eq (Num 0) (Num 0);
           App «candle_cv_bool_and»
             [Uop Ispair (from_cv bounded_case16594_cell0_whole_encoded_jobs);
              Binop Eq
                (App «candle_cv_list_length»
                  [from_cv bounded_case16594_cell0_whole_job_metadata])
                (from_cv bounded_case16594_cell0_whole_tree_dim)]])
        (Pair
          (Uop Snd (from_cv bounded_case16594_cell0_whole_encoded_jobs))
          (Pair (from_cv bounded_case16594_cell0_whole_job_metadata) (Num 0))))
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Num 0)
            (Pair bounded_case16594_cell0_whole_job_metadata (Num 0))))),refs)
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results
  >> conj_tac
  >- simp [bounded_case16594_cell0_whole_leaf_guard_eval]
  >> irule
       compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results
  >> conj_tac
  >- simp [bounded_case16594_cell0_whole_leaf_jobs_tail_eval]
  >> irule
       compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_leaf_transition_eval:
  12 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition»
      [from_cv bounded_case16594_cell0_whole_tree_dim;
       from_cv (Num 0);
       from_cv bounded_case16594_cell0_whole_encoded_jobs;
       from_cv (Num 0)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Num 0)
            (Pair bounded_case16594_cell0_whole_job_metadata (Num 0))))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_cell0_whole_compact_transition_unfold]
  >> simp
       [bounded_case16594_cell0_whole_compact_transition_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_num]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_cell0_whole_job_metadata`
  >> conj_tac
  >- simp [bounded_case16594_cell0_whole_leaf_boxes_eval]
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         bounded_case16594_cell0_whole_leaf_result_eval)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
