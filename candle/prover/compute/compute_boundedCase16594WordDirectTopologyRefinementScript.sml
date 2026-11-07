(*****************************************************************************
 * Refinement of the direct compact-topology executor to the ordinary cexp   *
 * topology program embedded in the unchanged Flyspeck whole-call source.    *
 *****************************************************************************)
Theory compute_boundedCase16594WordDirectTopologyRefinement
Ancestors
  compute_boundedCase16594WordDirectTopology
  compute_boundedCase16594Cell0WholeTopologyEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_direct_boxes_joinable_def:
  bounded_case16594_direct_boxes_joinable (Num left_terminal) right_boxes = T /\
  bounded_case16594_direct_boxes_joinable
      (Pair (Num malformed_left) left_tail) right_boxes = F /\
  bounded_case16594_direct_boxes_joinable
      (Pair (Pair left_lower left_upper) left_tail)
      (Num malformed_right) = F /\
  bounded_case16594_direct_boxes_joinable
      (Pair (Pair left_lower left_upper) left_tail)
      (Pair (Num malformed_right_interval) right_tail) = F /\
  bounded_case16594_direct_boxes_joinable
      (Pair (Pair left_lower left_upper) left_tail)
      (Pair (Pair right_lower right_upper) right_tail) =
    bounded_case16594_direct_boxes_joinable left_tail right_tail
End

Definition bounded_case16594_direct_boxes_join_body_def:
  bounded_case16594_direct_boxes_join_body =
    If (Uop Ispair (Var «left»))
      (If (Uop Ispair (Var «right»))
        (Pair
          (Pair (Uop Fst (Uop Fst (Var «left»)))
            (Uop Snd (Uop Fst (Var «right»))))
          (App «candle_cv_q_boxes_compact_join»
            [Uop Snd (Var «left»);Uop Snd (Var «right»)]))
        (Num 0))
      (Num 0)
End

Theorem bounded_case16594_direct_compute_eval_literal_app2:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME ([first_name;second_name],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv (first_argument:cv);from_cv (second_argument:cv)])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(first_name,from_cv first_argument);
         (second_name,from_cv second_argument)] body)
      refs
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
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_direct_boxes_join_named_lookup:
  ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_q_boxes_compact_join» =
    SOME
      ([«left»;«right»],bounded_case16594_direct_boxes_join_body)
Proof
  rw
    [compute_boundedCase16594Cell0WholeCombinedLookupsTheory.bounded_case16594_cell0_whole_combined_boxes_compact_join_lookup,
     bounded_case16594_direct_boxes_join_body_def]
QED

Theorem bounded_case16594_direct_boxes_join_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_q_boxes_compact_join»
        [from_cv left_boxes;from_cv right_boxes]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_cell0_whole_combined_ceqs
      (subst
        [(«left»,from_cv left_boxes);(«right»,from_cv right_boxes)]
        bounded_case16594_direct_boxes_join_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_direct_compute_eval_literal_app2
  >> simp [bounded_case16594_direct_boxes_join_named_lookup]
QED

Theorem bounded_case16594_direct_cv_list_length_eval:
  !items clock refs.
    bounded_case16594_direct_cv_list_length items + 1 < clock ==>
    compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
        (App «candle_cv_list_length» [from_cv items]) (refs:hol_refs) =
      (M_success
        (Num (bounded_case16594_direct_cv_list_length items)),refs)
Proof
  Induct_on `items`
  >- (rpt strip_tac
      >> PURE_REWRITE_TAC [bounded_case16594_direct_cv_list_length_def]
      >> mp_tac
           (Q.INST [`items` |-> `Num n`,`clock` |-> `clock`,
                    `refs` |-> `refs`]
             compute_boundedCase16594Cell0WholeTopologyEvalTheory.bounded_case16594_cell0_whole_list_length_unfold)
      >> impl_tac >- intLib.ARITH_TAC
      >> disch_then (fn th => PURE_REWRITE_TAC [th])
      >> simp
           [compute_boundedCase16594Cell0WholeTopologyEvalTheory.bounded_case16594_cell0_whole_list_length_body_def,
            compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> rw [bounded_case16594_direct_cv_list_length_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_boundedCase16594Cell0WholeTopologyEvalTheory.bounded_case16594_cell0_whole_list_length_cons_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qpat_x_assum
       `!recursive_clock recursive_refs.
          bounded_case16594_direct_cv_list_length items' + 1 <
            recursive_clock ==> _`
       (qspecl_then [`clock - 1`,`refs`] mp_tac)
  >> impl_tac
  >- (fs [bounded_case16594_direct_cv_list_length_def]
      >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem bounded_case16594_direct_compute_eval_app2_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
    (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
    (M_success (from_cv result2),refs) ==>
  compute_eval clock ceqs
    (App function_name [argument1;argument2]) refs =
  compute_eval clock ceqs
    (App function_name [from_cv result1;from_cv result2]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 2`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_direct_boxes_join_eval:
  !left_boxes right_boxes clock refs.
    bounded_case16594_direct_boxes_joinable left_boxes right_boxes /\
    bounded_case16594_direct_cv_list_length left_boxes + 1 < clock ==>
    compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_q_boxes_compact_join»
        [from_cv left_boxes;from_cv right_boxes]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_direct_boxes_join left_boxes right_boxes)),refs)
Proof
  Induct_on `left_boxes`
  >- (rpt strip_tac
      >> PURE_REWRITE_TAC [bounded_case16594_direct_boxes_join_def]
      >> mp_tac
           (Q.INST [`left_boxes` |-> `Num n`,
                    `right_boxes` |-> `right_boxes`,
                    `clock` |-> `clock`,`refs` |-> `refs`]
             bounded_case16594_direct_boxes_join_unfold)
      >> impl_tac
      >- (fs [bounded_case16594_direct_cv_list_length_def]
          >> intLib.ARITH_TAC)
      >> disch_then (fn th => PURE_REWRITE_TAC [th])
      >> simp
           [bounded_case16594_direct_boxes_join_body_def,
            compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> Cases_on `left_boxes`
  >> fs [bounded_case16594_direct_boxes_joinable_def]
  >> Cases_on `right_boxes`
  >> fs [bounded_case16594_direct_boxes_joinable_def]
  >> Cases_on `c'`
  >> fs [bounded_case16594_direct_boxes_joinable_def]
  >> rpt strip_tac
  >> sg
       `compute_eval (clock - 1)
          bounded_case16594_cell0_whole_combined_ceqs
          (App «candle_cv_q_boxes_compact_join»
            [from_cv left_boxes';from_cv c0']) refs =
        (M_success
          (from_cv
            (bounded_case16594_direct_boxes_join left_boxes' c0')),refs)`
  >- (qpat_x_assum
        `!recursive_right recursive_clock recursive_refs.
           bounded_case16594_direct_boxes_joinable
             left_boxes' recursive_right /\ _ ==> _`
        (qspecl_then [`c0'`,`clock - 1`,`refs`] mp_tac)
      >> impl_tac
      >- (conj_tac >- asm_rewrite_tac []
          >> fs [bounded_case16594_direct_cv_list_length_def]
          >> intLib.ARITH_TAC)
      >> simp [])
  >> mp_tac
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST [`left_boxes` |-> `Pair (Pair c c0) left_boxes'`,
                  `right_boxes` |-> `Pair (Pair c'' c0'') c0'`,
                  `clock` |-> `clock`,`refs` |-> `refs`]
           bounded_case16594_direct_boxes_join_unfold))
  >> impl_tac
  >- (fs [bounded_case16594_direct_cv_list_length_def]
      >> intLib.ARITH_TAC)
  >> disch_then (fn th => PURE_REWRITE_TAC [th])
  >> simp
       [bounded_case16594_direct_boxes_join_body_def,
        bounded_case16594_direct_boxes_join_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv,
        compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`left` |-> `Pair c c0`,`right` |-> `left_boxes'`]
            compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair)]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`left` |-> `Pair c'' c0''`,`right` |-> `c0'`]
            compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair)]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         (Q.INST [`left_result` |-> `Pair c c0''`,
                  `right_result` |->
                    `bounded_case16594_direct_boxes_join left_boxes' c0'`]
           compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results))
  >> conj_tac
  >- simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_cell0_whole_combined_ceqs
          (App «candle_cv_q_boxes_compact_join»
            [from_cv left_boxes';from_cv c0']) refs`
  >> conj_tac
  >- (irule bounded_case16594_direct_compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >> simp
           [Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_direct_split_implies_join:
  !current_index axis_index roots left_boxes right_boxes.
    bounded_case16594_direct_boxes_split_exact_from current_index axis_index
      roots left_boxes right_boxes ==>
    bounded_case16594_direct_boxes_joinable left_boxes right_boxes /\
    bounded_case16594_direct_boxes_join left_boxes right_boxes = roots
Proof
  Induct_on `roots`
  >> simp
       [bounded_case16594_direct_boxes_split_exact_from_def,
        bounded_case16594_direct_boxes_joinable_def,
        bounded_case16594_direct_boxes_join_def]
  >> rpt gen_tac
  >> every_case_tac
  >> fs
       [bounded_case16594_direct_boxes_split_exact_from_def,
        bounded_case16594_direct_boxes_joinable_def,
        bounded_case16594_direct_boxes_join_def]
  >> rw []
  >> fs []
  >> metis_tac []
QED

val _ = export_theory ();
