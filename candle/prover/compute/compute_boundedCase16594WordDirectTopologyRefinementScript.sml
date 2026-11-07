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

Definition bounded_case16594_direct_boxes_split_body_def:
  bounded_case16594_direct_boxes_split_body =
    If (Uop Ispair (Var «roots»))
      (If (Uop Ispair (Var «left»))
        (If (Uop Ispair (Var «right»))
          (App «candle_cv_bool_and»
            [If (Binop Eq (Var «current») (Var «axis»))
               (App «candle_cv_bool_and»
                 [Binop Eq (Uop Fst (Uop Fst (Var «left»)))
                    (Uop Fst (Uop Fst (Var «roots»)));
                  App «candle_cv_bool_and»
                   [Binop Eq (Uop Snd (Uop Fst (Var «right»)))
                      (Uop Snd (Uop Fst (Var «roots»)));
                    Binop Eq (Uop Snd (Uop Fst (Var «left»)))
                      (Uop Fst (Uop Fst (Var «right»)))]])
               (App «candle_cv_bool_and»
                 [Binop Eq (Uop Fst (Var «left»))
                    (Uop Fst (Var «roots»));
                  Binop Eq (Uop Fst (Var «right»))
                    (Uop Fst (Var «roots»))]);
             App «candle_cv_q_boxes_split_exact_from»
               [Binop Add (Var «current») (Num 1);Var «axis»;
                Uop Snd (Var «roots»);Uop Snd (Var «left»);
                Uop Snd (Var «right»)]])
          (Num 0))
        (Num 0))
      (If (Binop Eq (Var «roots») (Num 0))
        (App «candle_cv_bool_and»
          [Binop Eq (Var «left») (Num 0);
           Binop Eq (Var «right») (Num 0)])
        (Num 0))
End

Theorem bounded_case16594_direct_compute_eval_literal_app5:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME ([name1;name2;name3;name4;name5],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv argument1;from_cv argument2;from_cv argument3;
         from_cv argument4;from_cv argument5])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv argument1);(name2,from_cv argument2);
         (name3,from_cv argument3);(name4,from_cv argument4);
         (name5,from_cv argument5)] body) refs
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

Theorem bounded_case16594_direct_boxes_split_named_lookup:
  ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_q_boxes_split_exact_from» =
    SOME
      ([«current»;«axis»;«roots»;«left»;«right»],
       bounded_case16594_direct_boxes_split_body)
Proof
  rw
    [compute_boundedCase16594Cell0WholeCombinedLookupsTheory.bounded_case16594_cell0_whole_combined_boxes_split_exact_from_lookup,
     bounded_case16594_direct_boxes_split_body_def]
QED

Theorem bounded_case16594_direct_boxes_split_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_q_boxes_split_exact_from»
        [from_cv (Num current_index);from_cv (Num axis_index);
         from_cv roots;from_cv left_boxes;from_cv right_boxes])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_cell0_whole_combined_ceqs
      (subst
        [(«current»,from_cv (Num current_index));
         («axis»,from_cv (Num axis_index));(«roots»,from_cv roots);
         («left»,from_cv left_boxes);(«right»,from_cv right_boxes)]
        bounded_case16594_direct_boxes_split_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_direct_compute_eval_literal_app5
  >> simp [bounded_case16594_direct_boxes_split_named_lookup]
QED

Theorem bounded_case16594_direct_compute_eval_app5_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) /\
  compute_eval clock ceqs argument4 refs =
      (M_success (from_cv result4),refs) /\
  compute_eval clock ceqs argument5 refs =
      (M_success (from_cv result5),refs) ==>
  compute_eval clock ceqs
      (App function_name
        [argument1;argument2;argument3;argument4;argument5]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3;
         from_cv result4;from_cv result5]) refs
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
  >> Cases_on `LENGTH q = 5`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_direct_boxes_split_cons_eval:
  !current_index axis_index root_lower root_upper roots_tail
    left_lower left_upper left_tail right_lower right_upper right_tail
    clock refs.
    (if current_index = axis_index then
       left_lower = root_lower /\ right_upper = root_upper /\
       left_upper = right_lower
     else
       Pair left_lower left_upper = Pair root_lower root_upper /\
       Pair right_lower right_upper = Pair root_lower root_upper) /\
    compute_eval (clock - 1)
      bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_q_boxes_split_exact_from»
        [from_cv (Num (SUC current_index));from_cv (Num axis_index);
         from_cv roots_tail;from_cv left_tail;from_cv right_tail]) refs =
      (M_success (Num 1),refs) /\
    2 < clock ==>
    compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_q_boxes_split_exact_from»
        [from_cv (Num current_index);from_cv (Num axis_index);
         from_cv (Pair (Pair root_lower root_upper) roots_tail);
         from_cv (Pair (Pair left_lower left_upper) left_tail);
         from_cv (Pair (Pair right_lower right_upper) right_tail)]) refs =
      (M_success (Num 1),refs)
Proof
  rpt strip_tac
  >> rw [bounded_case16594_direct_boxes_split_unfold]
  >> simp
       [bounded_case16594_direct_boxes_split_body_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv,
        compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`left` |-> `Pair root_lower root_upper`,
                   `right` |-> `roots_tail`]
            compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair)]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`left` |-> `Pair left_lower left_upper`,
                   `right` |-> `left_tail`]
            compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair)]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`left` |-> `Pair right_lower right_upper`,
                   `right` |-> `right_tail`]
            compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair)]
  >> irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_true_one_eval
  >> conj_tac
  >- fs []
  >> conj_tac
  >- (Cases_on `current_index = axis_index`
      >> fs []
      >> simp
           [Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
            compute_evalTheory.do_snd_def,compute_evalTheory.do_binop_def,
            compute_evalTheory.do_eq_def,compute_evalTheory.option_def,
            compute_evalTheory.check_def,
            compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_named_lookup,
            compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_body_def,
            compute_evalTheory.subst_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_ignore_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_cell0_whole_combined_ceqs
          (App «candle_cv_q_boxes_split_exact_from»
            [from_cv (Num (SUC current_index));from_cv (Num axis_index);
             from_cv roots_tail;from_cv left_tail;from_cv right_tail]) refs`
  >> conj_tac
  >- (irule bounded_case16594_direct_compute_eval_app5_argument_results
      >> conj_tac >- fs []
      >> simp
           [Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.do_binop_def,compute_evalTheory.do_arith_def,
            compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_direct_boxes_split_eval:
  !current_index axis_index roots left_boxes right_boxes clock refs.
    bounded_case16594_direct_boxes_split_exact_from current_index axis_index
      roots left_boxes right_boxes /\
    bounded_case16594_direct_cv_list_length roots + 2 < clock ==>
    compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_q_boxes_split_exact_from»
        [from_cv (Num current_index);from_cv (Num axis_index);
         from_cv roots;from_cv left_boxes;from_cv right_boxes]) refs =
      (M_success (Num 1),refs)
Proof
  Induct_on `roots`
  >- (rpt gen_tac
      >> rw
           [bounded_case16594_direct_boxes_split_exact_from_def,
            bounded_case16594_direct_cv_list_length_def]
      >> mp_tac
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST [`current_index` |-> `current_index`,
                      `axis_index` |-> `axis_index`,
                      `roots` |-> `Num 0`,`left_boxes` |-> `Num 0`,
                      `right_boxes` |-> `Num 0`,`clock` |-> `clock`,
                      `refs` |-> `refs`]
               bounded_case16594_direct_boxes_split_unfold))
      >> impl_tac >- intLib.ARITH_TAC
      >> disch_then (fn th => PURE_REWRITE_TAC [th])
      >> simp
           [bounded_case16594_direct_boxes_split_body_def,
            compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
            compute_evalTheory.do_binop_def,compute_evalTheory.do_eq_def,
            compute_evalTheory.option_def,compute_evalTheory.check_def,
            compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_named_lookup,
            compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_body_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_ignore_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt gen_tac
  >> BasicProvers.EVERY_CASE_TAC
  >> fs [bounded_case16594_direct_boxes_split_exact_from_def]
  >> BasicProvers.EVERY_CASE_TAC
  >> rpt strip_tac
  >> (simp [compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_case16594_direct_boxes_split_cons_eval)
      >> conj_tac >- fs []
      >> conj_tac
      >- (qpat_x_assum
           `!recursive_current recursive_axis recursive_left recursive_right
              recursive_clock recursive_refs.
              bounded_case16594_direct_boxes_split_exact_from
                recursive_current recursive_axis roots' recursive_left
                recursive_right /\ _ ==> _`
           (fn th => match_mp_tac th)
          >> fs [bounded_case16594_direct_cv_list_length_def])
      >> fs [])
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
