(*****************************************************************************
 * Registered evaluator semantics for historical raw interval-list addition.
 *
 * Multiplication constructs its center gradient and second-order terms in an
 * unrounded integer representation, then performs one outward rounding pass.
 * This theorem follows the literal recursive source operation over arbitrary
 * raw interval objects; it does not specialize the proof to case-10173 data.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalRawListAddEval
Ancestors
  compute_registeredCase10173HistoricalListArithmeticEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_raw_interval_list_add_body_def:
  registered_case10173_fs_raw_interval_list_add_body =
    If (Uop Ispair (Var «xs»))
      (If (Uop Ispair (Var «ys»))
        (Pair
          (App «candle_cv_fs_raw_interval_add»
            [Uop Fst (Var «xs»);Uop Fst (Var «ys»)])
          (App «candle_cv_fs_raw_interval_list_add»
            [Uop Snd (Var «xs»);Uop Snd (Var «ys»)]))
        (Num 0))
      (Num 0)
End

Definition registered_case10173_fs_raw_interval_list_add_object_def:
  registered_case10173_fs_raw_interval_list_add_object
      ([]:cv list) [] = SOME [] /\
  registered_case10173_fs_raw_interval_list_add_object
      (left::left_rest) (right::right_rest) =
    (case bounded_object_fs_raw_interval_add left right of
     | NONE => NONE
     | SOME entry =>
       case registered_case10173_fs_raw_interval_list_add_object
         left_rest right_rest of
       | NONE => NONE
       | SOME entries => SOME (entry::entries)) /\
  registered_case10173_fs_raw_interval_list_add_object _ _ = NONE
End

Theorem registered_case10173_fs_raw_interval_list_add_object_length:
  !right result.
    registered_case10173_fs_raw_interval_list_add_object
      left right = SOME result ==>
    LENGTH left = LENGTH right /\ LENGTH result = LENGTH left
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> rw [registered_case10173_fs_raw_interval_list_add_object_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_fs_raw_interval_list_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_interval_list_add» =
    SOME
      ([«xs»;«ys»],
       registered_case10173_fs_raw_interval_list_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_interval_list_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_list_add»
        [from_cv (registered_case10173_cv_list left);
         from_cv (registered_case10173_cv_list right)])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«xs»,from_cv (registered_case10173_cv_list left));
         («ys»,from_cv (registered_case10173_cv_list right))]
        registered_case10173_fs_raw_interval_list_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_interval_list_add_lookup]
QED

Theorem registered_case10173_fs_raw_interval_list_add_object_eval:
  !right result clock refs.
    registered_case10173_fs_raw_interval_list_add_object
        left right = SOME result /\
    LENGTH left + 5 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_add»
          [from_cv (registered_case10173_cv_list left);
           from_cv (registered_case10173_cv_list right)])
        (refs:hol_refs) =
      (M_success
        (from_cv (registered_case10173_cv_list result)),refs)
Proof
  Induct_on `left`
  >- (Cases_on `right`
      >> rpt strip_tac
      >> gvs [registered_case10173_fs_raw_interval_list_add_object_def]
      >> rw [registered_case10173_fs_raw_interval_list_add_unfold]
      >> simp
           [registered_case10173_fs_raw_interval_list_add_body_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
            compute_execTheory.from_cv_def,
            Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> Cases_on `right`
  >- (rpt strip_tac
      >> gvs [registered_case10173_fs_raw_interval_list_add_object_def])
  >> rpt strip_tac
  >> Cases_on `bounded_object_fs_raw_interval_add h' h`
  >> gvs [registered_case10173_fs_raw_interval_list_add_object_def]
  >> Cases_on
       `registered_case10173_fs_raw_interval_list_add_object left t`
  >> gvs [registered_case10173_fs_raw_interval_list_add_object_def]
  >> rw [registered_case10173_fs_raw_interval_list_add_unfold]
  >> simp
       [registered_case10173_fs_raw_interval_list_add_body_def,
        compute_evalTheory.subst_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair h' (registered_case10173_cv_list left):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair h (registered_case10173_cv_list t):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `x`,
            `right_result` |-> `registered_case10173_cv_list x'`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_add»
            [Uop Fst
               (Pair (from_cv h')
                 (from_cv (registered_case10173_cv_list left)));
             Uop Fst
               (Pair (from_cv h)
                 (from_cv (registered_case10173_cv_list t)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_add»
            [from_cv h';from_cv h]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
        >> intLib.ARITH_TAC)
      >> rw []
      >> irule
           compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_raw_interval_add_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_add»
          [Uop Snd
             (Pair (from_cv h')
               (from_cv (registered_case10173_cv_list left)));
           Uop Snd
             (Pair (from_cv h)
               (from_cv (registered_case10173_cv_list t)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_add»
          [from_cv (registered_case10173_cv_list left);
           from_cv (registered_case10173_cv_list t)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
        >> intLib.ARITH_TAC)
  >> rw []
  >> first_x_assum irule
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
