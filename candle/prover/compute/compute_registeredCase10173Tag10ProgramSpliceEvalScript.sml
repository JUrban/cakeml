Theory compute_registeredCase10173Tag10ProgramSpliceEval
Ancestors
  compute_registeredCase10173SourceProgramIdentity
  compute_registeredCase10173CanonicalEval
  compute_registeredCase10173Tag10GenuineProgramMemoEval
Libs
  bossLib preamble intLib

Definition registered_case10173_tag10_hist_drop_eight_body_def:
  registered_case10173_tag10_hist_drop_eight_body =
    Uop Snd
      (Uop Snd
        (Uop Snd
          (Uop Snd
            (Uop Snd
              (Uop Snd
                (Uop Snd
                  (Uop Snd (Var «program»))))))))
End

Definition registered_case10173_tag10_hist_splice_aux_body_def:
  registered_case10173_tag10_hist_splice_aux_body =
    If (Uop Ispair (Var «splice_count»))
      (Num 0)
      (If (Binop Eq (Var «splice_count») (Num 0))
        (Pair (Num 10)
          (App «candle_cv_case10173_hist_drop_eight»
            [Var «program»]))
        (If (Uop Ispair (Var «program»))
          (Pair (Uop Fst (Var «program»))
            (App «candle_cv_case10173_hist_splice_aux»
              [Binop Sub (Var «splice_count») (Num 1);
               Uop Snd (Var «program»)]))
          (Num 0)))
End

Theorem registered_case10173_tag10_hist_drop_eight_lookup:
  ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_case10173_hist_drop_eight» =
    SOME ([«program»],registered_case10173_tag10_hist_drop_eight_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_tag10_hist_splice_aux_lookup:
  ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_case10173_hist_splice_aux» =
    SOME
      ([«splice_count»;«program»],
       registered_case10173_tag10_hist_splice_aux_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_tag10_hist_drop_eight_eval:
  8 <= registered_case10173_cv_list_length program /\
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_drop_eight» [from_cv program])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_drop 8 program)),refs)
Proof
  Cases_on `program`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> rename1 `Pair item0 tail0`
  >> Cases_on `tail0`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> rename1 `Pair item0 (Pair item1 tail1)`
  >> Cases_on `tail1`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> rename1 `Pair item0 (Pair item1 (Pair item2 tail2))`
  >> Cases_on `tail2`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> rename1 `Pair item0 (Pair item1 (Pair item2 (Pair item3 tail3)))`
  >> Cases_on `tail3`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> rename1
       `Pair item0 (Pair item1 (Pair item2 (Pair item3 (Pair item4 tail4))))`
  >> Cases_on `tail4`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> rename1
       `Pair item0
          (Pair item1 (Pair item2 (Pair item3 (Pair item4 (Pair item5 tail5)))))`
  >> Cases_on `tail5`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> rename1
       `Pair item0
          (Pair item1
            (Pair item2
              (Pair item3 (Pair item4 (Pair item5 (Pair item6 tail6))))))`
  >> Cases_on `tail6`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> rename1
       `Pair item0
          (Pair item1
            (Pair item2
              (Pair item3
                (Pair item4
                  (Pair item5 (Pair item6 (Pair item7 tail7)))))))`
  >> Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_tag10_hist_drop_eight_lookup,
        registered_case10173_tag10_hist_drop_eight_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def]
  >> EVAL_TAC
QED

Theorem registered_case10173_tag10_hist_splice_aux_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_splice_aux»
        [from_cv (Num splice_count);from_cv program])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (subst
        [(«splice_count»,from_cv (Num splice_count));
         («program»,from_cv program)]
        registered_case10173_tag10_hist_splice_aux_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_tag10_hist_splice_aux_lookup]
QED

Theorem registered_case10173_tag10_hist_splice_aux_subst:
  subst
    [(«splice_count»,from_cv (Num splice_count));
     («program»,from_cv program)]
    registered_case10173_tag10_hist_splice_aux_body =
  If (Uop Ispair (from_cv (Num splice_count)))
    (Num 0)
    (If (Binop Eq (from_cv (Num splice_count)) (Num 0))
      (Pair (Num 10)
        (App «candle_cv_case10173_hist_drop_eight» [from_cv program]))
      (If (Uop Ispair (from_cv program))
        (Pair (Uop Fst (from_cv program))
          (App «candle_cv_case10173_hist_splice_aux»
            [Binop Sub (from_cv (Num splice_count)) (Num 1);
             Uop Snd (from_cv program)]))
        (Num 0)))
Proof
  simp [registered_case10173_tag10_hist_splice_aux_body_def,
        compute_evalTheory.subst_def]
QED

Theorem registered_case10173_tag10_compute_eval_if_num_eq_zero:
  compute_eval clock ceqs
      (If (Binop Eq (Num n) (Num 0)) yes_branch no_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs
      (if n = 0 then yes_branch else no_branch) refs
Proof
  Cases_on `n`
  >> simp [compute_evalTheory.compute_eval_def,
           compute_evalTheory.do_binop_def,
           compute_evalTheory.do_eq_def,
           ml_monadBaseTheory.st_ex_bind_def,
           ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_compute_eval_suc_sub_one:
  compute_eval clock ceqs
      (Binop Sub (Num (SUC n)) (Num 1)) (refs:hol_refs) =
    (M_success (from_cv (Num n)),refs)
Proof
  simp [compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_hist_splice_aux_eval:
  !splice_count program clock refs.
    splice_count + 8 <=
        registered_case10173_cv_list_length program /\
    splice_count + 3 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_splice_aux»
          [from_cv (Num splice_count);from_cv program])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (registered_case10173_tag10_hist_splice_cv splice_count program)),refs)
Proof
  Induct_on `splice_count`
  >- (rpt gen_tac
      >> strip_tac
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_tag10_ceqs
              (subst
                [(«splice_count»,from_cv (Num 0));
                 («program»,from_cv program)]
                registered_case10173_tag10_hist_splice_aux_body) refs`
      >> conj_tac
      >- (irule registered_case10173_tag10_hist_splice_aux_unfold
          >> intLib.ARITH_TAC)
      >> rw
           [registered_case10173_tag10_hist_splice_aux_subst,
            compute_registeredCase10173Tag10GenuineProgramMemoEvalTheory.registered_case10173_tag10_hist_splice_cv_def,
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_num,
            registered_case10173_tag10_compute_eval_if_num_eq_zero]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`left_result` |-> `Num 10`,
                `right_result` |->
                  `registered_case10173_cv_drop 8 program`]
               compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
      >> conj_tac
      >- simp [compute_evalTheory.compute_eval_def,
               ml_monadBaseTheory.st_ex_return_def]
      >> irule registered_case10173_tag10_hist_drop_eight_eval
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> strip_tac
  >> Cases_on `program`
  >- fs
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> rename1 `Pair instruction rest`
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_tag10_ceqs
          (subst
            [(«splice_count»,from_cv (Num (SUC splice_count)));
             («program»,from_cv (Pair instruction rest))]
            registered_case10173_tag10_hist_splice_aux_body) refs`
  >> conj_tac
  >- (irule registered_case10173_tag10_hist_splice_aux_unfold
      >> intLib.ARITH_TAC)
  >> rw
       [registered_case10173_tag10_hist_splice_aux_subst,
        compute_registeredCase10173Tag10GenuineProgramMemoEvalTheory.registered_case10173_tag10_hist_splice_cv_def,
        compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_num,
        registered_case10173_tag10_compute_eval_if_num_eq_zero,
        compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac
  >- simp
       [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_tag10_ceqs
          (App «candle_cv_case10173_hist_splice_aux»
            [from_cv (Num splice_count);from_cv rest]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp [registered_case10173_tag10_compute_eval_suc_sub_one]
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> qpat_x_assum `!program clock refs. _`
       (qspecl_then [`rest`,`clock - 1`,`refs`] mp_tac)
  >> impl_tac
  >- (conj_tac
      >- fs
           [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
      >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem registered_case10173_tag10_prepared_program_splice_eval:
  registered_case10173_cv_list_length program = 54 /\
  34 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_splice_aux»
        [Num 31;from_cv program]) (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_tag10_hist_splice_cv 31 program)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.SPECL [`31`,`program`,`clock`,`refs`]
           registered_case10173_tag10_hist_splice_aux_eval))
  >> simp []
QED

val _ = export_theory ();
