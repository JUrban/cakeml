(*****************************************************************************
 * Exact current-source evaluator bridge for normalized object-q Taylor
 * arithmetic.  Normalization results are related by rational value rather
 * than by a particular GCD-reduced cv representation.
 *****************************************************************************)
Theory compute_boundedPackedSourceTaylorArithmeticEval
Ancestors
  compute_boundedPackedSourceRoundingEval
  compute_boundedPackedSourceEntrySuffixCongruence
  compute_boundedQFoldRelation
Libs
  bossLib preamble intLib

Definition bounded_packed_source_gcd_resume_exp_def:
  bounded_packed_source_gcd_resume_exp 0 argument = argument /\
  bounded_packed_source_gcd_resume_exp (SUC count) argument =
    App «candle_cv_num_gcd_state_resume»
      [bounded_packed_source_gcd_resume_exp count argument]
End

Definition bounded_packed_source_gcd_resume_n_def:
  bounded_packed_source_gcd_resume_n 0 (pair_state:num#num) = pair_state /\
  bounded_packed_source_gcd_resume_n (SUC count)
      (pair_state:num#num) =
    bounded_case10173_gcd_resume_state
      (bounded_packed_source_gcd_resume_n count pair_state)
End

Definition bounded_packed_source_gcd_pair_cv_def:
  bounded_packed_source_gcd_pair_cv (pair_state:num#num) =
    Pair (Num (FST pair_state)) (Num (SND pair_state))
End

Definition bounded_packed_source_num_gcd_extended_body_def:
  bounded_packed_source_num_gcd_extended_body =
    App «candle_cv_num_gcd_state_finish»
      [bounded_packed_source_gcd_resume_exp 7
        (App «candle_cv_num_gcd_state_chunk»
          [Var «a»;Var «b»])]
End

Theorem bounded_packed_source_num_gcd_extended_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_num_gcd_extended» =
    SOME ([«a»;«b»],bounded_packed_source_num_gcd_extended_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_gcd_resume_exp_eval:
  !n argument clock refs pair_state.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        argument (refs:hol_refs) =
      (M_success
        (from_cv (bounded_packed_source_gcd_pair_cv pair_state)),refs) /\
    132 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (bounded_packed_source_gcd_resume_exp n argument) refs =
      (M_success
        (from_cv
          (bounded_packed_source_gcd_pair_cv
            (bounded_packed_source_gcd_resume_n n pair_state))),refs)
Proof
  Induct_on `n`
  >- simp
       [bounded_packed_source_gcd_resume_exp_def,
        bounded_packed_source_gcd_resume_n_def]
  >> rpt gen_tac
  >> strip_tac
  >> simp
       [bounded_packed_source_gcd_resume_exp_def,
        bounded_packed_source_gcd_resume_n_def]
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (bounded_packed_source_gcd_resume_exp n argument) refs =
      (M_success
        (from_cv
          (bounded_packed_source_gcd_pair_cv
            (bounded_packed_source_gcd_resume_n n pair_state))),refs)` by
       (first_x_assum match_mp_tac
        >> asm_rewrite_tac [])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_num_gcd_state_resume»
            [from_cv
              (bounded_packed_source_gcd_pair_cv
                (bounded_packed_source_gcd_resume_n n pair_state))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> mp_tac
       (Q.INST
         [`left` |->
            `FST (bounded_packed_source_gcd_resume_n n pair_state)`,
          `right` |->
            `SND (bounded_packed_source_gcd_resume_n n pair_state)`,
          `clock` |-> `clock`,
          `refs` |-> `refs`]
         compute_registeredCase10173GcdEvalTheory.registered_case10173_num_gcd_state_resume_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> simp
       [bounded_packed_source_gcd_pair_cv_def,
        compute_registeredCase10173GcdEvalTheory.bounded_case10173_gcd_resume_cv_def,
        pairTheory.PAIR]
QED

Theorem bounded_packed_source_num_gcd_extended_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_extended»
        [from_cv (Num a);from_cv (Num b)]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«a»,from_cv (Num a));(«b»,from_cv (Num b))]
        bounded_packed_source_num_gcd_extended_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [bounded_packed_source_num_gcd_extended_lookup]
QED

Theorem bounded_packed_source_gcd_finish_exp_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument (refs:hol_refs) =
    (M_success
      (from_cv (bounded_packed_source_gcd_pair_cv pair_state)),refs) /\
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_state_finish» [argument]) refs =
    (M_success
      (from_cv
        (Num
          (bounded_case10173_gcd_finish
            (FST pair_state) (SND pair_state)))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_num_gcd_state_finish»
            [from_cv (bounded_packed_source_gcd_pair_cv pair_state)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> simp [bounded_packed_source_gcd_pair_cv_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173GcdEvalTheory.registered_case10173_num_gcd_state_finish_eval)
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_gcd_chunk_eval:
  130 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_state_chunk»
        [from_cv (Num a);from_cv (Num b)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_source_gcd_pair_cv
          (bounded_case10173_gcd_state 128 a b))),refs)
Proof
  strip_tac
  >> simp [bounded_packed_source_gcd_pair_cv_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_execTheory.from_cv_def,
          compute_registeredCase10173GcdEvalTheory.bounded_case10173_gcd_state_cv_def]
         compute_registeredCase10173GcdEvalTheory.registered_case10173_num_gcd_state_chunk_eval)
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_gcd_resume_exp_subst:
  !n environment argument.
    subst environment
      (bounded_packed_source_gcd_resume_exp n argument) =
    bounded_packed_source_gcd_resume_exp n
      (subst environment argument)
Proof
  Induct
  >> simp
       [bounded_packed_source_gcd_resume_exp_def,
        compute_evalTheory.subst_def]
QED

Theorem bounded_packed_source_num_gcd_extended_body_subst:
  subst [(«a»,from_cv (Num a));(«b»,from_cv (Num b))]
      bounded_packed_source_num_gcd_extended_body =
    App «candle_cv_num_gcd_state_finish»
      [bounded_packed_source_gcd_resume_exp 7
        (App «candle_cv_num_gcd_state_chunk»
          [from_cv (Num a);from_cv (Num b)])]
Proof
  simp
    [bounded_packed_source_num_gcd_extended_body_def,
     bounded_packed_source_gcd_resume_exp_subst,
     compute_evalTheory.subst_def]
QED

Theorem bounded_packed_source_gcd_resume7_chunk_eval:
  132 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (bounded_packed_source_gcd_resume_exp 7
        (App «candle_cv_num_gcd_state_chunk»
          [from_cv (Num a);from_cv (Num b)])) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_source_gcd_pair_cv
          (bounded_packed_source_gcd_resume_n 7
            (bounded_case10173_gcd_state 128 a b)))),refs)
Proof
  strip_tac
  >> irule bounded_packed_source_gcd_resume_exp_eval
  >> (conj_tac THENL
        [intLib.ARITH_TAC,
         irule bounded_packed_source_gcd_chunk_eval
         >> intLib.ARITH_TAC])
QED

Theorem bounded_packed_source_num_gcd_extended_body_eval:
  132 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_state_finish»
        [bounded_packed_source_gcd_resume_exp 7
          (App «candle_cv_num_gcd_state_chunk»
            [from_cv (Num a);from_cv (Num b)])]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Num
          (bounded_case10173_gcd_finish
            (FST
              (bounded_packed_source_gcd_resume_n 7
                (bounded_case10173_gcd_state 128 a b)))
            (SND
              (bounded_packed_source_gcd_resume_n 7
                (bounded_case10173_gcd_state 128 a b)))))),refs)
Proof
  strip_tac
  >> irule bounded_packed_source_gcd_finish_exp_eval
  >> (conj_tac THENL
        [intLib.ARITH_TAC,
         irule bounded_packed_source_gcd_resume7_chunk_eval
         >> intLib.ARITH_TAC])
QED

Theorem bounded_packed_source_num_gcd_extended_historical_eval:
  135 < clock ==>
  ?common.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_extended»
        [from_cv (Num a);from_cv (Num b)]) (refs:hol_refs) =
      (M_success (from_cv (Num common)),refs)
Proof
  strip_tac
  >> qexists_tac
       `bounded_case10173_gcd_finish
          (FST
            (bounded_packed_source_gcd_resume_n 7
              (bounded_case10173_gcd_state 128 a b)))
          (SND
            (bounded_packed_source_gcd_resume_n 7
              (bounded_case10173_gcd_state 128 a b)))`
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 1`,`a` |-> `a`,`b` |-> `b`,
          `refs` |-> `refs`]
         bounded_packed_source_num_gcd_extended_body_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock`,`a` |-> `a`,`b` |-> `b`,
          `refs` |-> `refs`]
         bounded_packed_source_num_gcd_extended_unfold)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> asm_rewrite_tac
       [bounded_packed_source_num_gcd_extended_body_subst]
QED

Definition bounded_packed_source_q_normalize_signed_extended_body_def:
  bounded_packed_source_q_normalize_signed_extended_body =
    App «candle_cv_q_normalize_verified»
      [Var «z»;Var «denominator»;
       App «candle_cv_num_gcd_extended»
         [Binop Add (Uop Fst (Var «z»)) (Uop Snd (Var «z»));
          Var «denominator»]]
End

Definition bounded_packed_source_q_normalize_extended_body_def:
  bounded_packed_source_q_normalize_extended_body =
    App «candle_cv_q_normalize_signed_extended»
      [App «candle_cv_lc_znormalize» [Uop Fst (Var «q»)];
       App «candle_cv_q_den» [Var «q»]]
End

Theorem bounded_packed_source_q_normalize_extended_lookups:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_normalize_signed_extended» =
    SOME
      ([«z»;«denominator»],
       bounded_packed_source_q_normalize_signed_extended_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_normalize_extended» =
    SOME ([«q»],bounded_packed_source_q_normalize_extended_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_q_normalize_signed_extended_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_signed_extended»
        [from_cv encoded_z;from_cv encoded_denominator])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«z»,from_cv encoded_z);
         («denominator»,from_cv encoded_denominator)]
        bounded_packed_source_q_normalize_signed_extended_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [bounded_packed_source_q_normalize_extended_lookups]
QED

Theorem bounded_packed_source_q_normalize_extended_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_extended» [from_cv encoded_q])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«q»,from_cv encoded_q)]
        bounded_packed_source_q_normalize_extended_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [bounded_packed_source_q_normalize_extended_lookups]
QED

Theorem bounded_packed_source_q_normalize_signed_extended_from_gcd_eval:
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_extended»
        [Binop Add
           (Uop Fst (from_cv (Pair (Num positive) (Num negative))))
           (Uop Snd (from_cv (Pair (Num positive) (Num negative))));
         from_cv (Num denominator)]) (refs:hol_refs) =
    (M_success (from_cv (Num common)),refs) /\
  0 < denominator /\ 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_signed_extended»
        [from_cv (Pair (Num positive) (Num negative));
         from_cv (Num denominator)]) refs =
    (M_success
      (from_cv
        (bounded_case10173_q_normalize_verified_cv
          positive negative denominator common)),refs)
Proof
  strip_tac
  >> simp
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`encoded_z` |-> `(Pair (Num positive) (Num negative):cv)`,
             `encoded_denominator` |-> `(Num denominator:cv)`]
            bounded_packed_source_q_normalize_signed_extended_unfold))]
  >> simp
       [bounded_packed_source_q_normalize_signed_extended_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_normalize_verified»
            [from_cv (Pair (Num positive) (Num negative));
             from_cv (Num denominator);from_cv (Num common)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
      >> conj_tac >- fs []
      >> conj_tac
      >- simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> conj_tac
      >- simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> fs [compute_execTheory.from_cv_def])
  >> simp
       [compute_registeredCase10173QNormalizeRelationEvalTheory.registered_case10173_q_normalize_verified_eval]
QED

Theorem bounded_packed_source_q_normalize_signed_extended_relation_from_gcd_eval:
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_extended»
        [Binop Add
           (Uop Fst (from_cv (Pair (Num positive) (Num negative))))
           (Uop Snd (from_cv (Pair (Num positive) (Num negative))));
         from_cv (Num denominator)]) (refs:hol_refs) =
    (M_success (from_cv (Num common)),refs) /\
  0 < denominator /\ 4 < clock ==>
  ?normalized.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_normalize_signed_extended»
          [from_cv (Pair (Num positive) (Num negative));
           from_cv (Num denominator)]) refs =
      (M_success (from_cv normalized),refs) /\
    bounded_case10173_q_cv_equiv normalized
      (Pair (Pair (Num positive) (Num negative))
        (Num (denominator - 1)))
Proof
  strip_tac
  >> qexists_tac
       `bounded_case10173_q_normalize_verified_cv
          positive negative denominator common`
  >> conj_tac
  >- (irule bounded_packed_source_q_normalize_signed_extended_from_gcd_eval
      >> asm_rewrite_tac [])
  >> irule
       compute_boundedQNormalizeRelationTheory.bounded_case10173_q_normalize_verified_cv_equiv
  >> first_assum ACCEPT_TAC
QED

Theorem bounded_packed_source_q_signed_sum_eval:
  1 < clock ==>
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (Binop Add
        (Uop Fst (from_cv (Pair (Num positive) (Num negative))))
        (Uop Snd (from_cv (Pair (Num positive) (Num negative)))))
      (refs:hol_refs) =
    (M_success (from_cv (Num (positive + negative))),refs)
Proof
  strip_tac
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_q_signed_gcd_argument_eval:
  140 < clock ==>
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_extended»
        [Binop Add
           (Uop Fst (from_cv (Pair (Num positive) (Num negative))))
           (Uop Snd (from_cv (Pair (Num positive) (Num negative))));
         from_cv (Num denominator)]) (refs:hol_refs) =
    compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_extended»
        [from_cv (Num (positive + negative));
         from_cv (Num denominator)]) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_packed_source_q_signed_sum_eval
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_q_normalize_signed_extended_relation_eval:
  0 < denominator /\ 140 < clock ==>
  ?normalized.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_normalize_signed_extended»
          [from_cv (Pair (Num positive) (Num negative));
           from_cv (Num denominator)]) (refs:hol_refs) =
      (M_success (from_cv normalized),refs) /\
    bounded_case10173_q_cv_equiv normalized
      (Pair (Pair (Num positive) (Num negative))
        (Num (denominator - 1)))
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock`,`positive` |-> `positive`,
          `negative` |-> `negative`,`denominator` |-> `denominator`,
          `refs` |-> `refs`]
         bounded_packed_source_q_signed_gcd_argument_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 1`,`a` |-> `positive + negative`,
          `b` |-> `denominator`,`refs` |-> `refs`]
         bounded_packed_source_num_gcd_extended_historical_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> `4 < clock` by intLib.ARITH_TAC
  >> irule
       bounded_packed_source_q_normalize_signed_extended_relation_from_gcd_eval
  >> asm_rewrite_tac []
  >> qexists_tac `common`
  >> simp []
QED

Theorem bounded_packed_source_q_normalize_extended_relation_eval:
  0 < denominator /\ 145 < clock ==>
  ?normalized.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_normalize_extended»
          [from_cv
            (Pair (Pair (Num positive) (Num negative))
              (Num (denominator - 1)))]) (refs:hol_refs) =
      (M_success (from_cv normalized),refs) /\
    bounded_case10173_q_cv_equiv normalized
      (Pair (Pair (Num positive) (Num negative))
        (Num (denominator - 1)))
Proof
  strip_tac
  >> `?lc_positive lc_negative.
        bounded_case10173_lc_znormalize_cv positive negative =
          Pair (Num lc_positive) (Num lc_negative)` by
       (Cases_on `positive < negative`
        >- (qexists_tac `0`
            >> qexists_tac `negative - positive`
            >> simp
                 [compute_boundedQNormalizeRelationTheory.bounded_case10173_lc_znormalize_cv_def])
        >> qexists_tac `positive - negative`
        >> qexists_tac `0`
        >> simp
             [compute_boundedQNormalizeRelationTheory.bounded_case10173_lc_znormalize_cv_def])
  >> mp_tac
       (Q.INST
         [`positive` |-> `lc_positive`,
          `negative` |-> `lc_negative`,
          `denominator` |-> `denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         bounded_packed_source_q_normalize_signed_extended_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qexists_tac `normalized`
  >> conj_tac
  >- (simp [bounded_packed_source_q_normalize_extended_unfold]
      >> simp
           [bounded_packed_source_q_normalize_extended_body_def,
            compute_evalTheory.subst_def,
            compute_execProofTheory.subst_from_cv]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_q_normalize_signed_extended»
                [from_cv (Pair (Num lc_positive) (Num lc_negative));
                 from_cv (Num denominator)]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> conj_tac
          >- (irule EQ_TRANS
              >> qexists_tac
                   `compute_eval (clock - 1)
                      registered_case10173_historical_chunk16_ceqs
                      (App «candle_cv_lc_znormalize»
                        [Pair (Num positive) (Num negative)]) refs`
              >> conj_tac
              >- (irule
                    (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                      (Q.INST
                        [`clock` |-> `clock - 1`,
                         `ceqs` |->
                           `registered_case10173_historical_chunk16_ceqs`,
                         `argument` |->
                           `Uop Fst
                             (Pair (Pair (Num positive) (Num negative))
                               (Num (denominator - 1)))`,
                         `argument_result` |->
                           `Pair (Num positive) (Num negative)`,
                         `function_name` |->
                           `«candle_cv_lc_znormalize»`,
                         `refs` |-> `refs`]
                        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result))
                  >> conj_tac >- intLib.ARITH_TAC
                  >> simp
                       [compute_evalTheory.compute_eval_def,
                        compute_evalTheory.do_uop_def,
                        compute_evalTheory.do_fst_def,
                        ml_monadBaseTheory.st_ex_bind_def,
                        ml_monadBaseTheory.st_ex_return_def])
              >> mp_tac
                   (Q.INST
                     [`clock` |-> `clock - 1`,
                      `positive` |-> `positive`,
                      `negative` |-> `negative`,
                      `refs` |-> `refs`]
                     compute_registeredCase10173QNormalizeRelationEvalTheory.registered_case10173_lc_znormalize_eval)
              >> impl_tac >- intLib.ARITH_TAC
              >> simp [compute_execTheory.from_cv_def]
              >> PURE_ASM_REWRITE_TAC [])
          >> mp_tac
               (Q.INST
                 [`clock` |-> `clock - 1`,
                  `numerator` |->
                    `Pair (Num positive) (Num negative)`,
                  `denominator_minus_one` |-> `denominator - 1`,
                  `refs` |-> `refs`]
                 compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_positive_eval)
          >> impl_tac >- intLib.ARITH_TAC
          >> simp [compute_execTheory.from_cv_def]
          >> PURE_ASM_REWRITE_TAC [])
      >> PURE_ASM_REWRITE_TAC []
      >> simp [])
  >> irule
       compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
  >> qexists_tac
       `Pair (Pair (Num lc_positive) (Num lc_negative))
          (Num (denominator - 1))`
  >> conj_tac >- PURE_ASM_REWRITE_TAC []
  >> mp_tac
       (Q.INST
         [`positive` |-> `positive`,
          `negative` |-> `negative`,
          `denominator` |-> `denominator`]
         compute_boundedQNormalizeRelationTheory.bounded_case10173_lc_znormalize_cv_equiv)
  >> impl_tac >- intLib.ARITH_TAC
  >> PURE_ASM_REWRITE_TAC []
  >> simp []
QED

Theorem bounded_packed_source_q_normalize_extended_expression_uses_shared_core:
  compute_exp_uses_only bounded_packed_source_shared_core
    (App «candle_cv_q_normalize_extended» [from_cv encoded_q])
Proof
  simp
    [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
     compute_evalRestrictedCongruenceTheory.cexp_value_compute_exp_uses_only,
     compute_execProofTheory.cexp_value_from_cv,
     compute_boundedPackedSourceSharedCoreTheory.bounded_packed_source_shared_core_def]
QED

Theorem bounded_packed_source_q_normalize_extended_current_relation_eval:
  0 < denominator /\ 145 < clock ==>
  ?normalized.
    compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_normalize_extended»
          [from_cv
            (Pair (Pair (Num positive) (Num negative))
              (Num (denominator - 1)))]) (refs:hol_refs) =
      (M_success (from_cv normalized),refs) /\
    bounded_case10173_q_cv_equiv normalized
      (Pair (Pair (Num positive) (Num negative))
        (Num (denominator - 1)))
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`positive` |-> `positive`,
          `negative` |-> `negative`,
          `denominator` |-> `denominator`,
          `clock` |-> `clock`,
          `refs` |-> `refs`]
         bounded_packed_source_q_normalize_extended_relation_eval)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_normalize_extended»
          [from_cv
            (Pair (Pair (Num positive) (Num negative))
              (Num (denominator - 1)))]) refs =
      compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_normalize_extended»
          [from_cv
            (Pair (Pair (Num positive) (Num negative))
              (Num (denominator - 1)))]) refs` by
       (irule
          compute_boundedPackedSourceSharedCoreCongruenceTheory.bounded_packed_source_shared_core_eval_cong
        >> simp
             [bounded_packed_source_q_normalize_extended_expression_uses_shared_core])
  >> qexists_tac `normalized`
  >> conj_tac
  >- metis_tac []
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_add_expression_uses_suffix:
  compute_exp_uses_only bounded_packed_source_entry_suffix_reachable
    (App «candle_cv_q_add» [from_cv left;from_cv right])
Proof
  simp
    [compute_boundedPackedSourceEntrySuffixCongruenceTheory.bounded_packed_source_entry_suffix_reachable_def,
     compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
     compute_evalRestrictedCongruenceTheory.cexp_value_compute_exp_uses_only,
     compute_execProofTheory.cexp_value_from_cv,
     compute_boundedPackedObjectEntryDataTheory.bounded_packed_object_entry_ceqs_def]
QED

Theorem bounded_packed_source_q_mul_expression_uses_suffix:
  compute_exp_uses_only bounded_packed_source_entry_suffix_reachable
    (App «candle_cv_q_mul» [from_cv left;from_cv right])
Proof
  simp
    [compute_boundedPackedSourceEntrySuffixCongruenceTheory.bounded_packed_source_entry_suffix_reachable_def,
     compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
     compute_evalRestrictedCongruenceTheory.cexp_value_compute_exp_uses_only,
     compute_execProofTheory.cexp_value_from_cv,
     compute_boundedPackedObjectEntryDataTheory.bounded_packed_object_entry_ceqs_def]
QED

Theorem bounded_packed_source_q_add_current_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_add_cv left right)),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`left` |-> `left`,`right` |-> `right`,
          `clock` |-> `clock`,`refs` |-> `refs`]
         compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_add_eval)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> once_rewrite_tac
       [GSYM
          (MATCH_MP
            compute_boundedPackedSourceEntrySuffixCongruenceTheory.bounded_packed_source_entry_suffix_eval_cong
            bounded_packed_source_q_add_expression_uses_suffix)]
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_mul_current_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_mul» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_mul_cv left right)),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`left` |-> `left`,`right` |-> `right`,
          `clock` |-> `clock`,`refs` |-> `refs`]
         compute_boundedPackedObjectPrimitiveMulEvalTheory.bounded_packed_q_mul_eval)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> once_rewrite_tac
       [GSYM
          (MATCH_MP
            compute_boundedPackedSourceEntrySuffixCongruenceTheory.bounded_packed_source_entry_suffix_eval_cong
            bounded_packed_source_q_mul_expression_uses_suffix)]
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_cv_equiv_left_encoded:
  bounded_case10173_q_cv_equiv left right ==>
  bounded_object_q_encoded left
Proof
  rw
    [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_packed_source_q_cv_equiv_right_encoded:
  bounded_case10173_q_cv_equiv left right ==>
  bounded_object_q_encoded right
Proof
  rw
    [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Definition bounded_packed_source_q_add_normalized_extended_body_def:
  bounded_packed_source_q_add_normalized_extended_body =
    App «candle_cv_q_normalize_extended»
      [App «candle_cv_q_add» [Var «x»;Var «y»]]
End

Definition bounded_packed_source_q_mul_normalized_extended_body_def:
  bounded_packed_source_q_mul_normalized_extended_body =
    App «candle_cv_q_normalize_extended»
      [App «candle_cv_q_mul» [Var «x»;Var «y»]]
End

Theorem bounded_packed_source_q_normalized_extended_lookups:
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_add_normalized_extended» =
    SOME ([«x»;«y»],bounded_packed_source_q_add_normalized_extended_body) /\
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_mul_normalized_extended» =
    SOME ([«x»;«y»],bounded_packed_source_q_mul_normalized_extended_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_q_add_normalized_extended_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_add_normalized_extended»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst [( «x»,from_cv left);(«y»,from_cv right)]
        bounded_packed_source_q_add_normalized_extended_body) refs
Proof
  strip_tac
  >> irule bounded_packed_source_compute_eval_literal_app2
  >> simp [bounded_packed_source_q_normalized_extended_lookups]
QED

Theorem bounded_packed_source_q_mul_normalized_extended_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_mul_normalized_extended»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst [(«x»,from_cv left);(«y»,from_cv right)]
        bounded_packed_source_q_mul_normalized_extended_body) refs
Proof
  strip_tac
  >> irule bounded_packed_source_compute_eval_literal_app2
  >> simp [bounded_packed_source_q_normalized_extended_lookups]
QED

Theorem bounded_packed_source_q_add_canonical_current_eval:
  3 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_add»
        [from_cv
          (Pair (Pair (Num left_positive) (Num left_negative))
            (Num left_denominator_minus_one));
         from_cv
          (Pair (Pair (Num right_positive) (Num right_negative))
            (Num right_denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_add_cv
          (Pair (Pair (Num left_positive) (Num left_negative))
            (Num left_denominator_minus_one))
          (Pair (Pair (Num right_positive) (Num right_negative))
            (Num right_denominator_minus_one)))),refs)
Proof
  strip_tac
  >> irule bounded_packed_source_q_add_current_eval
  >> simp
       [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_q_add_canonical_argument_eval:
  3 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_normalize_extended»
        [App «candle_cv_q_add»
          [from_cv
            (Pair (Pair (Num left_positive) (Num left_negative))
              (Num left_denominator_minus_one));
           from_cv
            (Pair (Pair (Num right_positive) (Num right_negative))
              (Num right_denominator_minus_one))]]) (refs:hol_refs) =
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_normalize_extended»
        [from_cv
          (bounded_object_q_add_cv
            (Pair (Pair (Num left_positive) (Num left_negative))
              (Num left_denominator_minus_one))
            (Pair (Pair (Num right_positive) (Num right_negative))
              (Num right_denominator_minus_one)))]) refs
Proof
  strip_tac
  >> irule bounded_packed_source_compute_eval_app1_argument_result
  >> conj_tac >- intLib.ARITH_TAC
  >> irule bounded_packed_source_q_add_canonical_current_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_q_add_normalized_extended_from_normalize_eval:
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_normalize_extended»
        [from_cv
          (bounded_object_q_add_cv
            (Pair (Pair (Num left_positive) (Num left_negative))
              (Num left_denominator_minus_one))
            (Pair (Pair (Num right_positive) (Num right_negative))
              (Num right_denominator_minus_one)))]) (refs:hol_refs) =
    (M_success (from_cv normalized),refs) /\
  150 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_add_normalized_extended»
        [from_cv
          (Pair (Pair (Num left_positive) (Num left_negative))
            (Num left_denominator_minus_one));
         from_cv
          (Pair (Pair (Num right_positive) (Num right_negative))
            (Num right_denominator_minus_one))]) refs =
    (M_success (from_cv normalized),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock`,
          `left` |->
            `Pair (Pair (Num left_positive) (Num left_negative))
              (Num left_denominator_minus_one)`,
          `right` |->
            `Pair (Pair (Num right_positive) (Num right_negative))
              (Num right_denominator_minus_one)`,
          `refs` |-> `refs`]
         bounded_packed_source_q_add_normalized_extended_unfold)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> mp_tac
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`clock` |-> `clock - 1`,`refs` |-> `refs`]
           bounded_packed_source_q_add_canonical_argument_eval))
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> simp
       [bounded_packed_source_q_add_normalized_extended_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_add_normalized_extended_canonical_relation_eval:
  150 < clock ==>
  ?normalized.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_add_normalized_extended»
          [from_cv
            (Pair (Pair (Num left_positive) (Num left_negative))
              (Num left_denominator_minus_one));
           from_cv
            (Pair (Pair (Num right_positive) (Num right_negative))
              (Num right_denominator_minus_one))]) (refs:hol_refs) =
      (M_success (from_cv normalized),refs) /\
    bounded_case10173_q_cv_equiv normalized
      (bounded_object_q_add_cv
        (Pair (Pair (Num left_positive) (Num left_negative))
          (Num left_denominator_minus_one))
        (Pair (Pair (Num right_positive) (Num right_negative))
          (Num right_denominator_minus_one)))
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`positive` |->
            `left_positive * SUC right_denominator_minus_one +
             right_positive * SUC left_denominator_minus_one`,
          `negative` |->
            `left_negative * SUC right_denominator_minus_one +
             right_negative * SUC left_denominator_minus_one`,
          `denominator` |->
            `SUC left_denominator_minus_one *
             SUC right_denominator_minus_one`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_normalize_extended_current_relation_eval)
  >> impl_tac
  >- (conj_tac >- simp []
      >> intLib.ARITH_TAC)
  >> strip_tac
  >> qexists_tac `normalized`
  >> conj_tac
  >- (irule
        bounded_packed_source_q_add_normalized_extended_from_normalize_eval
      >> asm_rewrite_tac
           [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_def])
  >> asm_rewrite_tac
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_def]
QED

Theorem bounded_packed_source_q_encoded_shape:
  bounded_object_q_encoded value ==>
  ?positive negative denominator_minus_one.
    value =
      Pair (Pair (Num positive) (Num negative))
        (Num denominator_minus_one)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> metis_tac []
QED

Theorem bounded_packed_source_q_add_normalized_extended_relation_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  150 < clock ==>
  ?normalized.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_add_normalized_extended»
          [from_cv left;from_cv right]) (refs:hol_refs) =
      (M_success (from_cv normalized),refs) /\
    bounded_case10173_q_cv_equiv normalized
      (bounded_object_q_add_cv left right)
Proof
  strip_tac
  >> metis_tac
       [bounded_packed_source_q_encoded_shape,
        bounded_packed_source_q_add_normalized_extended_canonical_relation_eval]
QED

Theorem bounded_packed_source_q_mul_canonical_current_eval:
  3 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_mul»
        [from_cv
          (Pair (Pair (Num left_positive) (Num left_negative))
            (Num left_denominator_minus_one));
         from_cv
          (Pair (Pair (Num right_positive) (Num right_negative))
            (Num right_denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_mul_cv
          (Pair (Pair (Num left_positive) (Num left_negative))
            (Num left_denominator_minus_one))
          (Pair (Pair (Num right_positive) (Num right_negative))
            (Num right_denominator_minus_one)))),refs)
Proof
  strip_tac
  >> irule bounded_packed_source_q_mul_current_eval
  >> simp
       [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_q_mul_canonical_argument_eval:
  3 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_normalize_extended»
        [App «candle_cv_q_mul»
          [from_cv
            (Pair (Pair (Num left_positive) (Num left_negative))
              (Num left_denominator_minus_one));
           from_cv
            (Pair (Pair (Num right_positive) (Num right_negative))
              (Num right_denominator_minus_one))]]) (refs:hol_refs) =
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_normalize_extended»
        [from_cv
          (bounded_object_q_mul_cv
            (Pair (Pair (Num left_positive) (Num left_negative))
              (Num left_denominator_minus_one))
            (Pair (Pair (Num right_positive) (Num right_negative))
              (Num right_denominator_minus_one)))]) refs
Proof
  strip_tac
  >> irule bounded_packed_source_compute_eval_app1_argument_result
  >> conj_tac >- intLib.ARITH_TAC
  >> irule bounded_packed_source_q_mul_canonical_current_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_q_mul_normalized_extended_from_normalize_eval:
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_normalize_extended»
        [from_cv
          (bounded_object_q_mul_cv
            (Pair (Pair (Num left_positive) (Num left_negative))
              (Num left_denominator_minus_one))
            (Pair (Pair (Num right_positive) (Num right_negative))
              (Num right_denominator_minus_one)))]) (refs:hol_refs) =
    (M_success (from_cv normalized),refs) /\
  150 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_mul_normalized_extended»
        [from_cv
          (Pair (Pair (Num left_positive) (Num left_negative))
            (Num left_denominator_minus_one));
         from_cv
          (Pair (Pair (Num right_positive) (Num right_negative))
            (Num right_denominator_minus_one))]) refs =
    (M_success (from_cv normalized),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock`,
          `left` |->
            `Pair (Pair (Num left_positive) (Num left_negative))
              (Num left_denominator_minus_one)`,
          `right` |->
            `Pair (Pair (Num right_positive) (Num right_negative))
              (Num right_denominator_minus_one)`,
          `refs` |-> `refs`]
         bounded_packed_source_q_mul_normalized_extended_unfold)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> mp_tac
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`clock` |-> `clock - 1`,`refs` |-> `refs`]
           bounded_packed_source_q_mul_canonical_argument_eval))
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> simp
       [bounded_packed_source_q_mul_normalized_extended_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_mul_normalized_extended_canonical_relation_eval:
  150 < clock ==>
  ?normalized.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_mul_normalized_extended»
          [from_cv
            (Pair (Pair (Num left_positive) (Num left_negative))
              (Num left_denominator_minus_one));
           from_cv
            (Pair (Pair (Num right_positive) (Num right_negative))
              (Num right_denominator_minus_one))]) (refs:hol_refs) =
      (M_success (from_cv normalized),refs) /\
    bounded_case10173_q_cv_equiv normalized
      (bounded_object_q_mul_cv
        (Pair (Pair (Num left_positive) (Num left_negative))
          (Num left_denominator_minus_one))
        (Pair (Pair (Num right_positive) (Num right_negative))
          (Num right_denominator_minus_one)))
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`positive` |->
            `left_positive * right_positive +
             left_negative * right_negative`,
          `negative` |->
            `left_positive * right_negative +
             left_negative * right_positive`,
          `denominator` |->
            `SUC left_denominator_minus_one *
             SUC right_denominator_minus_one`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_normalize_extended_current_relation_eval)
  >> impl_tac
  >- (conj_tac >- simp []
      >> intLib.ARITH_TAC)
  >> strip_tac
  >> qexists_tac `normalized`
  >> conj_tac
  >- (irule
        bounded_packed_source_q_mul_normalized_extended_from_normalize_eval
      >> asm_rewrite_tac
           [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_def])
  >> asm_rewrite_tac
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_def]
QED

Theorem bounded_packed_source_q_mul_normalized_extended_relation_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  150 < clock ==>
  ?normalized.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_mul_normalized_extended»
          [from_cv left;from_cv right]) (refs:hol_refs) =
      (M_success (from_cv normalized),refs) /\
    bounded_case10173_q_cv_equiv normalized
      (bounded_object_q_mul_cv left right)
Proof
  strip_tac
  >> metis_tac
       [bounded_packed_source_q_encoded_shape,
        bounded_packed_source_q_mul_normalized_extended_canonical_relation_eval]
QED

Theorem bounded_packed_source_q_abs_upper_expression_uses_suffix:
  compute_exp_uses_only bounded_packed_source_entry_suffix_reachable
    (App «candle_cv_q_abs_upper» [from_cv object_interval])
Proof
  simp
    [compute_boundedPackedSourceEntrySuffixCongruenceTheory.bounded_packed_source_entry_suffix_reachable_def,
     compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
     compute_evalRestrictedCongruenceTheory.cexp_value_compute_exp_uses_only,
     compute_execProofTheory.cexp_value_from_cv,
     compute_boundedPackedObjectEntryDataTheory.bounded_packed_object_entry_ceqs_def]
QED

Theorem bounded_packed_source_q_zero_expression_uses_suffix:
  compute_exp_uses_only bounded_packed_source_entry_suffix_reachable
    (App «candle_cv_q_zero» [])
Proof
  simp
    [compute_boundedPackedSourceEntrySuffixCongruenceTheory.bounded_packed_source_entry_suffix_reachable_def,
     compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
     compute_boundedPackedObjectEntryDataTheory.bounded_packed_object_entry_ceqs_def]
QED

Theorem bounded_packed_source_q_abs_upper_current_eval:
  bounded_packed_q_interval_encoded object_interval /\
  6 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_abs_upper» [from_cv object_interval])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_packed_q_source_abs_upper_cv object_interval)),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`object_interval` |-> `object_interval`,
          `clock` |-> `clock`,`refs` |-> `refs`]
         compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_source_abs_upper_eval)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> once_rewrite_tac
       [GSYM
          (MATCH_MP
            compute_boundedPackedSourceEntrySuffixCongruenceTheory.bounded_packed_source_entry_suffix_eval_cong
            bounded_packed_source_q_abs_upper_expression_uses_suffix)]
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_zero_current_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_zero» []) (refs:hol_refs) =
    (M_success (from_cv bounded_object_q_zero_cv),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock`,`refs` |-> `refs`]
         compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_zero_eval)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> once_rewrite_tac
       [GSYM
          (MATCH_MP
            compute_boundedPackedSourceEntrySuffixCongruenceTheory.bounded_packed_source_entry_suffix_eval_cong
            bounded_packed_source_q_zero_expression_uses_suffix)]
  >> asm_rewrite_tac []
QED

Definition bounded_packed_source_q_dot_abs_upper_extended_body_def:
  bounded_packed_source_q_dot_abs_upper_extended_body =
    If (Uop Ispair (Var «xs»))
      (If (Uop Ispair (Var «ys»))
        (App «candle_cv_q_add_normalized_extended»
          [App «candle_cv_q_mul_normalized_extended»
            [Uop Fst (Var «xs»);
             App «candle_cv_q_abs_upper» [Uop Fst (Var «ys»)]];
           App «candle_cv_q_dot_abs_upper_extended»
             [Uop Snd (Var «xs»);Uop Snd (Var «ys»)]])
        (App «candle_cv_q_zero» []))
      (App «candle_cv_q_zero» [])
End

Theorem bounded_packed_source_q_dot_abs_upper_extended_lookup:
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_dot_abs_upper_extended» =
    SOME ([«xs»;«ys»],bounded_packed_source_q_dot_abs_upper_extended_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_q_dot_abs_upper_extended_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dot_abs_upper_extended»
        [from_cv xs;from_cv ys]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst [(«xs»,from_cv xs);(«ys»,from_cv ys)]
        bounded_packed_source_q_dot_abs_upper_extended_body) refs
Proof
  strip_tac
  >> irule bounded_packed_source_compute_eval_literal_app2
  >> simp [bounded_packed_source_q_dot_abs_upper_extended_lookup]
QED

Theorem bounded_packed_source_q_dot_cons_structural_relation_eval:
  bounded_object_q_encoded radius /\
  bounded_packed_q_interval_encoded entry /\
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dot_abs_upper_extended»
        [from_cv tail_radii;from_cv tail_entries])
      (refs:hol_refs) =
    (M_success (from_cv tail_result),refs) /\
  bounded_case10173_q_cv_equiv tail_result tail_semantic /\
  150 < clock ==>
  ?result.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_add_normalized_extended»
          [App «candle_cv_q_mul_normalized_extended»
            [Uop Fst (Pair (from_cv radius) (from_cv tail_radii));
             App «candle_cv_q_abs_upper»
               [Uop Fst (Pair (from_cv entry) (from_cv tail_entries))]];
           App «candle_cv_q_dot_abs_upper_extended»
             [Uop Snd (Pair (from_cv radius) (from_cv tail_radii));
              Uop Snd (Pair (from_cv entry) (from_cv tail_entries))]])
        refs =
      (M_success (from_cv result),refs) /\
    bounded_case10173_q_cv_equiv result
      (bounded_object_q_add_cv
        (bounded_object_q_mul_cv radius
          (bounded_packed_q_source_abs_upper_cv entry))
        tail_semantic)
Proof
  strip_tac
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (Uop Fst (Pair (from_cv radius) (from_cv tail_radii))) refs =
      (M_success (from_cv radius),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_fst_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (Uop Fst (Pair (from_cv entry) (from_cv tail_entries))) refs =
      (M_success (from_cv entry),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_fst_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (Uop Snd (Pair (from_cv radius) (from_cv tail_radii))) refs =
      (M_success (from_cv tail_radii),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_snd_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (Uop Snd (Pair (from_cv entry) (from_cv tail_entries))) refs =
      (M_success (from_cv tail_entries),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_snd_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_abs_upper»
          [Uop Fst (Pair (from_cv entry) (from_cv tail_entries))]) refs =
      (M_success
        (from_cv (bounded_packed_q_source_abs_upper_cv entry)),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval clock
                bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                (App «candle_cv_q_abs_upper» [from_cv entry]) refs`
        >> conj_tac
        >- (irule bounded_packed_source_compute_eval_app1_argument_result
            >> asm_rewrite_tac []
            >> intLib.ARITH_TAC)
        >> irule bounded_packed_source_q_abs_upper_current_eval
        >> asm_rewrite_tac []
        >> intLib.ARITH_TAC)
  >> `bounded_object_q_encoded
        (bounded_packed_q_source_abs_upper_cv entry)` by
       (irule
          compute_boundedPackedObjectPrimitiveAbsContractTheory.bounded_packed_q_source_abs_upper_encoded
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`left` |-> `radius`,
          `right` |-> `bounded_packed_q_source_abs_upper_cv entry`,
          `clock` |-> `clock`,`refs` |-> `refs`]
         bounded_packed_source_q_mul_normalized_extended_relation_eval)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_mul_normalized_extended»
          [Uop Fst (Pair (from_cv radius) (from_cv tail_radii));
           App «candle_cv_q_abs_upper»
             [Uop Fst (Pair (from_cv entry) (from_cv tail_entries))]]) refs =
      (M_success (from_cv normalized),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval clock
                bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                (App «candle_cv_q_mul_normalized_extended»
                  [from_cv radius;
                   from_cv (bounded_packed_q_source_abs_upper_cv entry)]) refs`
        >> conj_tac
        >- (irule bounded_packed_source_compute_eval_app2_argument_results
            >> asm_rewrite_tac []
            >> intLib.ARITH_TAC)
        >> asm_rewrite_tac [])
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_dot_abs_upper_extended»
          [Uop Snd (Pair (from_cv radius) (from_cv tail_radii));
           Uop Snd (Pair (from_cv entry) (from_cv tail_entries))]) refs =
      (M_success (from_cv tail_result),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval clock
                bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                (App «candle_cv_q_dot_abs_upper_extended»
                  [from_cv tail_radii;from_cv tail_entries]) refs`
        >> conj_tac
        >- (irule bounded_packed_source_compute_eval_app2_argument_results
            >> asm_rewrite_tac []
            >> intLib.ARITH_TAC)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_encoded normalized` by
       metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
  >> `bounded_object_q_encoded tail_result` by
       metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
  >> mp_tac
       (Q.INST
         [`left` |-> `normalized`,`right` |-> `tail_result`,
          `clock` |-> `clock`,`refs` |-> `refs`]
         bounded_packed_source_q_add_normalized_extended_relation_eval)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> qexists_tac `normalized'`
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock
              bounded_case16594_packed_source_cell0_entry_v2173_ceqs
              (App «candle_cv_q_add_normalized_extended»
                [from_cv normalized;from_cv tail_result]) refs`
      >> conj_tac
      >- (irule bounded_packed_source_compute_eval_app2_argument_results
          >> asm_rewrite_tac []
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> irule
       compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
  >> qexists_tac
       `bounded_object_q_add_cv normalized tail_result`
  >> conj_tac >- asm_rewrite_tac []
  >> irule compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_dot_abs_upper_extended_relation_eval:
  !radii entries clock refs.
    EVERY bounded_object_q_encoded radii /\
    EVERY bounded_packed_q_interval_encoded entries /\
    160 * (LENGTH radii + 1) < clock ==>
    ?result.
      compute_eval clock
          bounded_case16594_packed_source_cell0_entry_v2173_ceqs
          (App «candle_cv_q_dot_abs_upper_extended»
            [from_cv (bounded_object_q_cv_list radii);
             from_cv (bounded_object_q_cv_list entries)])
          (refs:hol_refs) =
        (M_success (from_cv result),refs) /\
      bounded_case10173_q_cv_equiv result
        (bounded_packed_q_source_dot_abs_upper_cv radii entries)
Proof
  Induct_on `radii`
  >- (rw
        [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_cv_def]
      >> rw [bounded_packed_source_q_dot_abs_upper_extended_unfold]
      >> qexists_tac `bounded_object_q_zero_cv`
      >> conj_tac
      >- (simp
            [bounded_packed_source_q_dot_abs_upper_extended_body_def,
             compute_evalTheory.subst_def,
             compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
             compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_num]
          >> irule bounded_packed_source_q_zero_current_eval
          >> intLib.ARITH_TAC)
      >> irule
           compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl
      >> simp
           [compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded])
  >> Cases_on `entries`
  >- (rw
        [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_cv_def]
      >> rw [bounded_packed_source_q_dot_abs_upper_extended_unfold]
      >> qexists_tac `bounded_object_q_zero_cv`
      >> conj_tac
      >- (simp
            [bounded_packed_source_q_dot_abs_upper_extended_body_def,
             compute_evalTheory.subst_def,
             compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
             compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_num,
             compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair]
          >> irule bounded_packed_source_q_zero_current_eval
          >> intLib.ARITH_TAC)
      >> irule
           compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl
      >> simp
           [compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded])
  >> rw
       [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_cv_def]
  >> rw [bounded_packed_source_q_dot_abs_upper_extended_unfold]
  >> simp
       [bounded_packed_source_q_dot_abs_upper_extended_body_def,
        compute_evalTheory.subst_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair]
  >> qpat_x_assum `!entries clock refs. _`
       (qspecl_then [`t`,`clock - 1`,`refs`] mp_tac)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `tail_value` strip_assume_tac)
  >> irule
       (Q.INST
         [`radius` |-> `h`,
          `entry` |-> `h'`,
          `tail_radii` |-> `bounded_object_q_cv_list radii`,
          `tail_entries` |-> `bounded_object_q_cv_list t`,
          `tail_result` |-> `tail_value`,
          `tail_semantic` |->
            `bounded_packed_q_source_dot_abs_upper_cv radii t`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_dot_cons_structural_relation_eval)
  >> `150 < clock - 1` by intLib.ARITH_TAC
  >> asm_rewrite_tac []
  >> metis_tac []
QED

Definition bounded_packed_source_q_weighted_rows_abs_upper_cv_def:
  bounded_packed_source_q_weighted_rows_abs_upper_cv radii [] rows =
      bounded_object_q_zero_cv /\
  bounded_packed_source_q_weighted_rows_abs_upper_cv radii (_::_) [] =
      bounded_object_q_zero_cv /\
  bounded_packed_source_q_weighted_rows_abs_upper_cv radii
      (weight::weights) (row::rows) =
    bounded_object_q_add_cv
      (bounded_object_q_mul_cv weight
        (bounded_packed_q_source_dot_abs_upper_cv radii row))
      (bounded_packed_source_q_weighted_rows_abs_upper_cv
        radii weights rows)
End

Theorem bounded_packed_source_q_weighted_rows_abs_upper_encoded:
  !weights rows.
    EVERY bounded_object_q_encoded radii /\
    EVERY bounded_object_q_encoded weights /\
    EVERY (EVERY bounded_packed_q_interval_encoded) rows ==>
    bounded_object_q_encoded
      (bounded_packed_source_q_weighted_rows_abs_upper_cv
        radii weights rows)
Proof
  Induct_on `weights`
  >> Cases_on `rows`
  >> simp
       [bounded_packed_source_q_weighted_rows_abs_upper_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded]
  >> metis_tac
       [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded]
QED

Definition bounded_packed_source_q_weighted_rows_abs_upper_extended_body_def:
  bounded_packed_source_q_weighted_rows_abs_upper_extended_body =
    If (Uop Ispair (Var «weights»))
      (If (Uop Ispair (Var «row_lists»))
        (App «candle_cv_q_add_normalized_extended»
          [App «candle_cv_q_mul_normalized_extended»
            [Uop Fst (Var «weights»);
             App «candle_cv_q_dot_abs_upper_extended»
               [Var «radii»;Uop Fst (Var «row_lists»)]];
           App «candle_cv_q_weighted_rows_abs_upper_extended»
             [Var «radii»;Uop Snd (Var «weights»);
              Uop Snd (Var «row_lists»)]])
        (App «candle_cv_q_zero» []))
      (App «candle_cv_q_zero» [])
End

Theorem bounded_packed_source_q_weighted_rows_abs_upper_extended_lookup:
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_weighted_rows_abs_upper_extended» =
    SOME
      ([«radii»;«weights»;«row_lists»],
       bounded_packed_source_q_weighted_rows_abs_upper_extended_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_q_weighted_rows_abs_upper_extended_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_weighted_rows_abs_upper_extended»
        [from_cv radii;from_cv weights;from_cv rows])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst
        [(«radii»,from_cv radii);(«weights»,from_cv weights);
         («row_lists»,from_cv rows)]
        bounded_packed_source_q_weighted_rows_abs_upper_extended_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectErrorEvalTheory.bounded_packed_compute_eval_literal_app3
  >> simp
       [bounded_packed_source_q_weighted_rows_abs_upper_extended_lookup]
QED

Theorem bounded_packed_source_q_weighted_rows_cons_structural_relation_eval:
  bounded_object_q_encoded weight /\
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dot_abs_upper_extended»
        [from_cv radii;from_cv row]) (refs:hol_refs) =
    (M_success (from_cv row_result),refs) /\
  bounded_case10173_q_cv_equiv row_result row_semantic /\
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_weighted_rows_abs_upper_extended»
        [from_cv radii;from_cv tail_weights;from_cv tail_rows]) refs =
    (M_success (from_cv tail_result),refs) /\
  bounded_case10173_q_cv_equiv tail_result tail_semantic /\
  150 < clock ==>
  ?result.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_add_normalized_extended»
          [App «candle_cv_q_mul_normalized_extended»
            [Uop Fst (Pair (from_cv weight) (from_cv tail_weights));
             App «candle_cv_q_dot_abs_upper_extended»
               [from_cv radii;
                Uop Fst (Pair (from_cv row) (from_cv tail_rows))]];
           App «candle_cv_q_weighted_rows_abs_upper_extended»
             [from_cv radii;
              Uop Snd (Pair (from_cv weight) (from_cv tail_weights));
              Uop Snd (Pair (from_cv row) (from_cv tail_rows))]]) refs =
      (M_success (from_cv result),refs) /\
    bounded_case10173_q_cv_equiv result
      (bounded_object_q_add_cv
        (bounded_object_q_mul_cv weight row_semantic) tail_semantic)
Proof
  strip_tac
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (Uop Fst (Pair (from_cv weight) (from_cv tail_weights))) refs =
      (M_success (from_cv weight),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (Uop Fst (Pair (from_cv row) (from_cv tail_rows))) refs =
      (M_success (from_cv row),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (Uop Snd (Pair (from_cv weight) (from_cv tail_weights))) refs =
      (M_success (from_cv tail_weights),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (Uop Snd (Pair (from_cv row) (from_cv tail_rows))) refs =
      (M_success (from_cv tail_rows),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_dot_abs_upper_extended»
          [from_cv radii;
           Uop Fst (Pair (from_cv row) (from_cv tail_rows))]) refs =
      (M_success (from_cv row_result),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval clock
                bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                (App «candle_cv_q_dot_abs_upper_extended»
                  [from_cv radii;from_cv row]) refs`
        >> conj_tac
        >- (irule bounded_packed_source_compute_eval_app2_argument_results
            >> asm_rewrite_tac []
            >> simp
                 [compute_evalTheory.compute_eval_def,
                  compute_execProofTheory.compute_eval_from_cv,
                  ml_monadBaseTheory.st_ex_return_def]
            >> intLib.ARITH_TAC)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_encoded row_result` by
       metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
  >> mp_tac
       (Q.INST
         [`left` |-> `weight`,`right` |-> `row_result`,
          `clock` |-> `clock`,`refs` |-> `refs`]
         bounded_packed_source_q_mul_normalized_extended_relation_eval)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_mul_normalized_extended»
          [Uop Fst (Pair (from_cv weight) (from_cv tail_weights));
           App «candle_cv_q_dot_abs_upper_extended»
             [from_cv radii;
              Uop Fst (Pair (from_cv row) (from_cv tail_rows))]]) refs =
      (M_success (from_cv normalized),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval clock
                bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                (App «candle_cv_q_mul_normalized_extended»
                  [from_cv weight;from_cv row_result]) refs`
        >> conj_tac
        >- (irule bounded_packed_source_compute_eval_app2_argument_results
            >> asm_rewrite_tac []
            >> intLib.ARITH_TAC)
        >> asm_rewrite_tac [])
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_weighted_rows_abs_upper_extended»
          [from_cv radii;
           Uop Snd (Pair (from_cv weight) (from_cv tail_weights));
           Uop Snd (Pair (from_cv row) (from_cv tail_rows))]) refs =
      (M_success (from_cv tail_result),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval clock
                bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                (App «candle_cv_q_weighted_rows_abs_upper_extended»
                  [from_cv radii;from_cv tail_weights;
                   from_cv tail_rows]) refs`
        >> conj_tac
        >- (irule
              compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
            >> asm_rewrite_tac []
            >> simp
                 [compute_evalTheory.compute_eval_def,
                  compute_execProofTheory.compute_eval_from_cv,
                  ml_monadBaseTheory.st_ex_return_def]
            >> intLib.ARITH_TAC)
        >> asm_rewrite_tac [])
  >> `bounded_object_q_encoded normalized` by
       metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
  >> `bounded_object_q_encoded tail_result` by
       metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
  >> mp_tac
       (Q.INST
         [`left` |-> `normalized`,`right` |-> `tail_result`,
          `clock` |-> `clock`,`refs` |-> `refs`]
         bounded_packed_source_q_add_normalized_extended_relation_eval)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> qexists_tac `normalized'`
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock
              bounded_case16594_packed_source_cell0_entry_v2173_ceqs
              (App «candle_cv_q_add_normalized_extended»
                [from_cv normalized;from_cv tail_result]) refs`
      >> conj_tac
      >- (irule bounded_packed_source_compute_eval_app2_argument_results
          >> asm_rewrite_tac []
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> irule
       compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
  >> qexists_tac `bounded_object_q_add_cv normalized tail_result`
  >> conj_tac >- asm_rewrite_tac []
  >> irule compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong
  >> conj_tac
  >- (irule
        compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
      >> qexists_tac `bounded_object_q_mul_cv weight row_result`
      >> conj_tac >- asm_rewrite_tac []
      >> irule compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
      >> conj_tac
      >- (irule
            compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl
          >> asm_rewrite_tac [])
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_weighted_rows_abs_upper_extended_relation_eval:
  !weights rows radii clock refs.
    EVERY bounded_object_q_encoded radii /\
    EVERY bounded_object_q_encoded weights /\
    EVERY (EVERY bounded_packed_q_interval_encoded) rows /\
    170 * (LENGTH weights + 1) + 170 * (LENGTH radii + 1) < clock ==>
    ?result.
      compute_eval clock
          bounded_case16594_packed_source_cell0_entry_v2173_ceqs
          (App «candle_cv_q_weighted_rows_abs_upper_extended»
            [from_cv (bounded_object_q_cv_list radii);
             from_cv (bounded_object_q_cv_list weights);
             from_cv
               (bounded_object_q_cv_list
                 (MAP bounded_object_q_cv_list rows))])
          (refs:hol_refs) =
        (M_success (from_cv result),refs) /\
      bounded_case10173_q_cv_equiv result
        (bounded_packed_source_q_weighted_rows_abs_upper_cv
          radii weights rows)
Proof
  Induct_on `weights`
  >- (rw [bounded_packed_source_q_weighted_rows_abs_upper_cv_def]
      >> rw
           [bounded_packed_source_q_weighted_rows_abs_upper_extended_unfold]
      >> qexists_tac `bounded_object_q_zero_cv`
      >> conj_tac
      >- (simp
            [bounded_packed_source_q_weighted_rows_abs_upper_extended_body_def,
             compute_evalTheory.subst_def,
             compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
             compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_num]
          >> irule bounded_packed_source_q_zero_current_eval
          >> intLib.ARITH_TAC)
      >> irule
           compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl
      >> simp
           [compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded])
  >> Cases_on `rows`
  >- (rw [bounded_packed_source_q_weighted_rows_abs_upper_cv_def]
      >> rw
           [bounded_packed_source_q_weighted_rows_abs_upper_extended_unfold]
      >> qexists_tac `bounded_object_q_zero_cv`
      >> conj_tac
      >- (simp
            [bounded_packed_source_q_weighted_rows_abs_upper_extended_body_def,
             compute_evalTheory.subst_def,
             compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
             compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_num,
             compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair]
          >> irule bounded_packed_source_q_zero_current_eval
          >> intLib.ARITH_TAC)
      >> irule
           compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl
      >> simp
           [compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded])
  >> rw [bounded_packed_source_q_weighted_rows_abs_upper_cv_def]
  >> rw [bounded_packed_source_q_weighted_rows_abs_upper_extended_unfold]
  >> simp
       [bounded_packed_source_q_weighted_rows_abs_upper_extended_body_def,
        compute_evalTheory.subst_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair]
  >> `EVERY bounded_packed_q_interval_encoded h` by fs []
  >> `160 * (LENGTH radii + 1) < clock - 1` by intLib.ARITH_TAC
  >> `?row_value.
        compute_eval (clock - 1)
            bounded_case16594_packed_source_cell0_entry_v2173_ceqs
            (App «candle_cv_q_dot_abs_upper_extended»
              [from_cv (bounded_object_q_cv_list radii);
               from_cv (bounded_object_q_cv_list h)]) refs =
          (M_success (from_cv row_value),refs) /\
        bounded_case10173_q_cv_equiv row_value
          (bounded_packed_q_source_dot_abs_upper_cv radii h)` by
       (irule bounded_packed_source_q_dot_abs_upper_extended_relation_eval
        >> asm_rewrite_tac [])
  >> `?tail_value.
        compute_eval (clock - 1)
            bounded_case16594_packed_source_cell0_entry_v2173_ceqs
            (App «candle_cv_q_weighted_rows_abs_upper_extended»
              [from_cv (bounded_object_q_cv_list radii);
               from_cv (bounded_object_q_cv_list weights);
               from_cv
                 (bounded_object_q_cv_list
                   (MAP bounded_object_q_cv_list t))]) refs =
          (M_success (from_cv tail_value),refs) /\
        bounded_case10173_q_cv_equiv tail_value
          (bounded_packed_source_q_weighted_rows_abs_upper_cv
            radii weights t)` by
       (`170 * (LENGTH weights + 1) + 170 * (LENGTH radii + 1) <
          clock - 1` by intLib.ARITH_TAC
        >> metis_tac [])
  >> irule
       bounded_packed_source_q_weighted_rows_cons_structural_relation_eval
  >> `150 < clock - 1` by intLib.ARITH_TAC
  >> asm_rewrite_tac []
  >> metis_tac []
QED

Definition bounded_packed_source_q_taylor_model_error_cv_def:
  bounded_packed_source_q_taylor_model_error_cv radii gradient hessian =
    bounded_object_q_add_cv
      (bounded_packed_q_source_dot_abs_upper_cv radii gradient)
      (bounded_object_q_mul_cv
        (bounded_analytic_source_q_cv 1 0 1)
        (bounded_packed_source_q_weighted_rows_abs_upper_cv
          radii radii hessian))
End

Theorem bounded_packed_source_q_half_encoded:
  bounded_object_q_encoded (bounded_analytic_source_q_cv 1 0 1)
Proof
  simp
    [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_decodes]
QED

Theorem bounded_packed_source_q_taylor_model_error_encoded:
  EVERY bounded_object_q_encoded radii /\
  EVERY bounded_packed_q_interval_encoded gradient /\
  EVERY (EVERY bounded_packed_q_interval_encoded) hessian ==>
  bounded_object_q_encoded
    (bounded_packed_source_q_taylor_model_error_cv
      radii gradient hessian)
Proof
  strip_tac
  >> simp
       [bounded_packed_source_q_taylor_model_error_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded,
        compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_encoded,
        bounded_packed_source_q_weighted_rows_abs_upper_encoded]
QED

Definition bounded_packed_source_q_taylor_model_error_body_def:
  bounded_packed_source_q_taylor_model_error_body =
    App «candle_cv_q_add_normalized_extended»
      [App «candle_cv_q_dot_abs_upper_extended»
        [Var «radii»;
         App «candle_cv_q_dim_first_jet_gradient»
           [Var «center_first»]];
       App «candle_cv_q_mul_normalized_extended»
         [App «candle_cv_q_half» [];
          App «candle_cv_q_weighted_rows_abs_upper_extended»
            [Var «radii»;Var «radii»;Var «hessian»]]]
End

Theorem bounded_packed_source_q_taylor_model_error_lookup:
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_dim_taylor_model_error» =
    SOME
      ([«radii»;«center_first»;«hessian»],
       bounded_packed_source_q_taylor_model_error_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_q_taylor_model_error_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dim_taylor_model_error»
        [from_cv radii;from_cv center_first;from_cv hessian])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst
        [(«radii»,from_cv radii);(«center_first»,from_cv center_first);
         («hessian»,from_cv hessian)]
        bounded_packed_source_q_taylor_model_error_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectErrorEvalTheory.bounded_packed_compute_eval_literal_app3
  >> simp [bounded_packed_source_q_taylor_model_error_lookup]
QED

Theorem bounded_packed_source_q_half_expression_uses_suffix:
  compute_exp_uses_only bounded_packed_source_entry_suffix_reachable
    (App «candle_cv_q_half» [])
Proof
  simp
    [compute_boundedPackedSourceEntrySuffixCongruenceTheory.bounded_packed_source_entry_suffix_reachable_def,
     compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
     compute_boundedPackedObjectEntryDataTheory.bounded_packed_object_entry_ceqs_def]
QED

Theorem bounded_packed_source_q_half_current_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_half» []) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_analytic_source_q_cv 1 0 1)),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock`,`refs` |-> `refs`]
         compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_half_eval)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> once_rewrite_tac
       [GSYM
          (MATCH_MP
            compute_boundedPackedSourceEntrySuffixCongruenceTheory.bounded_packed_source_entry_suffix_eval_cong
            bounded_packed_source_q_half_expression_uses_suffix)]
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_taylor_model_error_relation_eval:
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded gradient /\
  EVERY (EVERY bounded_packed_q_interval_encoded) hessian /\
  500 * (LENGTH radii + 1) < clock ==>
  ?result.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_dim_taylor_model_error»
          [from_cv (bounded_object_q_cv_list radii);
           from_cv
             (Pair center_value (bounded_object_q_cv_list gradient));
           from_cv
             (bounded_object_q_cv_list
               (MAP bounded_object_q_cv_list hessian))])
        (refs:hol_refs) =
      (M_success (from_cv result),refs) /\
    bounded_case10173_q_cv_equiv result
      (bounded_packed_source_q_taylor_model_error_cv
        radii gradient hessian)
Proof
  strip_tac
  >> rw [bounded_packed_source_q_taylor_model_error_unfold]
  >> simp
       [bounded_packed_source_q_taylor_model_error_body_def,
        compute_evalTheory.subst_def]
  >> mp_tac
       (Q.SPECL [`radii`,`gradient`,`clock - 1`,`refs`]
         bounded_packed_source_q_dot_abs_upper_extended_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `linear_value` strip_assume_tac)
  >> `compute_eval (clock - 1)
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_dot_abs_upper_extended»
          [from_cv (bounded_object_q_cv_list radii);
           App «candle_cv_q_dim_first_jet_gradient»
             [Pair (from_cv center_value)
               (from_cv (bounded_object_q_cv_list gradient))]]) refs =
      (M_success (from_cv linear_value),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval (clock - 1)
                bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                (App «candle_cv_q_dot_abs_upper_extended»
                  [from_cv (bounded_object_q_cv_list radii);
                   from_cv (bounded_object_q_cv_list gradient)]) refs`
        >> conj_tac
        >- (irule bounded_packed_source_compute_eval_app2_argument_results
            >> conj_tac
            >- intLib.ARITH_TAC
            >> conj_tac
            >- simp [compute_execProofTheory.compute_eval_from_cv]
            >> `Pair (from_cv center_value)
                  (from_cv (bounded_object_q_cv_list gradient)) =
                from_cv
                  (Pair center_value
                    (bounded_object_q_cv_list gradient))` by
                 simp [compute_execTheory.from_cv_def]
            >> asm_rewrite_tac []
            >> irule bounded_packed_source_q_dim_first_jet_gradient_eval
            >> intLib.ARITH_TAC)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.SPECL
         [`radii`,`hessian`,`radii`,`clock - 1`,`refs`]
         bounded_packed_source_q_weighted_rows_abs_upper_extended_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `weighted_value` strip_assume_tac)
  >> `bounded_object_q_encoded linear_value` by
       metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
  >> `bounded_object_q_encoded weighted_value` by
       metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
  >> mp_tac
       (Q.INST
         [`left` |-> `bounded_analytic_source_q_cv 1 0 1`,
          `right` |-> `weighted_value`,`clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         bounded_packed_source_q_mul_normalized_extended_relation_eval)
  >> impl_tac
  >- (conj_tac
      >- (ACCEPT_TAC bounded_packed_source_q_half_encoded)
      >> conj_tac
      >- asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `quadratic_value` strip_assume_tac)
  >> `compute_eval (clock - 1)
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_mul_normalized_extended»
          [App «candle_cv_q_half» [];
           App «candle_cv_q_weighted_rows_abs_upper_extended»
             [from_cv (bounded_object_q_cv_list radii);
              from_cv (bounded_object_q_cv_list radii);
              from_cv
                (bounded_object_q_cv_list
                  (MAP bounded_object_q_cv_list hessian))]]) refs =
      (M_success (from_cv quadratic_value),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval (clock - 1)
                bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                (App «candle_cv_q_mul_normalized_extended»
                  [from_cv (bounded_analytic_source_q_cv 1 0 1);
                   from_cv weighted_value]) refs`
        >> conj_tac
        >- (irule bounded_packed_source_compute_eval_app2_argument_results
            >> conj_tac
            >- intLib.ARITH_TAC
            >> conj_tac
            >- (irule bounded_packed_source_q_half_current_eval
                >> intLib.ARITH_TAC)
            >> asm_rewrite_tac [])
        >> asm_rewrite_tac [])
  >> `bounded_case10173_q_cv_equiv quadratic_value
        (bounded_object_q_mul_cv
          (bounded_analytic_source_q_cv 1 0 1)
          (bounded_packed_source_q_weighted_rows_abs_upper_cv
            radii radii hessian))` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
        >> qexists_tac
             `bounded_object_q_mul_cv
                (bounded_analytic_source_q_cv 1 0 1) weighted_value`
        >> asm_rewrite_tac []
        >> irule
             compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
        >> asm_rewrite_tac []
        >> irule
             compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl
        >> (ACCEPT_TAC bounded_packed_source_q_half_encoded))
  >> `bounded_object_q_encoded quadratic_value` by
       metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
  >> mp_tac
       (Q.INST
         [`left` |-> `linear_value`,`right` |-> `quadratic_value`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_add_normalized_extended_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `result_value` strip_assume_tac)
  >> qexists_tac `result_value`
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_packed_source_cell0_entry_v2173_ceqs
              (App «candle_cv_q_add_normalized_extended»
                [from_cv linear_value;from_cv quadratic_value]) refs`
      >> conj_tac
      >- (irule bounded_packed_source_compute_eval_app2_argument_results
          >> asm_rewrite_tac []
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> rw [bounded_packed_source_q_taylor_model_error_cv_def]
  >> irule
       compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
  >> qexists_tac
       `bounded_object_q_add_cv linear_value quadratic_value`
  >> asm_rewrite_tac []
  >> irule compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_neg_encoded:
  bounded_object_q_encoded value ==>
  bounded_object_q_encoded (bounded_object_q_neg_cv value)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> qexists_tac `(-fraction0,fraction1)`
  >> irule
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_decodes
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_neg_cv_equiv_cong:
  bounded_case10173_q_cv_equiv left right ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_neg_cv left)
    (bounded_object_q_neg_cv right)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedQFoldRelationTheory.bounded_object_q_cv_equiv_decodes
  >> `bounded_object_q_ints (bounded_object_q_neg_cv left) =
        SOME (-left_numerator,left_denominator)` by
       metis_tac
         [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_decodes]
  >> `bounded_object_q_ints (bounded_object_q_neg_cv right) =
        SOME (-right_numerator,right_denominator)` by
       metis_tac
         [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_decodes]
  >> simp
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
        integerTheory.INT_MUL_LNEG]
QED

Definition bounded_packed_source_q_interval_cv_equiv_def:
  bounded_packed_source_q_interval_cv_equiv actual expected <=>
    ?actual_lower actual_upper expected_lower expected_upper.
      actual = Pair actual_lower actual_upper /\
      expected = Pair expected_lower expected_upper /\
      bounded_case10173_q_cv_equiv actual_lower expected_lower /\
      bounded_case10173_q_cv_equiv actual_upper expected_upper
End

Theorem bounded_packed_source_q_interval_cv_equiv_refl:
  !object_interval.
  bounded_packed_q_interval_encoded object_interval ==>
  bounded_packed_source_q_interval_cv_equiv
    object_interval object_interval
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def,
     bounded_packed_source_q_interval_cv_equiv_def]
  >> metis_tac
       [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl]
QED

Theorem bounded_packed_source_q_interval_cv_equiv_left_encoded:
  bounded_packed_source_q_interval_cv_equiv actual expected ==>
  bounded_packed_q_interval_encoded actual
Proof
  rw
    [bounded_packed_source_q_interval_cv_equiv_def,
     compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
QED

Theorem bounded_packed_source_q_interval_cv_equiv_right_encoded:
  bounded_packed_source_q_interval_cv_equiv actual expected ==>
  bounded_packed_q_interval_encoded expected
Proof
  rw
    [bounded_packed_source_q_interval_cv_equiv_def,
     compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> metis_tac [bounded_packed_source_q_cv_equiv_right_encoded]
QED

Definition bounded_packed_source_q_symmetric_interval_cv_def:
  bounded_packed_source_q_symmetric_interval_cv radius =
    Pair (bounded_object_q_neg_cv radius) radius
End

Theorem bounded_packed_source_q_symmetric_interval_encoded:
  bounded_object_q_encoded radius ==>
  bounded_packed_q_interval_encoded
    (bounded_packed_source_q_symmetric_interval_cv radius)
Proof
  simp
    [bounded_packed_source_q_symmetric_interval_cv_def,
     compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def,
     bounded_packed_source_q_neg_encoded]
QED

Theorem bounded_packed_source_q_symmetric_interval_cv_equiv_cong:
  bounded_case10173_q_cv_equiv actual expected ==>
  bounded_packed_source_q_interval_cv_equiv
    (bounded_packed_source_q_symmetric_interval_cv actual)
    (bounded_packed_source_q_symmetric_interval_cv expected)
Proof
  strip_tac
  >> simp
       [bounded_packed_source_q_interval_cv_equiv_def,
        bounded_packed_source_q_symmetric_interval_cv_def]
  >> metis_tac [bounded_packed_source_q_neg_cv_equiv_cong]
QED

Definition bounded_packed_source_q_symmetric_interval_body_def:
  bounded_packed_source_q_symmetric_interval_body =
    Pair
      (App «candle_cv_q_neg» [Var «radius»])
      (Var «radius»)
End

Theorem bounded_packed_source_q_symmetric_interval_lookup:
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_symmetric_interval» =
    SOME ([«radius»],bounded_packed_source_q_symmetric_interval_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_q_symmetric_interval_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_symmetric_interval» [from_cv radius])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst [(«radius»,from_cv radius)]
        bounded_packed_source_q_symmetric_interval_body) refs
Proof
  strip_tac
  >> irule bounded_packed_source_compute_eval_literal_app1
  >> simp [bounded_packed_source_q_symmetric_interval_lookup]
QED

Theorem bounded_packed_source_q_symmetric_interval_eval:
  bounded_object_q_encoded radius /\
  4 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_symmetric_interval» [from_cv radius])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_packed_source_q_symmetric_interval_cv radius)),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_q_symmetric_interval_unfold]
  >> simp
       [bounded_packed_source_q_symmetric_interval_body_def,
        compute_evalTheory.subst_def,
        bounded_packed_source_q_symmetric_interval_cv_def]
  >> once_rewrite_tac
       [GSYM (CONJUNCT2 compute_execTheory.from_cv_def)]
  >> irule
       compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results
  >> conj_tac
  >- (irule bounded_packed_source_q_neg_object_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_source_q_symmetric_interval_relation_eval:
  bounded_case10173_q_cv_equiv radius semantic_radius /\
  4 < clock ==>
  ?result.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_symmetric_interval» [from_cv radius])
        (refs:hol_refs) =
      (M_success (from_cv result),refs) /\
    bounded_packed_source_q_interval_cv_equiv result
      (bounded_packed_source_q_symmetric_interval_cv semantic_radius)
Proof
  strip_tac
  >> qexists_tac `bounded_packed_source_q_symmetric_interval_cv radius`
  >> conj_tac
  >- (irule bounded_packed_source_q_symmetric_interval_eval
      >> metis_tac [bounded_packed_source_q_cv_equiv_left_encoded])
  >> irule bounded_packed_source_q_symmetric_interval_cv_equiv_cong
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_interval_add_cv_equiv_cong:
  bounded_packed_source_q_interval_cv_equiv left semantic_left /\
  bounded_packed_source_q_interval_cv_equiv right semantic_right ==>
  bounded_packed_source_q_interval_cv_equiv
    (bounded_packed_q_source_interval_add_cv left right)
    (bounded_packed_q_source_interval_add_cv semantic_left semantic_right)
Proof
  rw [bounded_packed_source_q_interval_cv_equiv_def]
  >> simp
       [compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_interval_add_cv_def,
        bounded_packed_source_q_interval_cv_equiv_def]
  >> metis_tac
       [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong]
QED

Definition bounded_packed_source_q_interval_add_extended_body_def:
  bounded_packed_source_q_interval_add_extended_body =
    Pair
      (App «candle_cv_q_add_normalized_extended»
        [Uop Fst (Var «x»);Uop Fst (Var «y»)])
      (App «candle_cv_q_add_normalized_extended»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Theorem bounded_packed_source_q_interval_add_extended_lookup:
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_interval_add_extended» =
    SOME
      ([«x»;«y»],bounded_packed_source_q_interval_add_extended_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_q_interval_add_extended_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_interval_add_extended»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst [(«x»,from_cv left);(«y»,from_cv right)]
        bounded_packed_source_q_interval_add_extended_body) refs
Proof
  strip_tac
  >> irule bounded_packed_source_compute_eval_literal_app2
  >> simp [bounded_packed_source_q_interval_add_extended_lookup]
QED

Theorem bounded_packed_source_q_interval_add_extended_pair_relation_eval:
  bounded_object_q_encoded left_lower /\
  bounded_object_q_encoded left_upper /\
  bounded_object_q_encoded right_lower /\
  bounded_object_q_encoded right_upper /\
  bounded_case10173_q_cv_equiv left_lower semantic_left_lower /\
  bounded_case10173_q_cv_equiv left_upper semantic_left_upper /\
  bounded_case10173_q_cv_equiv right_lower semantic_right_lower /\
  bounded_case10173_q_cv_equiv right_upper semantic_right_upper /\
  155 < clock ==>
  ?result_lower result_upper.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_interval_add_extended»
          [from_cv (Pair left_lower left_upper);
           from_cv (Pair right_lower right_upper)]) (refs:hol_refs) =
      (M_success (from_cv (Pair result_lower result_upper)),refs) /\
    bounded_case10173_q_cv_equiv result_lower
      (bounded_object_q_add_cv semantic_left_lower semantic_right_lower) /\
    bounded_case10173_q_cv_equiv result_upper
      (bounded_object_q_add_cv semantic_left_upper semantic_right_upper)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`left` |-> `left_lower`,`right` |-> `right_lower`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_add_normalized_extended_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `result_lower` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`left` |-> `left_upper`,`right` |-> `right_upper`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_add_normalized_extended_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `result_upper` strip_assume_tac)
  >> qexists_tac `result_lower`
  >> qexists_tac `result_upper`
  >> conj_tac
  >- (rw [bounded_packed_source_q_interval_add_extended_unfold]
      >> simp
           [bounded_packed_source_q_interval_add_extended_body_def,
            compute_evalTheory.subst_def,
            compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results)
      >> conj_tac
      >- (irule EQ_TRANS
          >> qexists_tac
               `compute_eval (clock - 1)
                  bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                  (App «candle_cv_q_add_normalized_extended»
                    [from_cv left_lower;from_cv right_lower]) refs`
          >> conj_tac
          >- (irule bounded_packed_source_compute_eval_app2_argument_results
              >> conj_tac >- intLib.ARITH_TAC
              >> simp
                   [compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_fst_literal_pair])
          >> asm_rewrite_tac [])
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_packed_source_cell0_entry_v2173_ceqs
              (App «candle_cv_q_add_normalized_extended»
                [from_cv left_upper;from_cv right_upper]) refs`
      >> conj_tac
      >- (irule bounded_packed_source_compute_eval_app2_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> simp
               [compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_snd_literal_pair])
      >> asm_rewrite_tac [])
  >> conj_tac
  >- (irule
        compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
      >> qexists_tac `bounded_object_q_add_cv left_lower right_lower`
      >> asm_rewrite_tac []
      >> irule compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong
      >> asm_rewrite_tac [])
  >> irule
       compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
  >> qexists_tac `bounded_object_q_add_cv left_upper right_upper`
  >> asm_rewrite_tac []
  >> irule compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_interval_add_extended_relation_eval:
  bounded_packed_source_q_interval_cv_equiv left semantic_left /\
  bounded_packed_source_q_interval_cv_equiv right semantic_right /\
  155 < clock ==>
  ?result.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_interval_add_extended»
          [from_cv left;from_cv right]) (refs:hol_refs) =
      (M_success (from_cv result),refs) /\
    bounded_packed_source_q_interval_cv_equiv result
      (bounded_packed_q_source_interval_add_cv semantic_left semantic_right)
Proof
  rw [bounded_packed_source_q_interval_cv_equiv_def]
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `actual_lower`,
          `left_upper` |-> `actual_upper`,
          `right_lower` |-> `actual_lower'`,
          `right_upper` |-> `actual_upper'`,
          `semantic_left_lower` |-> `expected_lower`,
          `semantic_left_upper` |-> `expected_upper`,
          `semantic_right_lower` |-> `expected_lower'`,
          `semantic_right_upper` |-> `expected_upper'`,
          `clock` |-> `clock`,`refs` |-> `refs`]
         bounded_packed_source_q_interval_add_extended_pair_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> metis_tac
           [bounded_packed_source_q_cv_equiv_left_encoded])
  >> disch_then
       (qx_choose_then `result_lower`
         (qx_choose_then `result_upper` strip_assume_tac))
  >> qexists_tac `Pair result_lower result_upper`
  >> conj_tac >- asm_rewrite_tac []
  >> simp
       [compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_interval_add_cv_def]
  >> asm_rewrite_tac []
QED

Definition bounded_packed_source_q_taylor_model_value_cv_def:
  bounded_packed_source_q_taylor_model_value_cv
      center_value radii gradient hessian =
    bounded_packed_q_source_interval_add_cv center_value
      (bounded_packed_source_q_symmetric_interval_cv
        (bounded_packed_source_q_taylor_model_error_cv
          radii gradient hessian))
End

Definition bounded_packed_source_q_taylor_model_value_body_def:
  bounded_packed_source_q_taylor_model_value_body =
    App «candle_cv_q_interval_add_extended»
      [App «candle_cv_q_dim_first_jet_f» [Var «center_first»];
       App «candle_cv_q_symmetric_interval»
         [App «candle_cv_q_dim_taylor_model_error»
           [Var «radii»;Var «center_first»;Var «hessian»]]]
End

Theorem bounded_packed_source_q_taylor_model_value_lookup:
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_dim_taylor_model_value_bound» =
    SOME
      ([«radii»;«center_first»;«hessian»],
       bounded_packed_source_q_taylor_model_value_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_q_taylor_model_value_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dim_taylor_model_value_bound»
        [from_cv radii;from_cv center_first;from_cv hessian])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst
        [(«radii»,from_cv radii);(«center_first»,from_cv center_first);
         («hessian»,from_cv hessian)]
        bounded_packed_source_q_taylor_model_value_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectErrorEvalTheory.bounded_packed_compute_eval_literal_app3
  >> simp [bounded_packed_source_q_taylor_model_value_lookup]
QED

Theorem bounded_packed_source_q_taylor_model_value_relation_eval:
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded gradient /\
  EVERY (EVERY bounded_packed_q_interval_encoded) hessian /\
  700 * (LENGTH radii + 1) < clock ==>
  ?result.
    compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_dim_taylor_model_value_bound»
          [from_cv (bounded_object_q_cv_list radii);
           from_cv
             (Pair center_value (bounded_object_q_cv_list gradient));
           from_cv
             (bounded_object_q_cv_list
               (MAP bounded_object_q_cv_list hessian))])
        (refs:hol_refs) =
      (M_success (from_cv result),refs) /\
    bounded_packed_source_q_interval_cv_equiv result
      (bounded_packed_source_q_taylor_model_value_cv
        center_value radii gradient hessian)
Proof
  strip_tac
  >> `0 < clock` by intLib.ARITH_TAC
  >> mp_tac
       (Q.INST
         [`radii` |-> `radii`,`center_value` |-> `center_value`,
          `gradient` |-> `gradient`,`hessian` |-> `hessian`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_taylor_model_error_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `error_result` strip_assume_tac)
  >> `compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_dim_taylor_model_value_bound»
          [from_cv (bounded_object_q_cv_list radii);
           from_cv
             (Pair center_value (bounded_object_q_cv_list gradient));
           from_cv
             (bounded_object_q_cv_list
               (MAP bounded_object_q_cv_list hessian))]) refs =
      compute_eval (clock - 1)
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (subst
          [(«radii»,from_cv (bounded_object_q_cv_list radii));
           («center_first»,from_cv
             (Pair center_value (bounded_object_q_cv_list gradient)));
           («hessian»,from_cv
             (bounded_object_q_cv_list
               (MAP bounded_object_q_cv_list hessian)))]
          bounded_packed_source_q_taylor_model_value_body) refs` by
       (irule bounded_packed_source_q_taylor_model_value_unfold
        >> asm_rewrite_tac [])
  >> fs [compute_execTheory.from_cv_def]
  >> `bounded_object_q_encoded error_result` by
       metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
  >> mp_tac
       (Q.INST
         [`radius` |-> `error_result`,
          `semantic_radius` |->
            `bounded_packed_source_q_taylor_model_error_cv
               radii gradient hessian`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_symmetric_interval_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `symmetric_result` strip_assume_tac)
  >> `compute_eval (clock - 1)
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_symmetric_interval»
          [App «candle_cv_q_dim_taylor_model_error»
            [from_cv (bounded_object_q_cv_list radii);
             Pair (from_cv center_value)
               (from_cv (bounded_object_q_cv_list gradient));
             from_cv
               (bounded_object_q_cv_list
                 (MAP bounded_object_q_cv_list hessian))]]) refs =
      (M_success (from_cv symmetric_result),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval (clock - 1)
                bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                (App «candle_cv_q_symmetric_interval»
                  [from_cv error_result]) refs`
        >> conj_tac
        >- (irule bounded_packed_source_compute_eval_app1_argument_result
            >> asm_rewrite_tac []
            >> intLib.ARITH_TAC)
        >> asm_rewrite_tac [])
  >> `bounded_packed_source_q_interval_cv_equiv
        center_value center_value` by
       (irule bounded_packed_source_q_interval_cv_equiv_refl
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`left` |-> `center_value`,`semantic_left` |-> `center_value`,
          `right` |-> `symmetric_result`,
          `semantic_right` |->
            `bounded_packed_source_q_symmetric_interval_cv
               (bounded_packed_source_q_taylor_model_error_cv
                 radii gradient hessian)`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_interval_add_extended_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `value_result` strip_assume_tac)
  >> qexists_tac `value_result`
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_packed_source_cell0_entry_v2173_ceqs
              (subst
                [(«radii»,from_cv (bounded_object_q_cv_list radii));
                 («center_first»,
                   Pair (from_cv center_value)
                     (from_cv (bounded_object_q_cv_list gradient)));
                 («hessian»,from_cv
                   (bounded_object_q_cv_list
                     (MAP bounded_object_q_cv_list hessian)))]
                bounded_packed_source_q_taylor_model_value_body) refs`
      >> conj_tac
      >- asm_rewrite_tac []
      >> simp
           [bounded_packed_source_q_taylor_model_value_body_def,
            compute_evalTheory.subst_def]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_packed_source_cell0_entry_v2173_ceqs
              (App «candle_cv_q_interval_add_extended»
                [from_cv center_value;from_cv symmetric_result]) refs`
      >> conj_tac
      >- (irule bounded_packed_source_compute_eval_app2_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> conj_tac
          >- (irule
                (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                  bounded_packed_source_q_dim_first_jet_f_eval)
              >> intLib.ARITH_TAC)
          >> asm_rewrite_tac [])
      >> asm_rewrite_tac [])
  >> rw [bounded_packed_source_q_taylor_model_value_cv_def]
  >> asm_rewrite_tac []
QED

Definition bounded_packed_source_q_taylor_model_gradient_cv_def:
  bounded_packed_source_q_taylor_model_gradient_cv radii gradients rows =
    case gradients of
      [] => []
    | gradient::tail_gradients =>
        case rows of
          [] => []
        | row::tail_rows =>
            bounded_packed_q_source_interval_add_cv gradient
              (bounded_packed_source_q_symmetric_interval_cv
                (bounded_packed_q_source_dot_abs_upper_cv radii row)) ::
            bounded_packed_source_q_taylor_model_gradient_cv
              radii tail_gradients tail_rows
End

Definition bounded_packed_source_q_taylor_model_gradient_body_def:
  bounded_packed_source_q_taylor_model_gradient_body =
    If (Uop Ispair (Var «gradient_intervals»))
      (If (Uop Ispair (Var «row_lists»))
        (Pair
          (App «candle_cv_q_interval_add_extended»
            [Uop Fst (Var «gradient_intervals»);
             App «candle_cv_q_symmetric_interval»
               [App «candle_cv_q_dot_abs_upper_extended»
                 [Var «radii»;Uop Fst (Var «row_lists»)]]])
          (App «candle_cv_q_dim_taylor_model_gradient_bounds»
            [Var «radii»;Uop Snd (Var «gradient_intervals»);
             Uop Snd (Var «row_lists»)]))
        (Num 0))
      (Num 0)
End

Theorem bounded_packed_source_q_taylor_model_gradient_lookup:
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_dim_taylor_model_gradient_bounds» =
    SOME
      ([«radii»;«gradient_intervals»;«row_lists»],
       bounded_packed_source_q_taylor_model_gradient_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_q_taylor_model_gradient_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dim_taylor_model_gradient_bounds»
        [from_cv radii;from_cv gradient_intervals;from_cv row_lists])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst
        [(«radii»,from_cv radii);
         («gradient_intervals»,from_cv gradient_intervals);
         («row_lists»,from_cv row_lists)]
        bounded_packed_source_q_taylor_model_gradient_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectErrorEvalTheory.bounded_packed_compute_eval_literal_app3
  >> simp [bounded_packed_source_q_taylor_model_gradient_lookup]
QED

Theorem bounded_packed_source_q_taylor_model_gradient_relation_eval:
  !gradients rows radii clock refs.
    EVERY bounded_object_q_encoded radii /\
    EVERY bounded_packed_q_interval_encoded gradients /\
    EVERY (EVERY bounded_packed_q_interval_encoded) rows /\
    LENGTH gradients = LENGTH rows /\
    400 * (LENGTH gradients + 1) +
      200 * (LENGTH radii + 1) < clock ==>
    ?result.
      compute_eval clock
          bounded_case16594_packed_source_cell0_entry_v2173_ceqs
          (App «candle_cv_q_dim_taylor_model_gradient_bounds»
            [from_cv (bounded_object_q_cv_list radii);
             from_cv (bounded_object_q_cv_list gradients);
             from_cv
               (bounded_object_q_cv_list
                 (MAP bounded_object_q_cv_list rows))])
          (refs:hol_refs) =
        (M_success
          (from_cv (bounded_object_q_cv_list result)),refs) /\
      LIST_REL bounded_packed_source_q_interval_cv_equiv result
        (bounded_packed_source_q_taylor_model_gradient_cv
          radii gradients rows)
Proof
  Induct_on `gradients`
  >- (rw [bounded_packed_source_q_taylor_model_gradient_cv_def]
      >> fs []
      >> rw [bounded_packed_source_q_taylor_model_gradient_unfold]
      >> simp
           [bounded_packed_source_q_taylor_model_gradient_body_def,
            compute_evalTheory.subst_def,
            compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_num,
            compute_execProofTheory.compute_eval_from_cv]
      >> (ACCEPT_TAC
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`x` |-> `(Num 0:cv)`,`s` |-> `refs`,
                 `ck` |-> `clock - 1`,
                 `eqs` |->
                   `bounded_case16594_packed_source_cell0_entry_v2173_ceqs`]
                (SPEC_ALL compute_execProofTheory.compute_eval_from_cv)))))
  >> Cases_on `rows` >- simp []
  >> rw [Once bounded_packed_source_q_taylor_model_gradient_cv_def]
  >> rw [bounded_packed_source_q_taylor_model_gradient_unfold]
  >> simp
       [bounded_packed_source_q_taylor_model_gradient_body_def,
        compute_evalTheory.subst_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair]
  >> `EVERY bounded_packed_q_interval_encoded h` by fs []
  >> `160 * (LENGTH radii + 1) < clock - 1` by intLib.ARITH_TAC
  >> `?dot_result.
        compute_eval (clock - 1)
            bounded_case16594_packed_source_cell0_entry_v2173_ceqs
            (App «candle_cv_q_dot_abs_upper_extended»
              [from_cv (bounded_object_q_cv_list radii);
               from_cv (bounded_object_q_cv_list h)]) refs =
          (M_success (from_cv dot_result),refs) /\
        bounded_case10173_q_cv_equiv dot_result
          (bounded_packed_q_source_dot_abs_upper_cv radii h)` by
       (irule bounded_packed_source_q_dot_abs_upper_extended_relation_eval
        >> asm_rewrite_tac [])
  >> `bounded_object_q_encoded dot_result` by
       metis_tac [bounded_packed_source_q_cv_equiv_left_encoded]
  >> `?symmetric_result.
        compute_eval (clock - 1)
            bounded_case16594_packed_source_cell0_entry_v2173_ceqs
            (App «candle_cv_q_symmetric_interval»
              [from_cv dot_result]) refs =
          (M_success (from_cv symmetric_result),refs) /\
        bounded_packed_source_q_interval_cv_equiv symmetric_result
          (bounded_packed_source_q_symmetric_interval_cv
            (bounded_packed_q_source_dot_abs_upper_cv radii h))` by
       (irule bounded_packed_source_q_symmetric_interval_relation_eval
        >> asm_rewrite_tac []
        >> intLib.ARITH_TAC)
  >> `bounded_packed_source_q_interval_cv_equiv h' h'` by
       (irule bounded_packed_source_q_interval_cv_equiv_refl
        >> fs [])
  >> `?head_result.
        compute_eval (clock - 1)
            bounded_case16594_packed_source_cell0_entry_v2173_ceqs
            (App «candle_cv_q_interval_add_extended»
              [from_cv h';from_cv symmetric_result]) refs =
          (M_success (from_cv head_result),refs) /\
        bounded_packed_source_q_interval_cv_equiv head_result
          (bounded_packed_q_source_interval_add_cv h'
            (bounded_packed_source_q_symmetric_interval_cv
              (bounded_packed_q_source_dot_abs_upper_cv radii h)))` by
       (irule bounded_packed_source_q_interval_add_extended_relation_eval
        >> asm_rewrite_tac []
        >> intLib.ARITH_TAC)
  >> `?tail_result.
        compute_eval (clock - 1)
            bounded_case16594_packed_source_cell0_entry_v2173_ceqs
            (App «candle_cv_q_dim_taylor_model_gradient_bounds»
              [from_cv (bounded_object_q_cv_list radii);
               from_cv (bounded_object_q_cv_list gradients);
               from_cv
                 (bounded_object_q_cv_list
                   (MAP bounded_object_q_cv_list t))]) refs =
          (M_success
            (from_cv (bounded_object_q_cv_list tail_result)),refs) /\
        LIST_REL bounded_packed_source_q_interval_cv_equiv tail_result
          (bounded_packed_source_q_taylor_model_gradient_cv
            radii gradients t)` by
       (first_x_assum match_mp_tac
        >> asm_rewrite_tac []
        >> intLib.ARITH_TAC)
  >> qexists_tac `head_result::tail_result`
  >> conj_tac
  >- (rw
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results)
      >> conj_tac
      >- (irule EQ_TRANS
          >> qexists_tac
               `compute_eval (clock - 1)
                  bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                  (App «candle_cv_q_interval_add_extended»
                    [from_cv h';from_cv symmetric_result]) refs`
          >> conj_tac
          >- (irule bounded_packed_source_compute_eval_app2_argument_results
              >> conj_tac >- intLib.ARITH_TAC
              >> conj_tac
              >- simp
                   [compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_fst_literal_pair]
              >> irule EQ_TRANS
              >> qexists_tac
                   `compute_eval (clock - 1)
                      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                      (App «candle_cv_q_symmetric_interval»
                        [from_cv dot_result]) refs`
              >> conj_tac
              >- (irule bounded_packed_source_compute_eval_app1_argument_result
                  >> conj_tac >- intLib.ARITH_TAC
                  >> irule EQ_TRANS
                  >> qexists_tac
                       `compute_eval (clock - 1)
                          bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                          (App «candle_cv_q_dot_abs_upper_extended»
                            [from_cv (bounded_object_q_cv_list radii);
                             from_cv (bounded_object_q_cv_list h)]) refs`
                  >> conj_tac
                  >- (irule bounded_packed_source_compute_eval_app2_argument_results
                      >> conj_tac >- intLib.ARITH_TAC
                      >> simp
                           [compute_execProofTheory.compute_eval_from_cv,
                            compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_fst_literal_pair])
                  >> asm_rewrite_tac [])
              >> asm_rewrite_tac [])
          >> asm_rewrite_tac [])
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_packed_source_cell0_entry_v2173_ceqs
              (App «candle_cv_q_dim_taylor_model_gradient_bounds»
                [from_cv (bounded_object_q_cv_list radii);
                 from_cv (bounded_object_q_cv_list gradients);
                 from_cv
                   (bounded_object_q_cv_list
                     (MAP bounded_object_q_cv_list t))]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_snd_literal_pair]
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> simp []
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_complete_value_relation_eval:
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded gradient /\
  EVERY (EVERY bounded_packed_q_interval_encoded) hessian /\
  800 * (LENGTH radii + 1) < clock ==>
  ?value_bound.
    compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (bounded_packed_source_q_complete_value_exp
          (from_cv (bounded_object_q_cv_list radii))
          (from_cv
            (Pair center_value (bounded_object_q_cv_list gradient)))
          (from_cv (bounded_packed_source_q_cv_matrix hessian)))
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_packed_source_q_fixed_interval_round_cv value_bound)),
       refs) /\
    bounded_packed_source_q_interval_cv_equiv value_bound
      (bounded_packed_source_q_taylor_model_value_cv
        center_value radii gradient hessian)
Proof
  strip_tac
  >> rw [bounded_packed_source_q_cv_matrix_def]
  >> `?value_bound.
        compute_eval clock
            bounded_case16594_packed_source_cell0_entry_v2173_ceqs
            (App «candle_cv_q_dim_taylor_model_value_bound»
              [from_cv (bounded_object_q_cv_list radii);
               from_cv
                 (Pair center_value
                   (bounded_object_q_cv_list gradient));
               from_cv
                 (bounded_object_q_cv_list
                   (MAP bounded_object_q_cv_list hessian))]) refs =
          (M_success (from_cv value_bound),refs) /\
        bounded_packed_source_q_interval_cv_equiv value_bound
          (bounded_packed_source_q_taylor_model_value_cv
            center_value radii gradient hessian)` by
       (irule bounded_packed_source_q_taylor_model_value_relation_eval
        >> asm_rewrite_tac []
        >> intLib.ARITH_TAC)
  >> `bounded_packed_q_interval_encoded value_bound` by
       metis_tac
         [bounded_packed_source_q_interval_cv_equiv_left_encoded]
  >> qexists_tac `value_bound`
  >> conj_tac
  >- (rw [bounded_packed_source_q_complete_value_exp_def]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock
              bounded_case16594_packed_source_cell0_entry_v2173_ceqs
              (App «candle_cv_q_fixed_interval_round»
                [from_cv value_bound]) refs`
      >> conj_tac
      >- (irule bounded_packed_source_compute_eval_app1_argument_result
          >> conj_tac >- intLib.ARITH_TAC
          >> fs [compute_execTheory.from_cv_def])
      >> irule
           bounded_packed_source_q_fixed_interval_round_object_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_interval_cv_equiv_every_left_encoded:
  !left right.
    LIST_REL bounded_packed_source_q_interval_cv_equiv left right ==>
    EVERY bounded_packed_q_interval_encoded left
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> simp []
  >> metis_tac [bounded_packed_source_q_interval_cv_equiv_left_encoded]
QED

Theorem bounded_packed_source_q_taylor_model_gradient_cv_length:
  !gradients rows radii.
    LENGTH gradients = LENGTH rows ==>
    LENGTH
      (bounded_packed_source_q_taylor_model_gradient_cv
        radii gradients rows) = LENGTH gradients
Proof
  Induct_on `gradients`
  >> Cases_on `rows`
  >> simp [Once bounded_packed_source_q_taylor_model_gradient_cv_def]
QED

Theorem bounded_packed_source_q_complete_gradient_relation_eval:
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded gradient /\
  EVERY (EVERY bounded_packed_q_interval_encoded) hessian /\
  LENGTH gradient = LENGTH hessian /\
  800 * (LENGTH gradient + LENGTH radii + 2) < clock ==>
  ?gradient_bounds.
    compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (bounded_packed_source_q_complete_gradient_exp
          (from_cv (bounded_object_q_cv_list radii))
          (from_cv
            (Pair center_value (bounded_object_q_cv_list gradient)))
          (from_cv (bounded_packed_source_q_cv_matrix hessian)))
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_object_q_cv_list
            (MAP bounded_packed_source_q_fixed_interval_round_cv
              gradient_bounds))),refs) /\
    LIST_REL bounded_packed_source_q_interval_cv_equiv gradient_bounds
      (bounded_packed_source_q_taylor_model_gradient_cv
        radii gradient hessian)
Proof
  strip_tac
  >> rw [bounded_packed_source_q_cv_matrix_def]
  >> `?gradient_bounds.
        compute_eval clock
            bounded_case16594_packed_source_cell0_entry_v2173_ceqs
            (App «candle_cv_q_dim_taylor_model_gradient_bounds»
              [from_cv (bounded_object_q_cv_list radii);
               from_cv (bounded_object_q_cv_list gradient);
               from_cv
                 (bounded_object_q_cv_list
                   (MAP bounded_object_q_cv_list hessian))]) refs =
          (M_success
            (from_cv (bounded_object_q_cv_list gradient_bounds)),refs) /\
        LIST_REL bounded_packed_source_q_interval_cv_equiv gradient_bounds
          (bounded_packed_source_q_taylor_model_gradient_cv
            radii gradient hessian)` by
       (irule bounded_packed_source_q_taylor_model_gradient_relation_eval
        >> asm_rewrite_tac []
        >> intLib.ARITH_TAC)
  >> `EVERY bounded_packed_q_interval_encoded gradient_bounds` by
       metis_tac
         [bounded_packed_source_q_interval_cv_equiv_every_left_encoded]
  >> `LENGTH gradient_bounds = LENGTH gradient` by
       metis_tac
         [LIST_REL_LENGTH,
          bounded_packed_source_q_taylor_model_gradient_cv_length]
  >> qexists_tac `gradient_bounds`
  >> conj_tac
  >- (rw [bounded_packed_source_q_complete_gradient_exp_def]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock
              bounded_case16594_packed_source_cell0_entry_v2173_ceqs
              (App «candle_cv_q_fixed_interval_list_round»
                [from_cv (bounded_object_q_cv_list gradient_bounds)]) refs`
      >> conj_tac
      >- (irule bounded_packed_source_compute_eval_app1_argument_result
          >> conj_tac >- intLib.ARITH_TAC
          >> irule EQ_TRANS
          >> qexists_tac
               `compute_eval clock
                  bounded_case16594_packed_source_cell0_entry_v2173_ceqs
                  (App «candle_cv_q_dim_taylor_model_gradient_bounds»
                    [from_cv (bounded_object_q_cv_list radii);
                     from_cv (bounded_object_q_cv_list gradient);
                     from_cv
                       (bounded_object_q_cv_list
                         (MAP bounded_object_q_cv_list hessian))]) refs`
          >> conj_tac
          >- (irule
                compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
              >> conj_tac >- intLib.ARITH_TAC
              >> conj_tac
              >- simp [compute_execProofTheory.compute_eval_from_cv]
              >> conj_tac
              >- (`Pair (from_cv center_value)
                       (from_cv (bounded_object_q_cv_list gradient)) =
                    from_cv
                      (Pair center_value
                        (bounded_object_q_cv_list gradient))` by
                    simp [compute_execTheory.from_cv_def]
                  >> asm_rewrite_tac []
                  >> irule
                       bounded_packed_source_q_dim_first_jet_gradient_eval
                  >> intLib.ARITH_TAC)
              >> simp [compute_execProofTheory.compute_eval_from_cv])
          >> asm_rewrite_tac [])
      >> irule
           bounded_packed_source_q_fixed_interval_list_round_object_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_result_complete_rounded_relation_eval:
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded gradient /\
  EVERY (EVERY bounded_packed_q_interval_encoded) hessian /\
  LENGTH gradient = LENGTH hessian /\
  1000 * (LENGTH gradient + LENGTH radii + 2) < clock ==>
  ?value_bound gradient_bounds.
    compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_dim_taylor_model_result_complete_rounded»
          [from_cv (bounded_object_q_cv_list radii);
           from_cv domain_cv;
           from_cv
             (Pair center_value (bounded_object_q_cv_list gradient));
           from_cv (bounded_packed_source_q_cv_matrix hessian)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_packed_source_q_taylor_result_cv domain_cv
            (Pair center_value (bounded_object_q_cv_list gradient))
            (bounded_packed_source_q_fixed_interval_round_cv value_bound)
            (bounded_object_q_cv_list
              (MAP bounded_packed_source_q_fixed_interval_round_cv
                gradient_bounds))
            (bounded_packed_source_q_cv_matrix hessian))),refs) /\
    bounded_packed_source_q_interval_cv_equiv value_bound
      (bounded_packed_source_q_taylor_model_value_cv
        center_value radii gradient hessian) /\
    LIST_REL bounded_packed_source_q_interval_cv_equiv gradient_bounds
      (bounded_packed_source_q_taylor_model_gradient_cv
        radii gradient hessian)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`radii` |-> `radii`,`center_value` |-> `center_value`,
          `gradient` |-> `gradient`,`hessian` |-> `hessian`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_complete_value_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `value_bound` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`radii` |-> `radii`,`center_value` |-> `center_value`,
          `gradient` |-> `gradient`,`hessian` |-> `hessian`,
          `clock` |-> `clock - 1`,`refs` |-> `refs`]
         bounded_packed_source_q_complete_gradient_relation_eval)
  >> impl_tac
  >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `gradient_bounds` strip_assume_tac)
  >> qexists_tac `value_bound`
  >> qexists_tac `gradient_bounds`
  >> conj_tac
  >- (irule
        bounded_packed_source_q_result_complete_rounded_eval_from_results
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_packed_source_q_fixed_round_lower_cv_encoded:
  bounded_object_q_encoded value ==>
  bounded_object_q_encoded
    (bounded_packed_source_q_fixed_round_lower_cv value)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> drule
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> strip_tac
  >> gvs [bounded_packed_source_q_fixed_round_lower_cv_def]
  >> Cases_on `positive < negative`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
QED

Theorem bounded_packed_source_q_fixed_round_upper_cv_encoded:
  bounded_object_q_encoded value ==>
  bounded_object_q_encoded
    (bounded_packed_source_q_fixed_round_upper_cv value)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> drule
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> strip_tac
  >> gvs [bounded_packed_source_q_fixed_round_upper_cv_def]
  >> Cases_on `positive < negative`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
QED

Theorem bounded_packed_source_q_fixed_interval_round_cv_encoded:
  bounded_packed_q_interval_encoded value ==>
  bounded_packed_q_interval_encoded
    (bounded_packed_source_q_fixed_interval_round_cv value)
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> gvs [bounded_packed_source_q_fixed_interval_round_cv_def]
  >> metis_tac
       [bounded_packed_source_q_fixed_round_lower_cv_encoded,
        bounded_packed_source_q_fixed_round_upper_cv_encoded]
QED

Theorem bounded_packed_source_q_fixed_interval_list_round_cv_encoded:
  !values.
    EVERY bounded_packed_q_interval_encoded values ==>
    EVERY bounded_packed_q_interval_encoded
      (MAP bounded_packed_source_q_fixed_interval_round_cv values)
Proof
  Induct_on `values`
  >> simp []
  >> metis_tac [bounded_packed_source_q_fixed_interval_round_cv_encoded]
QED

Theorem bounded_packed_source_q_fixed_interval_matrix_round_cv_encoded:
  !rows.
    EVERY (EVERY bounded_packed_q_interval_encoded) rows ==>
    EVERY (EVERY bounded_packed_q_interval_encoded)
      (MAP
        (MAP bounded_packed_source_q_fixed_interval_round_cv)
        rows)
Proof
  Induct_on `rows`
  >> simp []
  >> metis_tac
       [bounded_packed_source_q_fixed_interval_list_round_cv_encoded]
QED

Theorem bounded_packed_source_q_result_complete_relation_eval:
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded gradient /\
  EVERY (EVERY bounded_packed_q_interval_encoded) hessian /\
  LENGTH gradient = LENGTH hessian /\
  1200 *
    (SUM (MAP LENGTH hessian) + LENGTH gradient + LENGTH radii + 3) <
      clock ==>
  ?value_bound gradient_bounds.
    compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_dim_taylor_model_result_complete»
          [from_cv (bounded_object_q_cv_list radii);
           from_cv domain_cv;
           from_cv
             (Pair center_value (bounded_object_q_cv_list gradient));
           from_cv (bounded_packed_source_q_cv_matrix hessian)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_packed_source_q_taylor_result_cv domain_cv
            (Pair
              (bounded_packed_source_q_fixed_interval_round_cv center_value)
              (bounded_object_q_cv_list
                (MAP bounded_packed_source_q_fixed_interval_round_cv
                  gradient)))
            (bounded_packed_source_q_fixed_interval_round_cv value_bound)
            (bounded_object_q_cv_list
              (MAP bounded_packed_source_q_fixed_interval_round_cv
                gradient_bounds))
            (bounded_packed_source_q_cv_matrix
              (MAP
                (MAP bounded_packed_source_q_fixed_interval_round_cv)
                hessian)))),refs) /\
    bounded_packed_source_q_interval_cv_equiv value_bound
      (bounded_packed_source_q_taylor_model_value_cv
        (bounded_packed_source_q_fixed_interval_round_cv center_value)
        radii
        (MAP bounded_packed_source_q_fixed_interval_round_cv gradient)
        (MAP
          (MAP bounded_packed_source_q_fixed_interval_round_cv)
          hessian)) /\
    LIST_REL bounded_packed_source_q_interval_cv_equiv gradient_bounds
      (bounded_packed_source_q_taylor_model_gradient_cv radii
        (MAP bounded_packed_source_q_fixed_interval_round_cv gradient)
        (MAP
          (MAP bounded_packed_source_q_fixed_interval_round_cv)
          hessian))
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded
        (bounded_packed_source_q_fixed_interval_round_cv center_value)` by
       metis_tac [bounded_packed_source_q_fixed_interval_round_cv_encoded]
  >> `EVERY bounded_packed_q_interval_encoded
        (MAP bounded_packed_source_q_fixed_interval_round_cv gradient)` by
       metis_tac
         [bounded_packed_source_q_fixed_interval_list_round_cv_encoded]
  >> `EVERY (EVERY bounded_packed_q_interval_encoded)
        (MAP
          (MAP bounded_packed_source_q_fixed_interval_round_cv)
          hessian)` by
       metis_tac
         [bounded_packed_source_q_fixed_interval_matrix_round_cv_encoded]
  >> `compute_eval (clock - 1)
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_dim_first_jet_fixed_round»
          [from_cv
            (Pair center_value
              (bounded_object_q_cv_list gradient))]) refs =
      (M_success
        (from_cv
          (Pair
            (bounded_packed_source_q_fixed_interval_round_cv center_value)
            (bounded_object_q_cv_list
              (MAP bounded_packed_source_q_fixed_interval_round_cv
                gradient)))),refs)` by
       (irule
          bounded_packed_source_q_dim_first_jet_fixed_round_object_eval
        >> asm_rewrite_tac []
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        (App «candle_cv_q_fixed_interval_matrix_round»
          [from_cv (bounded_packed_source_q_cv_matrix hessian)]) refs =
      (M_success
        (from_cv
          (bounded_packed_source_q_cv_matrix
            (MAP
              (MAP bounded_packed_source_q_fixed_interval_round_cv)
              hessian))),refs)` by
       (irule
          bounded_packed_source_q_fixed_interval_matrix_round_object_eval
        >> asm_rewrite_tac []
        >> intLib.ARITH_TAC)
  >> `?value_bound gradient_bounds.
        compute_eval (clock - 1)
            bounded_case16594_packed_source_cell0_entry_v2173_ceqs
            (App «candle_cv_q_dim_taylor_model_result_complete_rounded»
              [from_cv (bounded_object_q_cv_list radii);
               from_cv domain_cv;
               from_cv
                 (Pair
                   (bounded_packed_source_q_fixed_interval_round_cv
                     center_value)
                   (bounded_object_q_cv_list
                     (MAP
                       bounded_packed_source_q_fixed_interval_round_cv
                       gradient)));
               from_cv
                 (bounded_packed_source_q_cv_matrix
                   (MAP
                     (MAP
                       bounded_packed_source_q_fixed_interval_round_cv)
                     hessian))]) refs =
          (M_success
            (from_cv
              (bounded_packed_source_q_taylor_result_cv domain_cv
                (Pair
                  (bounded_packed_source_q_fixed_interval_round_cv
                    center_value)
                  (bounded_object_q_cv_list
                    (MAP
                      bounded_packed_source_q_fixed_interval_round_cv
                      gradient)))
                (bounded_packed_source_q_fixed_interval_round_cv
                  value_bound)
                (bounded_object_q_cv_list
                  (MAP bounded_packed_source_q_fixed_interval_round_cv
                    gradient_bounds))
                (bounded_packed_source_q_cv_matrix
                  (MAP
                    (MAP
                      bounded_packed_source_q_fixed_interval_round_cv)
                    hessian)))),refs) /\
        bounded_packed_source_q_interval_cv_equiv value_bound
          (bounded_packed_source_q_taylor_model_value_cv
            (bounded_packed_source_q_fixed_interval_round_cv center_value)
            radii
            (MAP bounded_packed_source_q_fixed_interval_round_cv gradient)
            (MAP
              (MAP bounded_packed_source_q_fixed_interval_round_cv)
              hessian)) /\
        LIST_REL bounded_packed_source_q_interval_cv_equiv gradient_bounds
          (bounded_packed_source_q_taylor_model_gradient_cv radii
            (MAP bounded_packed_source_q_fixed_interval_round_cv gradient)
            (MAP
              (MAP bounded_packed_source_q_fixed_interval_round_cv)
              hessian))` by
       (irule
          bounded_packed_source_q_result_complete_rounded_relation_eval
        >> asm_rewrite_tac []
        >> simp []
        >> intLib.ARITH_TAC)
  >> qexists_tac `value_bound`
  >> qexists_tac `gradient_bounds`
  >> conj_tac
  >- (irule bounded_packed_source_q_result_complete_from_evals
      >> asm_rewrite_tac []
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac
           `Pair
              (bounded_packed_source_q_fixed_interval_round_cv center_value)
              (bounded_object_q_cv_list
                (MAP bounded_packed_source_q_fixed_interval_round_cv
                  gradient))`
      >> qexists_tac
           `bounded_packed_source_q_cv_matrix
              (MAP
                (MAP bounded_packed_source_q_fixed_interval_round_cv)
                hessian)`
      >> asm_rewrite_tac []
      )
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
