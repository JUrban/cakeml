(*****************************************************************************
 * Registered rational-normalization refinement.
 *
 * This layer connects the literal CakeML normalizer to the representation-
 * independent rational relation.  The bounded GCD result remains an
 * implementation choice: only the source's verified divide/fallback contract
 * is exposed to later interval and square-root proofs.
 *****************************************************************************)
Theory compute_registeredCase10173QNormalizeRelationEval
Ancestors
  compute_boundedQNormalizeRelation
  compute_registeredCase10173GcdEval
  compute_registeredCase10173SqrtCertificateEval
  compute_registeredCase10173TaylorWeightedRowsEval
Libs
  bossLib preamble intLib

Definition registered_case10173_lc_znormalize_body_def:
  registered_case10173_lc_znormalize_body =
    If
      (Binop Less (Uop Fst (Var «z»)) (Uop Snd (Var «z»)))
      (Pair (Num 0)
        (Binop Sub (Uop Snd (Var «z»)) (Uop Fst (Var «z»))))
      (Pair
        (Binop Sub (Uop Fst (Var «z»)) (Uop Snd (Var «z»)))
        (Num 0))
End

Definition registered_case10173_q_normalize_fallback_body_def:
  registered_case10173_q_normalize_fallback_body =
    Pair (Var «z»)
      (Binop Sub (Var «denominator») (Num 1))
End

Definition registered_case10173_q_normalize_divide_body_def:
  registered_case10173_q_normalize_divide_body =
    Pair
      (Pair
        (Binop Div (Uop Fst (Var «z»)) (Var «common»))
        (Binop Div (Uop Snd (Var «z»)) (Var «common»)))
      (Binop Sub
        (Binop Div (Var «denominator») (Var «common»))
        (Num 1))
End

Definition registered_case10173_q_normalize_verified_body_def:
  registered_case10173_q_normalize_verified_body =
    If (Binop Eq (Var «common») (Num 0))
      (App «candle_cv_q_normalize_fallback»
        [Var «z»;Var «denominator»])
      (If
        (Binop Eq
          (Binop Div (Var «denominator») (Var «common»))
          (Num 0))
        (App «candle_cv_q_normalize_fallback»
          [Var «z»;Var «denominator»])
        (If
          (Binop Eq
            (Binop Mul
              (Binop Div (Uop Fst (Var «z»)) (Var «common»))
              (Var «common»))
            (Uop Fst (Var «z»)))
          (If
            (Binop Eq
              (Binop Mul
                (Binop Div (Uop Snd (Var «z»)) (Var «common»))
                (Var «common»))
              (Uop Snd (Var «z»)))
            (If
              (Binop Eq
                (Binop Mul
                  (Binop Div (Var «denominator») (Var «common»))
                  (Var «common»))
                (Var «denominator»))
              (App «candle_cv_q_normalize_divide»
                [Var «z»;Var «denominator»;Var «common»])
              (App «candle_cv_q_normalize_fallback»
                [Var «z»;Var «denominator»]))
            (App «candle_cv_q_normalize_fallback»
              [Var «z»;Var «denominator»]))
          (App «candle_cv_q_normalize_fallback»
            [Var «z»;Var «denominator»])))
End

Definition registered_case10173_q_normalize_signed_body_def:
  registered_case10173_q_normalize_signed_body =
    App «candle_cv_q_normalize_verified»
      [Var «z»;Var «denominator»;
       App «candle_cv_num_gcd»
         [Binop Add (Uop Fst (Var «z»)) (Uop Snd (Var «z»));
          Var «denominator»]]
End

Definition registered_case10173_q_normalize_body_def:
  registered_case10173_q_normalize_body =
    App «candle_cv_q_normalize_signed»
      [App «candle_cv_lc_znormalize» [Uop Fst (Var «q»)];
       App «candle_cv_q_den» [Var «q»]]
End

Theorem registered_case10173_lc_znormalize_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_lc_znormalize» =
    SOME ([«z»],registered_case10173_lc_znormalize_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_normalize_fallback_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_normalize_fallback» =
    SOME
      ([«z»;«denominator»],
       registered_case10173_q_normalize_fallback_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_normalize_divide_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_normalize_divide» =
    SOME
      ([«z»;«denominator»;«common»],
       registered_case10173_q_normalize_divide_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_normalize_verified_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_normalize_verified» =
    SOME
      ([«z»;«denominator»;«common»],
       registered_case10173_q_normalize_verified_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_normalize_signed_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_normalize_signed» =
    SOME
      ([«z»;«denominator»],
       registered_case10173_q_normalize_signed_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_normalize_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_normalize» =
    SOME ([«q»],registered_case10173_q_normalize_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_normalize_verified_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_verified»
        [from_cv encoded_z;from_cv encoded_denominator;
         from_cv encoded_common]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«z»,from_cv encoded_z);
         («denominator»,from_cv encoded_denominator);
         («common»,from_cv encoded_common)]
        registered_case10173_q_normalize_verified_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_q_normalize_verified_lookup]
QED

Theorem registered_case10173_q_normalize_signed_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_signed»
        [from_cv encoded_z;from_cv encoded_denominator])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«z»,from_cv encoded_z);
         («denominator»,from_cv encoded_denominator)]
        registered_case10173_q_normalize_signed_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_q_normalize_signed_lookup]
QED

Theorem registered_case10173_q_normalize_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize» [from_cv encoded_q])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«q»,from_cv encoded_q)]
        registered_case10173_q_normalize_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_q_normalize_lookup]
QED

Theorem registered_case10173_lc_znormalize_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_lc_znormalize»
        [from_cv (Pair (Num positive) (Num negative))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case10173_lc_znormalize_cv positive negative)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_lc_znormalize_lookup,
        registered_case10173_lc_znormalize_body_def,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_lc_znormalize_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `positive < negative`
  >> fs []
QED

Theorem registered_case10173_q_normalize_fallback_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_fallback»
        [from_cv (Pair (Num positive) (Num negative));
         from_cv (Num denominator)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case10173_q_normalize_fallback_cv
          (Pair (Num positive) (Num negative)) denominator)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_normalize_fallback_lookup,
        registered_case10173_q_normalize_fallback_body_def,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_q_normalize_fallback_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_normalize_fallback_raw_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_fallback»
        [Pair (Num positive) (Num negative);Num denominator])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case10173_q_normalize_fallback_cv
          (Pair (Num positive) (Num negative)) denominator)),refs)
Proof
  mp_tac registered_case10173_q_normalize_fallback_eval
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_q_normalize_divide_eval:
  0 < common /\ 1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_divide»
        [from_cv (Pair (Num positive) (Num negative));
         from_cv (Num denominator);from_cv (Num common)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case10173_q_normalize_divide_cv
          positive negative denominator common)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_normalize_divide_lookup,
        registered_case10173_q_normalize_divide_body_def,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_q_normalize_divide_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_normalize_divide_raw_eval:
  0 < common /\ 1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_divide»
        [Pair (Num positive) (Num negative);Num denominator;Num common])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case10173_q_normalize_divide_cv
          positive negative denominator common)),refs)
Proof
  mp_tac registered_case10173_q_normalize_divide_eval
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_normalize_num_eq_eval:
  compute_eval clock ceqs (Binop Eq (Num left) (Num right))
      (refs:hol_refs) =
    (M_success (Num (if left = right then 1 else 0)),refs)
Proof
  Cases_on `left = right`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_normalize_div_eq_eval:
  compute_eval clock ceqs
      (Binop Eq
        (Binop Div (Num numerator) (Num divisor)) (Num right))
      (refs:hol_refs) =
    (M_success
      (Num
        (if numerator SAFEDIV divisor = right then 1 else 0)),refs)
Proof
  Cases_on `numerator SAFEDIV divisor = right`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_normalize_div_mul_eq_eval:
  compute_eval clock ceqs
      (Binop Eq
        (Binop Mul
          (Binop Div (Num numerator) (Num divisor))
          (Num factor))
        (Num right))
      (refs:hol_refs) =
    (M_success
      (Num
        (if (numerator SAFEDIV divisor) * factor = right
         then 1 else 0)),refs)
Proof
  Cases_on `(numerator SAFEDIV divisor) * factor = right`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_normalize_pair_fst_div_mul_eq_eval:
  compute_eval clock ceqs
      (Binop Eq
        (Binop Mul
          (Binop Div (Uop Fst (Pair (Num positive) (Num negative)))
            (Num divisor))
          (Num factor))
        (Uop Fst (Pair (Num positive) (Num negative))))
      (refs:hol_refs) =
    (M_success
      (Num
        (if (positive SAFEDIV divisor) * factor = positive
         then 1 else 0)),refs)
Proof
  Cases_on `(positive SAFEDIV divisor) * factor = positive`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_normalize_pair_snd_div_mul_eq_eval:
  compute_eval clock ceqs
      (Binop Eq
        (Binop Mul
          (Binop Div (Uop Snd (Pair (Num positive) (Num negative)))
            (Num divisor))
          (Num factor))
        (Uop Snd (Pair (Num positive) (Num negative))))
      (refs:hol_refs) =
    (M_success
      (Num
        (if (negative SAFEDIV divisor) * factor = negative
         then 1 else 0)),refs)
Proof
  Cases_on `(negative SAFEDIV divisor) * factor = negative`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_normalize_verified_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_verified»
        [from_cv (Pair (Num positive) (Num negative));
         from_cv (Num denominator);from_cv (Num common)])
      (refs:hol_refs) =
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
             `encoded_denominator` |-> `(Num denominator:cv)`,
             `encoded_common` |-> `(Num common:cv)`]
            registered_case10173_q_normalize_verified_unfold))]
  >> simp
       [registered_case10173_q_normalize_verified_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on `common = 0`
  >> fs
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_normalize_verified_cv_def,
        registered_case10173_normalize_num_eq_eval,
        registered_case10173_normalize_div_eq_eval,
        registered_case10173_normalize_div_mul_eq_eval,
        registered_case10173_normalize_pair_fst_div_mul_eq_eval,
        registered_case10173_normalize_pair_snd_div_mul_eq_eval,
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero,
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_compute_eval_if_bool,
        registered_case10173_q_normalize_fallback_eval,
        registered_case10173_q_normalize_fallback_raw_eval,
        registered_case10173_q_normalize_divide_eval,
        registered_case10173_q_normalize_divide_raw_eval,
        compute_syntaxTheory.SAFEDIV_def]
  >> Cases_on `denominator DIV common = 0`
  >> fs
       [registered_case10173_normalize_num_eq_eval,
        registered_case10173_normalize_div_eq_eval,
        registered_case10173_normalize_div_mul_eq_eval,
        registered_case10173_normalize_pair_fst_div_mul_eq_eval,
        registered_case10173_normalize_pair_snd_div_mul_eq_eval,
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero,
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_compute_eval_if_bool,
        registered_case10173_q_normalize_fallback_raw_eval,
        registered_case10173_q_normalize_divide_raw_eval,
        compute_syntaxTheory.SAFEDIV_def]
  >> Cases_on `(positive DIV common) * common = positive`
  >> fs
       [registered_case10173_normalize_num_eq_eval,
        registered_case10173_normalize_div_eq_eval,
        registered_case10173_normalize_div_mul_eq_eval,
        registered_case10173_normalize_pair_fst_div_mul_eq_eval,
        registered_case10173_normalize_pair_snd_div_mul_eq_eval,
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero,
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_compute_eval_if_bool,
        registered_case10173_q_normalize_fallback_raw_eval,
        registered_case10173_q_normalize_divide_raw_eval,
        compute_syntaxTheory.SAFEDIV_def]
  >> Cases_on `(negative DIV common) * common = negative`
  >> fs
       [registered_case10173_normalize_num_eq_eval,
        registered_case10173_normalize_div_eq_eval,
        registered_case10173_normalize_div_mul_eq_eval,
        registered_case10173_normalize_pair_fst_div_mul_eq_eval,
        registered_case10173_normalize_pair_snd_div_mul_eq_eval,
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero,
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_compute_eval_if_bool,
        registered_case10173_q_normalize_fallback_raw_eval,
        registered_case10173_q_normalize_divide_raw_eval,
        compute_syntaxTheory.SAFEDIV_def]
  >> Cases_on `(denominator DIV common) * common = denominator`
  >> fs
       [registered_case10173_normalize_num_eq_eval,
        registered_case10173_normalize_div_eq_eval,
        registered_case10173_normalize_div_mul_eq_eval,
        registered_case10173_normalize_pair_fst_div_mul_eq_eval,
        registered_case10173_normalize_pair_snd_div_mul_eq_eval,
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero,
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_compute_eval_if_bool,
        registered_case10173_q_normalize_fallback_raw_eval,
        registered_case10173_q_normalize_divide_raw_eval,
        compute_syntaxTheory.SAFEDIV_def]
QED

Theorem registered_case10173_q_normalize_verified_relation_eval:
  0 < denominator /\ 3 < clock ==>
  ?normalized.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_normalize_verified»
          [from_cv (Pair (Num positive) (Num negative));
           from_cv (Num denominator);from_cv (Num common)])
        (refs:hol_refs) =
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
  >- simp [registered_case10173_q_normalize_verified_eval]
  >> irule
       compute_boundedQNormalizeRelationTheory.bounded_case10173_q_normalize_verified_cv_equiv
  >> first_assum ACCEPT_TAC
QED

Theorem registered_case10173_q_normalize_signed_from_gcd_eval:
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd»
        [Binop Add
           (Uop Fst (from_cv (Pair (Num positive) (Num negative))))
           (Uop Snd (from_cv (Pair (Num positive) (Num negative))));
         from_cv (Num denominator)]) (refs:hol_refs) =
    (M_success (from_cv (Num common)),refs) /\
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_normalize_signed»
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
            registered_case10173_q_normalize_signed_unfold))]
  >> simp
       [registered_case10173_q_normalize_signed_body_def,
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
      >> conj_tac
      >- fs []
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
  >> simp [registered_case10173_q_normalize_verified_eval]
QED

Theorem registered_case10173_q_normalize_signed_relation_from_gcd_eval:
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd»
        [Binop Add
           (Uop Fst (from_cv (Pair (Num positive) (Num negative))))
           (Uop Snd (from_cv (Pair (Num positive) (Num negative))));
         from_cv (Num denominator)]) (refs:hol_refs) =
    (M_success (from_cv (Num common)),refs) /\
  0 < denominator /\ 4 < clock ==>
  ?normalized.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_normalize_signed»
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
  >- (irule registered_case10173_q_normalize_signed_from_gcd_eval
      >> asm_rewrite_tac [])
  >> irule
       compute_boundedQNormalizeRelationTheory.bounded_case10173_q_normalize_verified_cv_equiv
  >> first_assum ACCEPT_TAC
QED

Theorem registered_case10173_q_normalize_signed_relation_eval:
  0 < denominator /\ 136 < clock ==>
  ?normalized.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_normalize_signed»
          [from_cv (Pair (Num positive) (Num negative));
           from_cv (Num denominator)]) (refs:hol_refs) =
      (M_success (from_cv normalized),refs) /\
    bounded_case10173_q_cv_equiv normalized
      (Pair (Pair (Num positive) (Num negative))
        (Num (denominator - 1)))
Proof
  strip_tac
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd»
          [Binop Add
             (Uop Fst (from_cv (Pair (Num positive) (Num negative))))
             (Uop Snd (from_cv (Pair (Num positive) (Num negative))));
           from_cv (Num denominator)]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd»
          [from_cv (Num (positive + negative));
           from_cv (Num denominator)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> conj_tac
        >- simp
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_fst_def,
              compute_evalTheory.do_snd_def,
              compute_evalTheory.do_binop_def,
              compute_evalTheory.do_arith_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> simp
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              ml_monadBaseTheory.st_ex_return_def])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd»
          [Binop Add
             (Uop Fst (from_cv (Pair (Num positive) (Num negative))))
             (Uop Snd (from_cv (Pair (Num positive) (Num negative))));
           from_cv (Num denominator)]) refs =
      (M_success
        (from_cv
          (Num
            (bounded_case10173_num_gcd
              (positive + negative) denominator))),refs)` by
       (asm_rewrite_tac []
        >> irule
             compute_registeredCase10173GcdEvalTheory.registered_case10173_num_gcd_eval
        >> intLib.ARITH_TAC)
  >> irule registered_case10173_q_normalize_signed_relation_from_gcd_eval
  >> conj_tac >- first_assum ACCEPT_TAC
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_case10173_num_gcd
          (positive + negative) denominator`
  >> first_assum ACCEPT_TAC
QED

Theorem registered_case10173_q_normalize_relation_eval:
  0 < denominator /\ 140 < clock ==>
  ?normalized.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_normalize»
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
            >> simp [bounded_case10173_lc_znormalize_cv_def])
        >> qexists_tac `positive - negative`
        >> qexists_tac `0`
        >> simp [bounded_case10173_lc_znormalize_cv_def])
  >> mp_tac
       (Q.INST
         [`positive` |-> `lc_positive`,
          `negative` |-> `lc_negative`,
          `denominator` |-> `denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         registered_case10173_q_normalize_signed_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qexists_tac `normalized`
  >> conj_tac
  >- (simp [registered_case10173_q_normalize_unfold]
      >> simp
           [registered_case10173_q_normalize_body_def,
            compute_evalTheory.subst_def,
            compute_execProofTheory.subst_from_cv]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_q_normalize_signed»
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
                     registered_case10173_lc_znormalize_eval)
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

val _ = export_theory ();
