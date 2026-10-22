(*****************************************************************************
 * Registered evaluator semantics for exact negative rational conversion.
 *
 * The square-root second derivative is represented by a negative rational
 * interval.  Its lower endpoint rounds away from zero and its upper endpoint
 * rounds toward zero.  This is the signed counterpart of the positive
 * conversion layer and keeps that source operation out of each closed cell.
 *****************************************************************************)
Theory compute_registeredCase10173QNegativeConversionEval
Ancestors
  compute_registeredCase10173QDecimalEquiv
  compute_registeredCase10173QConversionEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_q_fixed_round_lower_negative_eval:
  0 < value /\ 7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_round_lower»
        [from_cv
          (Pair (Pair (Num 0) (Num value))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num 0)
            (Num
              ((1000000000000 * value) DIV
                 (denominator_minus_one + 1) +
               if (1000000000000 * value) MOD
                    (denominator_minus_one + 1) = 0
               then 0 else 1)))
          (Num 999999999999))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_lower_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_lower_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
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
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        compute_syntaxTheory.SAFEMOD_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on
       `(1000000000000 * value) MOD (denominator_minus_one + 1) = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_fixed_round_upper_negative_eval:
  0 < value /\ 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_round_upper»
        [from_cv
          (Pair (Pair (Num 0) (Num value))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num 0)
            (Num
              ((1000000000000 * value) DIV
               (denominator_minus_one + 1))))
          (Num 999999999999))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_upper_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_upper_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
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
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_of_q_lower_negative_eval:
  0 < value /\ 9 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_lower»
        [from_cv
          (Pair (Pair (Num 0) (Num value))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (Pair (Num 0)
        (Num
          ((1000000000000 * value) DIV
             (denominator_minus_one + 1) +
           if (1000000000000 * value) MOD
                (denominator_minus_one + 1) = 0
           then 0 else 1))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_of_q_lower_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_of_q_lower_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_lower_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_lower_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
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
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        compute_syntaxTheory.SAFEMOD_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on
       `(1000000000000 * value) MOD (denominator_minus_one + 1) = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_of_q_upper_negative_eval:
  0 < value /\ 7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_upper»
        [from_cv
          (Pair (Pair (Num 0) (Num value))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (Pair (Num 0)
        (Num
          ((1000000000000 * value) DIV
           (denominator_minus_one + 1)))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_of_q_upper_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_of_q_upper_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_upper_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_upper_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
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
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_of_q_lower_negative_fst_eval:
  0 < value /\ 9 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_lower»
        [Uop Fst
          (Pair
            (from_cv
              (Pair (Pair (Num 0) (Num value))
                (Num denominator_minus_one)))
            (from_cv other))]) (refs:hol_refs) =
    (M_success
      (Pair (Num 0)
        (Num
          ((1000000000000 * value) DIV
             (denominator_minus_one + 1) +
           if (1000000000000 * value) MOD
                (denominator_minus_one + 1) = 0
           then 0 else 1))),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_lower»
          [Uop Fst
            (Pair
              (from_cv
                (Pair (Pair (Num 0) (Num value))
                  (Num denominator_minus_one)))
              (from_cv other))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_lower»
          [from_cv
            (Pair (Pair (Num 0) (Num value))
              (Num denominator_minus_one))]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
  >> simp [registered_case10173_fs_of_q_lower_negative_eval]
QED

Theorem registered_case10173_fs_of_q_upper_negative_snd_eval:
  0 < value /\ 7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_upper»
        [Uop Snd
          (Pair
            (from_cv other)
            (from_cv
              (Pair (Pair (Num 0) (Num value))
                (Num denominator_minus_one))))]) (refs:hol_refs) =
    (M_success
      (Pair (Num 0)
        (Num
          ((1000000000000 * value) DIV
           (denominator_minus_one + 1)))),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_upper»
          [Uop Snd
            (Pair
              (from_cv other)
              (from_cv
                (Pair (Pair (Num 0) (Num value))
                  (Num denominator_minus_one))))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_upper»
          [from_cv
            (Pair (Pair (Num 0) (Num value))
              (Num denominator_minus_one))]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> simp [registered_case10173_fs_of_q_upper_negative_eval]
QED

Theorem registered_case10173_fs_interval_of_q_negative_eval:
  0 < lower_value /\ 0 < upper_value /\ 10 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q»
        [from_cv
          (Pair
            (Pair (Pair (Num 0) (Num lower_value))
              (Num lower_denominator_minus_one))
            (Pair (Pair (Num 0) (Num upper_value))
              (Num upper_denominator_minus_one)))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num 0)
            (Num
              ((1000000000000 * lower_value) DIV
                 (lower_denominator_minus_one + 1) +
               if (1000000000000 * lower_value) MOD
                    (lower_denominator_minus_one + 1) = 0
               then 0 else 1)))
          (Pair (Num 0)
            (Num
              ((1000000000000 * upper_value) DIV
               (upper_denominator_minus_one + 1)))))),refs)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_of_q_unfold]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_lower»
          [Uop Fst
            (Pair
              (Pair (Pair (Num 0) (Num lower_value))
                (Num lower_denominator_minus_one))
              (Pair (Pair (Num 0) (Num upper_value))
                (Num upper_denominator_minus_one)))]) refs =
      (M_success
        (Pair (Num 0)
          (Num
            ((1000000000000 * lower_value) DIV
               (lower_denominator_minus_one + 1) +
             if (1000000000000 * lower_value) MOD
                  (lower_denominator_minus_one + 1) = 0
             then 0 else 1))),refs)` by
       (match_mp_tac
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            (Q.INST
              [`clock` |-> `clock - 1`,
               `other:cv` |->
                 `Pair (Pair (Num 0) (Num upper_value))
                   (Num upper_denominator_minus_one)`,
               `refs` |-> `refs`]
              registered_case10173_fs_of_q_lower_negative_fst_eval))
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_upper»
          [Uop Snd
            (Pair
              (Pair (Pair (Num 0) (Num lower_value))
                (Num lower_denominator_minus_one))
              (Pair (Pair (Num 0) (Num upper_value))
                (Num upper_denominator_minus_one)))]) refs =
      (M_success
        (Pair (Num 0)
          (Num
            ((1000000000000 * upper_value) DIV
             (upper_denominator_minus_one + 1)))),refs)` by
       (match_mp_tac
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            (Q.INST
              [`clock` |-> `clock - 1`,
               `other:cv` |->
                 `Pair (Pair (Num 0) (Num lower_value))
                   (Num lower_denominator_minus_one)`,
               `refs` |-> `refs`]
              registered_case10173_fs_of_q_upper_negative_snd_eval))
        >> intLib.ARITH_TAC)
  >> simp
       [compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_of_q_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
