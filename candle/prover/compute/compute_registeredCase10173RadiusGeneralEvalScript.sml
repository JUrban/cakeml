(*****************************************************************************
 * Packet-independent evaluator refinement for registered source radii.
 *
 * This layer connects the literal rational radius preparation in the
 * registered source to the exact word radii authenticated by the fast
 * packet.  The individual arithmetic lemmas are intentionally symbolic;
 * no closed cell fixture or per-cell evaluator replay is used.
 *****************************************************************************)
Theory compute_registeredCase10173RadiusGeneralEval
Ancestors
  compute_registeredCase10173RadiusBinding
  compute_registeredCase10173QConversionEval
  compute_registeredCase10173RadiiEval
Libs
  bossLib preamble intLib

Definition registered_case10173_lc_zadd_body_def:
  registered_case10173_lc_zadd_body =
    Pair
      (Binop Add (Uop Fst (Var «x»)) (Uop Fst (Var «y»)))
      (Binop Add (Uop Snd (Var «x»)) (Uop Snd (Var «y»)))
End

Definition registered_case10173_lc_zscale_body_def:
  registered_case10173_lc_zscale_body =
    Pair
      (Binop Mul (Var «k») (Uop Fst (Var «x»)))
      (Binop Mul (Var «k») (Uop Snd (Var «x»)))
End

Definition registered_case10173_q_den_product_pred_body_def:
  registered_case10173_q_den_product_pred_body =
    Binop Add
      (Binop Add (Var «d1») (Var «d2»))
      (Binop Mul (Var «d1») (Var «d2»))
End

Definition registered_case10173_q_zmul_body_def:
  registered_case10173_q_zmul_body =
    Pair
      (Binop Add
        (Binop Mul (Uop Fst (Var «x»)) (Uop Fst (Var «y»)))
        (Binop Mul (Uop Snd (Var «x»)) (Uop Snd (Var «y»))))
      (Binop Add
        (Binop Mul (Uop Fst (Var «x»)) (Uop Snd (Var «y»)))
        (Binop Mul (Uop Snd (Var «x»)) (Uop Fst (Var «y»))))
End

Definition registered_case10173_q_add_body_def:
  registered_case10173_q_add_body =
    Pair
      (App «candle_cv_lc_zadd»
        [App «candle_cv_lc_zscale»
          [App «candle_cv_q_den» [Var «y»];Uop Fst (Var «x»)];
         App «candle_cv_lc_zscale»
          [App «candle_cv_q_den» [Var «x»];Uop Fst (Var «y»)]])
      (App «candle_cv_q_den_product_pred»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Definition registered_case10173_q_mul_body_def:
  registered_case10173_q_mul_body =
    Pair
      (App «candle_cv_q_zmul»
        [Uop Fst (Var «x»);Uop Fst (Var «y»)])
      (App «candle_cv_q_den_product_pred»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Definition registered_case10173_q_neg_body_def:
  registered_case10173_q_neg_body =
    Pair
      (Pair
        (Uop Snd (Uop Fst (Var «x»)))
        (Uop Fst (Uop Fst (Var «x»))))
      (Uop Snd (Var «x»))
End

Definition registered_case10173_q_half_body_def:
  registered_case10173_q_half_body =
    (Pair (Pair (Num 1) (Num 0)) (Num 1) : compute_exp)
End

Definition registered_case10173_q_radius_body_def:
  registered_case10173_q_radius_body =
    App «candle_cv_q_mul»
      [App «candle_cv_q_half» [];
       App «candle_cv_q_add»
        [Uop Snd (Var «i»);
         App «candle_cv_q_neg» [Uop Fst (Var «i»)]]]
End

Definition registered_case10173_q_radius_list_body_def:
  registered_case10173_q_radius_list_body =
    If (Uop Ispair (Var «boxes»))
      (Pair
        (App «candle_cv_q_radius» [Uop Fst (Var «boxes»)])
        (App «candle_cv_q_radius_list» [Uop Snd (Var «boxes»)]))
      (Num 0)
End

Definition registered_case10173_q_fixed_list_round_upper_body_def:
  registered_case10173_q_fixed_list_round_upper_body =
    If (Uop Ispair (Var «items»))
      (Pair
        (App «candle_cv_q_fixed_round_upper» [Uop Fst (Var «items»)])
        (App «candle_cv_q_fixed_list_round_upper» [Uop Snd (Var «items»)]))
      (Num 0)
End

Theorem registered_case10173_radius_helper_lookups:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_lc_zadd» =
    SOME ([«x»;«y»],registered_case10173_lc_zadd_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_lc_zscale» =
    SOME ([«k»;«x»],registered_case10173_lc_zscale_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_den_product_pred» =
    SOME
      ([«d1»;«d2»],registered_case10173_q_den_product_pred_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_zmul» =
    SOME ([«x»;«y»],registered_case10173_q_zmul_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_add» =
    SOME ([«x»;«y»],registered_case10173_q_add_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_mul» =
    SOME ([«x»;«y»],registered_case10173_q_mul_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_neg» =
    SOME ([«x»],registered_case10173_q_neg_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_half» =
    SOME ([],registered_case10173_q_half_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_radius» =
    SOME ([«i»],registered_case10173_q_radius_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_radius_list» =
    SOME ([«boxes»],registered_case10173_q_radius_list_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_fixed_list_round_upper» =
    SOME
      ([«items»],registered_case10173_q_fixed_list_round_upper_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_radius_positive_eval:
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_radius»
        [from_cv
          (Pair
            (Pair (Pair (Num lower_value) (Num 0))
              (Num lower_denominator_minus_one))
            (Pair (Pair (Num upper_value) (Num 0))
              (Num upper_denominator_minus_one)))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num (upper_value * (lower_denominator_minus_one + 1)))
            (Num (lower_value * (upper_denominator_minus_one + 1))))
          (Num
            (1 + 2 *
              (lower_denominator_minus_one +
               upper_denominator_minus_one +
               lower_denominator_minus_one *
                 upper_denominator_minus_one))))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_radius_helper_lookups,
        registered_case10173_lc_zadd_body_def,
        registered_case10173_lc_zscale_body_def,
        registered_case10173_q_den_product_pred_body_def,
        registered_case10173_q_zmul_body_def,
        registered_case10173_q_add_body_def,
        registered_case10173_q_mul_body_def,
        registered_case10173_q_neg_body_def,
        registered_case10173_q_half_body_def,
        registered_case10173_q_radius_body_def,
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
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_q_fixed_round_upper_nonnegative_eval:
  negative <= positive /\
  7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_round_upper»
        [from_cv
          (Pair (Pair (Num positive) (Num negative))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              ((1000000000000 * (positive - negative)) DIV
                 (denominator_minus_one + 1) +
               if (1000000000000 * (positive - negative)) MOD
                    (denominator_minus_one + 1) = 0
               then 0 else 1))
            (Num 0))
          (Num 999999999999))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_upper_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_upper_body_def,
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
       `(1000000000000 * (positive - negative)) MOD
          (denominator_minus_one + 1) = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_radius_fixed_positive_eval:
  lower_value * (upper_denominator_minus_one + 1) <=
      upper_value * (lower_denominator_minus_one + 1) /\
  bounded_decimal_natural_ceil64
      (upper_value * (lower_denominator_minus_one + 1) -
       lower_value * (upper_denominator_minus_one + 1))
      (2 *
        (lower_denominator_minus_one +
         upper_denominator_minus_one +
         lower_denominator_minus_one *
           upper_denominator_minus_one) + 2) = SOME radius /\
  30 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_round_upper»
        [App «candle_cv_q_radius»
          [from_cv
            (Pair
              (Pair (Pair (Num lower_value) (Num 0))
                (Num lower_denominator_minus_one))
              (Pair (Pair (Num upper_value) (Num 0))
                (Num upper_denominator_minus_one)))]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (bounded_word64_object_cv radius)
          (Num 999999999999))),refs)
Proof
  rpt strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_fixed_round_upper»
          [App «candle_cv_q_radius»
            [from_cv
              (Pair
                (Pair (Pair (Num lower_value) (Num 0))
                  (Num lower_denominator_minus_one))
                (Pair (Pair (Num upper_value) (Num 0))
                  (Num upper_denominator_minus_one)))]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_fixed_round_upper»
          [from_cv
            (Pair
              (Pair
                (Num
                  (upper_value *
                    (lower_denominator_minus_one + 1)))
                (Num
                  (lower_value *
                    (upper_denominator_minus_one + 1))))
              (Num
                (1 + 2 *
                  (lower_denominator_minus_one +
                   upper_denominator_minus_one +
                   lower_denominator_minus_one *
                     upper_denominator_minus_one))))]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp [registered_case10173_q_radius_positive_eval])
  >> qpat_x_assum
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_fixed_round_upper»
            [App «candle_cv_q_radius» _]) refs = _`
       SUBST1_TAC
  >> mp_tac
       (Q.INST
         [`negative` |->
            `lower_value * (upper_denominator_minus_one + 1)`,
          `positive` |->
            `upper_value * (lower_denominator_minus_one + 1)`,
          `denominator_minus_one` |->
            `1 + 2 *
              (lower_denominator_minus_one +
               upper_denominator_minus_one +
               lower_denominator_minus_one *
                 upper_denominator_minus_one)`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         registered_case10173_q_fixed_round_upper_nonnegative_eval)
  >> impl_tac >- simp []
  >> disch_then assume_tac
  >> fs
       [compute_execTheory.from_cv_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_word64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> imp_res_tac
       compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_value
  >> mp_tac
       (Q.INST
         [`value` |->
            `1000000000000 *
              (upper_value * (lower_denominator_minus_one + 1) -
               lower_value * (upper_denominator_minus_one + 1))`,
          `divisor` |->
            `2 *
              (lower_denominator_minus_one +
               upper_denominator_minus_one +
               lower_denominator_minus_one *
                 upper_denominator_minus_one) + 2`]
         compute_boundedSignedTheory.bounded_div_ceil)
  >> simp []
  >> metis_tac [arithmeticTheory.MULT_COMM,
                arithmeticTheory.ADD_COMM]
QED

Definition registered_case10173_source_radius_q_def:
  registered_case10173_source_radius_q
      (Pair
        (Pair (Pair (Num lower_value) (Num 0))
          (Num lower_denominator_minus_one))
        (Pair (Pair (Num upper_value) (Num 0))
          (Num upper_denominator_minus_one)) : cv) =
    (Pair
       (Num (upper_value * (lower_denominator_minus_one + 1)))
       (Num (lower_value * (upper_denominator_minus_one + 1))),
     Num
       (1 + 2 *
         (lower_denominator_minus_one +
          upper_denominator_minus_one +
          lower_denominator_minus_one *
            upper_denominator_minus_one))) /\
  registered_case10173_source_radius_q _ = (Num 0,Num 0)
End

Definition registered_case10173_source_radius_q_list_def:
  registered_case10173_source_radius_q_list (Num 0 : cv) = [] /\
  registered_case10173_source_radius_q_list (Pair interval intervals) =
    registered_case10173_source_radius_q interval::
      registered_case10173_source_radius_q_list intervals /\
  registered_case10173_source_radius_q_list _ = []
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Theorem bounded_case10173_source_radius64_positive_q_components:
  bounded_case10173_source_radius64_positive_q interval = SOME radius ==>
  ?lower_value lower_denominator_minus_one
   upper_value upper_denominator_minus_one.
    interval =
      Pair
        (Pair (Pair (Num lower_value) (Num 0))
          (Num lower_denominator_minus_one))
        (Pair (Pair (Num upper_value) (Num 0))
          (Num upper_denominator_minus_one)) /\
    lower_value * (upper_denominator_minus_one + 1) <=
      upper_value * (lower_denominator_minus_one + 1) /\
    bounded_decimal_natural_ceil64
      (upper_value * (lower_denominator_minus_one + 1) -
       lower_value * (upper_denominator_minus_one + 1))
      (2 *
        (lower_denominator_minus_one +
         upper_denominator_minus_one +
         lower_denominator_minus_one *
           upper_denominator_minus_one) + 2) = SOME radius
Proof
  Cases_on `interval`
  >- simp
       [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def]
  >> rename1 `Pair lower_cv upper_cv`
  >> Cases_on `lower_cv`
  >- simp
       [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def]
  >> rename1 `Pair (Pair lower_z lower_den) upper_cv`
  >> Cases_on `lower_z`
  >- simp
       [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def]
  >> rename1
       `Pair (Pair (Pair lower_pos lower_neg) lower_den) upper_cv`
  >> Cases_on `upper_cv`
  >- simp
       [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def]
  >> rename1
       `Pair (Pair (Pair lower_pos lower_neg) lower_den)
          (Pair upper_z upper_den)`
  >> Cases_on `upper_z`
  >- simp
       [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def]
  >> rename1
       `Pair (Pair (Pair lower_pos lower_neg) lower_den)
          (Pair (Pair upper_pos upper_neg) upper_den)`
  >> Cases_on `upper_pos`
  >> TRY
       (simp
         [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def])
  >> Cases_on `upper_neg`
  >> TRY
       (simp
         [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def])
  >> Cases_on `upper_den`
  >> TRY
       (simp
         [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def])
  >> Cases_on `lower_pos`
  >> TRY
       (simp
         [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def])
  >> Cases_on `lower_neg`
  >> TRY
       (simp
         [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def])
  >> Cases_on `lower_den`
  >> TRY
       (simp
         [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def])
  >> rename1
       `bounded_case10173_source_radius64_positive_q
          (Pair
            (Pair (Pair (Num lower_value) (Num lower_negative))
              (Num lower_denominator_minus_one))
            (Pair (Pair (Num upper_value) (Num upper_negative))
              (Num upper_denominator_minus_one))) = SOME radius`
  >> Cases_on `lower_negative`
  >> TRY
       (simp
         [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def])
  >> Cases_on `upper_negative`
  >> TRY
       (simp
         [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def])
  >> simp [arithmeticTheory.ADD1]
  >> strip_tac
  >> `2 *
        ((lower_denominator_minus_one + 1) *
         (upper_denominator_minus_one + 1)) =
      2 *
        (lower_denominator_minus_one +
         (upper_denominator_minus_one +
          lower_denominator_minus_one *
            upper_denominator_minus_one)) + 2` by
       intLib.ARITH_TAC
  >> pop_assum (fn th => once_rewrite_tac [GSYM th])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_q_radius_list_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_radius_list» [from_cv boxes])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«boxes»,from_cv boxes)]
        registered_case10173_q_radius_list_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_radius_helper_lookups]
QED

Theorem registered_case10173_q_radius_list_source_eval:
  !boxes radii clock refs.
    bounded_case10173_source_radii64_positive_q boxes = SOME radii /\
    LENGTH radii + 32 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_radius_list» [from_cv boxes])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (registered_case10173_q_cv_list
            (registered_case10173_source_radius_q_list boxes))),refs)
Proof
  Induct_on `boxes`
  >- (rpt strip_tac
      >> Cases_on `n`
      >> rw [registered_case10173_q_radius_list_unfold]
      >> gvs
           [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radii64_positive_q_def,
            registered_case10173_source_radius_q_list_def,
            compute_registeredCase10173RadiiEvalTheory.registered_case10173_q_cv_list_def]
      >> simp
           [registered_case10173_q_radius_list_body_def,
            compute_evalTheory.subst_def,
            compute_execTheory.from_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> rw [registered_case10173_q_radius_list_unfold]
  >> Cases_on
       `bounded_case10173_source_radius64_positive_q boxes`
  >> gvs
       [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radii64_positive_q_def]
  >> Cases_on
       `bounded_case10173_source_radii64_positive_q boxes'`
  >> gvs
       [compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radii64_positive_q_def]
  >> imp_res_tac
       bounded_case10173_source_radius64_positive_q_components
  >> gvs []
  >> simp
       [registered_case10173_q_radius_list_body_def,
        compute_evalTheory.subst_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`left` |->
              `Pair
                (Pair (Pair (Num lower_value) (Num 0))
                  (Num lower_denominator_minus_one))
                (Pair (Pair (Num upper_value) (Num 0))
                  (Num upper_denominator_minus_one))`,
             `right` |-> `boxes'`]
            compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components)]
  >> simp
       [registered_case10173_source_radius_q_list_def,
        registered_case10173_source_radius_q_def,
        compute_registeredCase10173RadiiEvalTheory.registered_case10173_q_cv_list_def]
  >> `2 *
        (lower_denominator_minus_one +
         (upper_denominator_minus_one +
          lower_denominator_minus_one * upper_denominator_minus_one)) + 1 =
      1 + 2 *
        (lower_denominator_minus_one + upper_denominator_minus_one +
         lower_denominator_minus_one * upper_denominator_minus_one)` by
       intLib.ARITH_TAC
  >> pop_assum (fn th => once_rewrite_tac [th])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
            [`left_result` |->
              `Pair
                (Pair
                  (Num
                    (upper_value *
                      (lower_denominator_minus_one + 1)))
                  (Num
                    (lower_value *
                      (upper_denominator_minus_one + 1))))
                (Num
                  (1 + 2 *
                    (lower_denominator_minus_one +
                     upper_denominator_minus_one +
                     lower_denominator_minus_one *
                       upper_denominator_minus_one)))`,
            `right_result` |->
              `registered_case10173_q_cv_list
                (registered_case10173_source_radius_q_list boxes')`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_radius»
            [Uop Fst
              (Pair
                (Pair
                  (Pair (Pair (Num lower_value) (Num 0))
                    (Num lower_denominator_minus_one))
                  (Pair (Pair (Num upper_value) (Num 0))
                    (Num upper_denominator_minus_one)))
                (from_cv boxes'))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_radius»
            [from_cv
              (Pair
                (Pair (Pair (Num lower_value) (Num 0))
                  (Num lower_denominator_minus_one))
                (Pair (Pair (Num upper_value) (Num 0))
                  (Num upper_denominator_minus_one)))]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                (Q.INST
                  [`left` |->
                    `Pair
                      (Pair (Pair (Num lower_value) (Num 0))
                        (Num lower_denominator_minus_one))
                      (Pair (Pair (Num upper_value) (Num 0))
                        (Num upper_denominator_minus_one))`,
                   `right` |-> `boxes'`]
                  compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components)]
        >> intLib.ARITH_TAC)
      >> qpat_x_assum
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_q_radius» [Uop Fst _]) refs = _`
           (fn th => once_rewrite_tac [th])
      >> simp [compute_execTheory.from_cv_def]
      >> `2 *
            (lower_denominator_minus_one +
             (upper_denominator_minus_one +
              lower_denominator_minus_one * upper_denominator_minus_one)) + 1 =
          1 + 2 *
            (lower_denominator_minus_one + upper_denominator_minus_one +
             lower_denominator_minus_one * upper_denominator_minus_one)` by
           intLib.ARITH_TAC
      >> qpat_x_assum
           `2 *
              (lower_denominator_minus_one +
               (upper_denominator_minus_one +
                lower_denominator_minus_one * upper_denominator_minus_one)) + 1 = _`
           (fn th => once_rewrite_tac [th])
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_q_radius_positive_eval)
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_radius_list»
          [Uop Snd
            (Pair
              (Pair
                (Pair (Pair (Num lower_value) (Num 0))
                  (Num lower_denominator_minus_one))
                (Pair (Pair (Num upper_value) (Num 0))
                  (Num upper_denominator_minus_one)))
              (from_cv boxes'))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_radius_list» [from_cv boxes']) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                (Q.INST
                  [`left` |->
                    `Pair
                      (Pair (Pair (Num lower_value) (Num 0))
                        (Num lower_denominator_minus_one))
                      (Pair (Pair (Num upper_value) (Num 0))
                        (Num upper_denominator_minus_one))`,
                   `right` |-> `boxes'`]
                  compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components)]
        >> intLib.ARITH_TAC)
  >> qpat_x_assum
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_radius_list» [Uop Snd _]) refs = _`
       (fn th => once_rewrite_tac [th])
  >> qpat_x_assum
       `!clock' refs. LENGTH x' + 32 < clock' ==> _`
       (fn th => irule th)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
