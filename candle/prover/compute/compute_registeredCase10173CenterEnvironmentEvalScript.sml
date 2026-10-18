(*****************************************************************************
 * Registered evaluator semantics for the exact rational center environment.
 *
 * The historical checker derives a point box at each source-box midpoint
 * before converting it to the decimal fixed-scale carrier.  This theory
 * keeps that derivation tied to the literal registered CakeML source.
 *****************************************************************************)
Theory compute_registeredCase10173CenterEnvironmentEval
Ancestors
  compute_registeredCase10173QConversionEval
  compute_registeredCase10173CenterEnvironmentObject
Libs
  bossLib preamble

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
    Binop Add (Binop Add (Var «d1») (Var «d2»))
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
      (App «candle_cv_q_zmul» [Uop Fst (Var «x»);Uop Fst (Var «y»)])
      (App «candle_cv_q_den_product_pred»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Definition registered_case10173_q_half_body_def:
  registered_case10173_q_half_body =
    (Pair (Pair (Num 1) (Num 0)) (Num 1) : compute_exp)
End

Definition registered_case10173_q_midpoint_body_def:
  registered_case10173_q_midpoint_body =
    App «candle_cv_q_mul»
      [App «candle_cv_q_half» [];
       App «candle_cv_q_add»
         [Uop Fst (Var «i»);Uop Snd (Var «i»)]]
End

Definition registered_case10173_q_point_interval_body_def:
  registered_case10173_q_point_interval_body =
    Pair (Var «q») (Var «q»)
End

Definition registered_case10173_q_center_environment_list_body_def:
  registered_case10173_q_center_environment_list_body =
    If (Uop Ispair (Var «boxes»))
      (Pair
        (App «candle_cv_q_point_interval»
          [App «candle_cv_q_midpoint» [Uop Fst (Var «boxes»)]])
        (App «candle_cv_q_center_environment_list»
          [Uop Snd (Var «boxes»)]))
      (Num 0)
End

val registered_case10173_q_midpoint_positive_cv_def =
  save_thm
    ("registered_case10173_q_midpoint_positive_cv_def",
     compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_midpoint_positive_cv_def);

val registered_case10173_q_center_environment_positive_def =
  save_thm
    ("registered_case10173_q_center_environment_positive_def",
     compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_center_environment_positive_def);

Theorem registered_case10173_lc_zadd_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_lc_zadd» =
    SOME ([«x»;«y»],registered_case10173_lc_zadd_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_lc_zscale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_lc_zscale» =
    SOME ([«k»;«x»],registered_case10173_lc_zscale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_den_product_pred_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_den_product_pred» =
    SOME
      ([«d1»;«d2»],registered_case10173_q_den_product_pred_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_zmul_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_zmul» =
    SOME ([«x»;«y»],registered_case10173_q_zmul_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_add» =
    SOME ([«x»;«y»],registered_case10173_q_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_mul_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_mul» =
    SOME ([«x»;«y»],registered_case10173_q_mul_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_half_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_half» =
    SOME ([],registered_case10173_q_half_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_midpoint_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_midpoint» =
    SOME ([«i»],registered_case10173_q_midpoint_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_point_interval_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_point_interval» =
    SOME ([«q»],registered_case10173_q_point_interval_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_center_environment_list_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_center_environment_list» =
    SOME
      ([«boxes»],registered_case10173_q_center_environment_list_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_midpoint_positive_eval:
  5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_midpoint»
        [from_cv
          (Pair
            (Pair (Pair (Num lower_value) (Num 0))
              (Num lower_denominator_minus_one))
            (Pair (Pair (Num upper_value) (Num 0))
              (Num upper_denominator_minus_one)))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_q_midpoint_positive_cv
          lower_value lower_denominator_minus_one
          upper_value upper_denominator_minus_one)),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_midpoint_lookup,
        registered_case10173_q_midpoint_body_def,
        registered_case10173_q_mul_lookup,
        registered_case10173_q_mul_body_def,
        registered_case10173_q_half_lookup,
        registered_case10173_q_half_body_def,
        registered_case10173_q_add_lookup,
        registered_case10173_q_add_body_def,
        registered_case10173_q_zmul_lookup,
        registered_case10173_q_zmul_body_def,
        registered_case10173_lc_zadd_lookup,
        registered_case10173_lc_zadd_body_def,
        registered_case10173_lc_zscale_lookup,
        registered_case10173_lc_zscale_body_def,
        registered_case10173_q_den_product_pred_lookup,
        registered_case10173_q_den_product_pred_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
        registered_case10173_q_midpoint_positive_cv_def,
        LET_THM,
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
QED

Theorem registered_case10173_q_point_interval_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_point_interval» [from_cv q]) (refs:hol_refs) =
    (M_success (from_cv (Pair q q)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_point_interval_lookup,
        registered_case10173_q_point_interval_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_center_environment_list_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_center_environment_list» [from_cv boxes])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«boxes»,from_cv boxes)]
        registered_case10173_q_center_environment_list_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_q_center_environment_list_lookup]
QED

Theorem registered_case10173_q_center_environment_list_nil_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_center_environment_list» [from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success (Num 0),refs)
Proof
  strip_tac
  >> simp [registered_case10173_q_center_environment_list_unfold]
  >> simp
       [registered_case10173_q_center_environment_list_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_center_environment_list_cons_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_midpoint» [from_cv interval])
      (refs:hol_refs) =
    (M_success (from_cv midpoint),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_center_environment_list» [from_cv boxes]) refs =
    (M_success (from_cv centers),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_center_environment_list»
        [from_cv (Pair interval boxes)]) refs =
    (M_success
      (from_cv (Pair (Pair midpoint midpoint) centers)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_q_center_environment_list_unfold]
  >> simp
       [registered_case10173_q_center_environment_list_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_midpoint»
          [Uop Fst (Pair (from_cv interval) (from_cv boxes))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_midpoint» [from_cv interval]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_point_interval»
          [App «candle_cv_q_midpoint»
            [Uop Fst (Pair (from_cv interval) (from_cv boxes))]]) refs =
      (M_success (from_cv (Pair midpoint midpoint)),refs)` by
       (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_point_interval»
            [App «candle_cv_q_midpoint»
              [Uop Fst (Pair (from_cv interval) (from_cv boxes))]]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_point_interval» [from_cv midpoint]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> simp [])
        >> simp [registered_case10173_q_point_interval_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_center_environment_list»
          [Uop Snd (Pair (from_cv interval) (from_cv boxes))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_center_environment_list» [from_cv boxes]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_center_environment_positive_eval:
  !boxes centers clock refs.
    registered_case10173_q_center_environment_positive boxes = SOME centers /\
    8 * (cv_size boxes + 1) < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_center_environment_list» [from_cv boxes])
        (refs:hol_refs) =
      (M_success (from_cv centers),refs)
Proof
  ho_match_mp_tac registered_case10173_q_center_environment_positive_ind
  >> rw [registered_case10173_q_center_environment_positive_def]
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_q_center_environment_list_nil_eval)
      >> intLib.ARITH_TAC)
  >> Cases_on
       `registered_case10173_q_center_environment_positive boxes`
  >> gvs []
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`interval` |->
              `Pair
                (Pair (Pair (Num lower_value) (Num 0))
                  (Num lower_denominator_minus_one))
                (Pair (Pair (Num upper_value) (Num 0))
                  (Num upper_denominator_minus_one))`,
            `midpoint` |->
              `registered_case10173_q_midpoint_positive_cv
                lower_value lower_denominator_minus_one
                upper_value upper_denominator_minus_one`]
           registered_case10173_q_center_environment_list_cons_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >> FIRST
       [irule
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            (Q.INST
              [`clock` |-> `clock - 1`,
               `lower_value` |-> `lower_value`,
               `lower_denominator_minus_one` |->
                 `lower_denominator_minus_one`,
               `upper_value` |-> `upper_value`,
               `upper_denominator_minus_one` |->
                 `upper_denominator_minus_one`,
               `refs` |-> `refs`]
              registered_case10173_q_midpoint_positive_eval))
        >> intLib.ARITH_TAC,
        qpat_x_assum `!clock' refs. _`
          (qspecl_then [`clock - 1`,`refs`] match_mp_tac)
        >> fs []
        >> intLib.ARITH_TAC]
QED

Theorem registered_case10173_center_environment_decimal_eval:
  registered_case10173_q_center_environment_positive boxes =
      SOME center_boxes /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME center_environment /\
  8 * (cv_size boxes + 1) < clock /\
  11 * (LENGTH center_environment + 1) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_of_q»
        [App «candle_cv_q_center_environment_list» [from_cv boxes]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv_list center_environment)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_center_environment_list» [from_cv boxes]) refs =
      (M_success (from_cv center_boxes),refs)` by
       simp [registered_case10173_q_center_environment_positive_eval]
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_of_q»
          [App «candle_cv_q_center_environment_list» [from_cv boxes]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_of_q»
          [from_cv center_boxes]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp []
        >> intLib.ARITH_TAC)
  >> simp
       [compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_list_of_q_object_eval]
QED

val _ = export_theory ();
