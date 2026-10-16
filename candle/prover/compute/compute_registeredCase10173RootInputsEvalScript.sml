(*****************************************************************************
 * Registered evaluator semantics for the historical root-input calculation.
 *
 * This first layer covers the small exact carriers shared by the center and
 * box radicand calculations.  Keeping it separate from the completed root
 * certificate theory makes the remaining proof loop inexpensive.
 *****************************************************************************)
Theory compute_registeredCase10173RootInputsEval
Ancestors
  compute_registeredCase10173RootRecordEval
Libs
  bossLib preamble

Definition registered_case10173_fs_zero_body_def:
  registered_case10173_fs_zero_body =
    (Pair (Num 0) (Num 0) : compute_exp)
End

Definition registered_case10173_fs_interval_zero_body_def:
  registered_case10173_fs_interval_zero_body =
    Pair (App «candle_cv_fs_zero» []) (App «candle_cv_fs_zero» [])
End

Definition registered_case10173_fs_raw_scale_body_def:
  registered_case10173_fs_raw_scale_body =
    Pair (Binop Mul (Var «factor») (Uop Fst (Var «x»)))
      (Binop Mul (Var «factor») (Uop Snd (Var «x»)))
End

Definition registered_case10173_fs_angle_interval_scale_body_def:
  registered_case10173_fs_angle_interval_scale_body =
    Pair
      (App «candle_cv_fs_raw_scale»
        [Var «factor»;Uop Fst (Var «value»)])
      (App «candle_cv_fs_raw_scale»
        [Var «factor»;Uop Snd (Var «value»)])
End

Definition registered_case10173_fs_interval_lookup_body_def:
  registered_case10173_fs_interval_lookup_body =
    If (Uop Ispair (Var «items»))
      (If (Uop Ispair (Var «variable»))
        (App «candle_cv_fs_interval_zero» [])
        (If (Binop Eq (Var «variable») (Num 0))
          (Uop Fst (Var «items»))
          (App «candle_cv_fs_interval_lookup»
            [Binop Sub (Var «variable») (Num 1);
             Uop Snd (Var «items»)])))
      (App «candle_cv_fs_interval_zero» [])
End

Definition registered_case10173_fs_hist_second_value_body_def:
  registered_case10173_fs_hist_second_value_body =
    Uop Fst (Var «second»)
End

Theorem registered_case10173_fs_zero_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_zero» =
    SOME ([],registered_case10173_fs_zero_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_zero_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_zero» =
    SOME ([],registered_case10173_fs_interval_zero_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_scale» =
    SOME
      ([«factor»;«x»],registered_case10173_fs_raw_scale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_interval_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_interval_scale» =
    SOME
      ([«factor»;«value»],
       registered_case10173_fs_angle_interval_scale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_lookup_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_lookup» =
    SOME
      ([«variable»;«items»],
       registered_case10173_fs_interval_lookup_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_second_value_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_second_value» =
    SOME
      ([«second»],registered_case10173_fs_hist_second_value_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_scale_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_scale»
        [from_cv (Num factor);
         from_cv (Pair (Num positive) (Num negative))])
      (refs:hol_refs) =
    (M_success
      (Pair (Num (factor * positive)) (Num (factor * negative))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_raw_scale_lookup,
        registered_case10173_fs_raw_scale_body_def,
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

Theorem registered_case10173_fs_raw_scale_fst_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_scale»
        [from_cv (Num factor);
         Uop Fst
           (Pair
             (from_cv (Pair (Num positive) (Num negative)))
             (from_cv other))]) (refs:hol_refs) =
    (M_success
      (Pair (Num (factor * positive)) (Num (factor * negative))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_raw_scale_lookup,
        registered_case10173_fs_raw_scale_body_def,
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

Theorem registered_case10173_fs_raw_scale_snd_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_scale»
        [from_cv (Num factor);
         Uop Snd
           (Pair
             (from_cv other)
             (from_cv (Pair (Num positive) (Num negative))))])
      (refs:hol_refs) =
    (M_success
      (Pair (Num (factor * positive)) (Num (factor * negative))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_raw_scale_lookup,
        registered_case10173_fs_raw_scale_body_def,
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

Theorem registered_case10173_fs_angle_interval_scale_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale»
        [from_cv factor;from_cv value]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«factor»,from_cv factor);(«value»,from_cv value)]
        registered_case10173_fs_angle_interval_scale_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_angle_interval_scale_lookup]
QED

Theorem registered_case10173_fs_angle_interval_scale_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale»
        [from_cv (Num factor);
         from_cv
           (Pair
             (Pair (Num lower_positive) (Num lower_negative))
             (Pair (Num upper_positive) (Num upper_negative)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num (factor * lower_positive))
            (Num (factor * lower_negative)))
          (Pair
            (Num (factor * upper_positive))
            (Num (factor * upper_negative))))),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_angle_interval_scale_unfold]
  >> simp
       [registered_case10173_fs_angle_interval_scale_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_raw_scale_lookup,
        registered_case10173_fs_raw_scale_body_def,
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

Theorem registered_case10173_fs_hist_second_value_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_value»
        [from_cv (Pair value derivatives)]) (refs:hol_refs) =
    (M_success (from_cv value),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_second_value_lookup,
        registered_case10173_fs_hist_second_value_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_lookup_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [from_cv variable;from_cv items]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«variable»,from_cv variable);(«items»,from_cv items)]
        registered_case10173_fs_interval_lookup_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_interval_lookup_lookup]
QED

Theorem registered_case10173_fs_interval_lookup_head_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [from_cv (Num 0);from_cv (Pair item items)]) (refs:hol_refs) =
    (M_success (from_cv item),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_lookup_unfold]
  >> simp
       [registered_case10173_fs_interval_lookup_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_lookup_tail_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [from_cv (Num variable);from_cv items]) (refs:hol_refs) = result ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [from_cv (Num (SUC variable));from_cv (Pair item items)]) refs =
    result
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_lookup_unfold]
  >> fs
       [registered_case10173_fs_interval_lookup_body_def,
        registered_case10173_fs_interval_lookup_unfold,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> gvs []
QED

val _ = export_theory ();
