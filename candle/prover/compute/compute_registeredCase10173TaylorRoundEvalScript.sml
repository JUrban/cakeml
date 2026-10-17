(*****************************************************************************
 * Registered evaluator refinement for interval assembly and directed
 * fixed-scale rounding used by Taylor value and gradient completion.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorRoundEval
Ancestors
  compute_registeredCase10173TaylorWeightedRowsEval
Libs
  bossLib preamble

Definition registered_case10173_fs_raw_interval_add_body_def:
  registered_case10173_fs_raw_interval_add_body =
    Pair
      (App «candle_cv_fs_raw_add»
        [Uop Fst (Var «x»);Uop Fst (Var «y»)])
      (App «candle_cv_fs_raw_add»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Definition registered_case10173_fs_floor_div_body_def:
  registered_case10173_fs_floor_div_body =
    If (Binop Less (Uop Fst (Var «x»)) (Uop Snd (Var «x»)))
      (Pair (Num 0)
        (App «candle_cv_q_ceil_div»
          [Binop Sub (Uop Snd (Var «x»)) (Uop Fst (Var «x»));
           Var «denominator»]))
      (Pair
        (Binop Div (Binop Sub (Uop Fst (Var «x»))
          (Uop Snd (Var «x»))) (Var «denominator»))
        (Num 0))
End

Definition registered_case10173_fs_ceil_div_body_def:
  registered_case10173_fs_ceil_div_body =
    If (Binop Less (Uop Fst (Var «x»)) (Uop Snd (Var «x»)))
      (Pair (Num 0)
        (Binop Div (Binop Sub (Uop Snd (Var «x»))
          (Uop Fst (Var «x»))) (Var «denominator»)))
      (Pair
        (App «candle_cv_q_ceil_div»
          [Binop Sub (Uop Fst (Var «x»)) (Uop Snd (Var «x»));
           Var «denominator»])
        (Num 0))
End

Definition registered_case10173_fs_raw_interval_round_body_def:
  registered_case10173_fs_raw_interval_round_body =
    Pair
      (App «candle_cv_fs_floor_div»
        [Uop Fst (Var «i»);Var «denominator»])
      (App «candle_cv_fs_ceil_div»
        [Uop Snd (Var «i»);Var «denominator»])
End

Theorem registered_case10173_fs_raw_interval_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_interval_add» =
    SOME ([«x»;«y»],registered_case10173_fs_raw_interval_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_floor_div_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_floor_div» =
    SOME ([«x»;«denominator»],registered_case10173_fs_floor_div_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_ceil_div_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_ceil_div» =
    SOME ([«x»;«denominator»],registered_case10173_fs_ceil_div_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_interval_round_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_interval_round» =
    SOME
      ([«denominator»;«i»],
       registered_case10173_fs_raw_interval_round_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_interval_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_add»
        [from_cv encoded_left;from_cv encoded_right])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«x»,from_cv encoded_left);(«y»,from_cv encoded_right)]
        registered_case10173_fs_raw_interval_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_interval_add_lookup]
QED

Theorem registered_case10173_fs_raw_interval_add_eval:
  bounded_object_fs_raw_interval_add left right = SOME result /\
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_add»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_interval_add_def]
  >> Cases_on `bounded_object_fs_raw_add c c'`
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_interval_add_def]
  >> Cases_on `bounded_object_fs_raw_add c0 c0'`
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_interval_add_def]
  >> strip_tac
  >> gvs []
  >> simp
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`encoded_left` |-> `(Pair c c0:cv)`,
             `encoded_right` |-> `(Pair c' c0':cv)`]
            registered_case10173_fs_raw_interval_add_unfold))]
  >> simp
       [registered_case10173_fs_raw_interval_add_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_add»
          [Uop Fst (Pair (from_cv c) (from_cv c0));
           Uop Fst (Pair (from_cv c') (from_cv c0'))]) refs =
      (M_success (from_cv x),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_add»
             [Uop Fst (Pair (from_cv c) (from_cv c0));
              Uop Fst (Pair (from_cv c') (from_cv c0'))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_add» [from_cv c;from_cv c']) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> fs
             [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_add_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_add»
          [Uop Snd (Pair (from_cv c) (from_cv c0));
           Uop Snd (Pair (from_cv c') (from_cv c0'))]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_add»
             [Uop Snd (Pair (from_cv c) (from_cv c0));
              Uop Snd (Pair (from_cv c') (from_cv c0'))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_add» [from_cv c0;from_cv c0']) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> fs
             [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_add_eval])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> simp []
QED

Theorem registered_case10173_fs_floor_div_pair_eval:
  0 < denominator /\ 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_floor_div»
        [from_cv (Pair (Num positive) (Num negative));
         from_cv (Num denominator)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (if positive < negative then
           Pair (Num 0)
             (Num
               (bounded_object_q_ceil_div
                 (negative - positive) denominator))
         else
           Pair (Num ((positive - negative) DIV denominator))
             (Num 0))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_floor_div_lookup,
        registered_case10173_fs_floor_div_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_body_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_def,
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
  >> Cases_on `positive < negative`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `(negative - positive) MOD denominator = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_ceil_div_pair_eval:
  0 < denominator /\ 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_ceil_div»
        [from_cv (Pair (Num positive) (Num negative));
         from_cv (Num denominator)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (if positive < negative then
           Pair (Num 0)
             (Num ((negative - positive) DIV denominator))
         else
           Pair
             (Num
               (bounded_object_q_ceil_div
                 (positive - negative) denominator))
             (Num 0))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_ceil_div_lookup,
        registered_case10173_fs_ceil_div_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_body_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_def,
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
  >> Cases_on `positive < negative`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `(positive - negative) MOD denominator = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_floor_div_eval:
  bounded_object_fs_floor_div source denominator = SOME result /\
  0 < denominator /\ 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_floor_div»
        [from_cv source;from_cv (Num denominator)]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `source`
  >> gvs
       [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> gvs
       [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def]
  >> Cases_on `n < n'`
  >> gvs
       [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def]
  >> rpt strip_tac
  >> gvs []
  >> mp_tac
       (Q.INST [`positive` |-> `n`, `negative` |-> `n'`]
         registered_case10173_fs_floor_div_pair_eval)
  >> simp []
QED

Theorem registered_case10173_fs_ceil_div_eval:
  bounded_object_fs_ceil_div source denominator = SOME result /\
  0 < denominator /\ 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_ceil_div»
        [from_cv source;from_cv (Num denominator)]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `source`
  >> gvs
       [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> gvs
       [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def]
  >> Cases_on `n < n'`
  >> gvs
       [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def]
  >> rpt strip_tac
  >> gvs []
  >> mp_tac
       (Q.INST [`positive` |-> `n`, `negative` |-> `n'`]
         registered_case10173_fs_ceil_div_pair_eval)
  >> simp []
QED

Theorem registered_case10173_fs_raw_interval_round_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_round»
        [from_cv (Num denominator);from_cv encoded_interval])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«denominator»,from_cv (Num denominator));
         («i»,from_cv encoded_interval)]
        registered_case10173_fs_raw_interval_round_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_interval_round_lookup]
QED

Theorem registered_case10173_fs_raw_interval_round_eval:
  bounded_object_fs_raw_interval_round denominator interval = SOME result /\
  0 < denominator /\ 10 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_round»
        [from_cv (Num denominator);from_cv interval]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `interval`
  >> gvs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_def]
  >> Cases_on `bounded_object_fs_floor_div c denominator`
  >> gvs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_def]
  >> Cases_on `bounded_object_fs_ceil_div c0 denominator`
  >> gvs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_def]
  >> rpt strip_tac
  >> gvs []
  >> simp
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`encoded_interval` |-> `(Pair c c0:cv)`]
            registered_case10173_fs_raw_interval_round_unfold))]
  >> simp
       [registered_case10173_fs_raw_interval_round_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_floor_div»
          [Uop Fst (Pair (from_cv c) (from_cv c0));Num denominator]) refs =
      (M_success (from_cv x),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_floor_div»
             [Uop Fst (Pair (from_cv c) (from_cv c0));
              Num denominator]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_floor_div»
             [from_cv c;from_cv (Num denominator)]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> conj_tac
           >- simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
           >> simp
                [compute_evalTheory.compute_eval_def,
                 ml_monadBaseTheory.st_ex_return_def])
        >> `5 < clock - 1` by intLib.ARITH_TAC
        >> mp_tac
             (Q.INST
               [`source` |-> `c`, `clock` |-> `clock - 1`,
                `result` |-> `x`]
               registered_case10173_fs_floor_div_eval)
        >> simp [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_ceil_div»
          [Uop Snd (Pair (from_cv c) (from_cv c0));Num denominator]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_ceil_div»
             [Uop Snd (Pair (from_cv c) (from_cv c0));
              Num denominator]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_ceil_div»
             [from_cv c0;from_cv (Num denominator)]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> conj_tac
           >- simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
           >> simp
                [compute_evalTheory.compute_eval_def,
                 ml_monadBaseTheory.st_ex_return_def])
        >> `5 < clock - 1` by intLib.ARITH_TAC
        >> mp_tac
             (Q.INST
               [`source` |-> `c0`, `clock` |-> `clock - 1`,
                `result` |-> `x'`]
               registered_case10173_fs_ceil_div_eval)
        >> simp [])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> simp []
QED

val _ = export_theory ();
