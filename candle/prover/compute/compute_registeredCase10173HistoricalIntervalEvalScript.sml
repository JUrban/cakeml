(*****************************************************************************
 * Registered evaluator semantics for the historical interval primitives.
 *
 * These operations are shared by both remaining dihedral refinements.  The
 * statements deliberately use the bounded-object interface so the exact
 * decimal proofs can be composed without replaying the generic evaluator.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalIntervalEval
Ancestors
  compute_registeredCase10173TaylorRoundEval
  compute_registeredCase10173RootInputsEval
Libs
  bossLib preamble

Definition registered_case10173_fs_canonical_body_def:
  registered_case10173_fs_canonical_body =
    If (Binop Less (Uop Fst (Var «x»)) (Uop Snd (Var «x»)))
      (Pair (Num 0)
        (Binop Sub (Uop Snd (Var «x»)) (Uop Fst (Var «x»))))
      (Pair
        (Binop Sub (Uop Fst (Var «x»)) (Uop Snd (Var «x»)))
        (Num 0))
End

Definition registered_case10173_fs_raw_min_body_def:
  registered_case10173_fs_raw_min_body =
    If (App «candle_cv_fs_raw_le» [Var «x»;Var «y»])
      (Var «x») (Var «y»)
End

Definition registered_case10173_fs_add_body_def:
  registered_case10173_fs_add_body =
    App «candle_cv_fs_canonical»
      [App «candle_cv_fs_raw_add» [Var «x»;Var «y»]]
End

Definition registered_case10173_fs_neg_body_def:
  registered_case10173_fs_neg_body =
    App «candle_cv_fs_raw_neg» [Var «x»]
End

Definition registered_case10173_fs_interval_neg_body_def:
  registered_case10173_fs_interval_neg_body =
    Pair
      (App «candle_cv_fs_neg» [Uop Snd (Var «i»)])
      (App «candle_cv_fs_neg» [Uop Fst (Var «i»)])
End

Definition registered_case10173_fs_interval_add_body_def:
  registered_case10173_fs_interval_add_body =
    Pair
      (App «candle_cv_fs_add»
        [Uop Fst (Var «x»);Uop Fst (Var «y»)])
      (App «candle_cv_fs_add»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Definition registered_case10173_fs_raw_interval_mul_body_def:
  registered_case10173_fs_raw_interval_mul_body =
    Pair
      (App «candle_cv_fs_raw_min»
        [App «candle_cv_fs_raw_min»
          [App «candle_cv_fs_raw_mul»
            [Uop Fst (Var «x»);Uop Fst (Var «y»)];
           App «candle_cv_fs_raw_mul»
            [Uop Fst (Var «x»);Uop Snd (Var «y»)]];
         App «candle_cv_fs_raw_min»
          [App «candle_cv_fs_raw_mul»
            [Uop Snd (Var «x»);Uop Fst (Var «y»)];
           App «candle_cv_fs_raw_mul»
            [Uop Snd (Var «x»);Uop Snd (Var «y»)]]])
      (App «candle_cv_fs_raw_max»
        [App «candle_cv_fs_raw_max»
          [App «candle_cv_fs_raw_mul»
            [Uop Fst (Var «x»);Uop Fst (Var «y»)];
           App «candle_cv_fs_raw_mul»
            [Uop Fst (Var «x»);Uop Snd (Var «y»)]];
         App «candle_cv_fs_raw_max»
          [App «candle_cv_fs_raw_mul»
            [Uop Snd (Var «x»);Uop Fst (Var «y»)];
           App «candle_cv_fs_raw_mul»
            [Uop Snd (Var «x»);Uop Snd (Var «y»)]]])
End

Definition registered_case10173_fs_angle_interval_mul_body_def:
  registered_case10173_fs_angle_interval_mul_body =
    App «candle_cv_fs_raw_interval_round»
      [App «candle_cv_fs_scale» [];
       App «candle_cv_fs_raw_interval_mul» [Var «left»;Var «right»]]
End

Theorem registered_case10173_fs_canonical_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_canonical» =
    SOME ([«x»],registered_case10173_fs_canonical_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_min_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_min» =
    SOME ([«x»;«y»],registered_case10173_fs_raw_min_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_add» =
    SOME ([«x»;«y»],registered_case10173_fs_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_neg_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_neg» =
    SOME ([«x»],registered_case10173_fs_neg_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_neg_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_neg» =
    SOME ([«i»],registered_case10173_fs_interval_neg_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_add» =
    SOME ([«x»;«y»],registered_case10173_fs_interval_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_interval_mul_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_interval_mul» =
    SOME ([«x»;«y»],registered_case10173_fs_raw_interval_mul_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_interval_mul_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_interval_mul» =
    SOME
      ([«left»;«right»],registered_case10173_fs_angle_interval_mul_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_canonical_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_canonical» [from_cv source])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv source)]
        registered_case10173_fs_canonical_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_canonical_lookup]
QED

Theorem registered_case10173_fs_raw_min_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_min» [from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv left);(«y»,from_cv right)]
        registered_case10173_fs_raw_min_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_min_lookup]
QED

Theorem registered_case10173_fs_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv left);(«y»,from_cv right)]
        registered_case10173_fs_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_add_lookup]
QED

Theorem registered_case10173_fs_neg_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_neg» [from_cv source]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv source)] registered_case10173_fs_neg_body)
      refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_neg_lookup]
QED

Theorem registered_case10173_fs_interval_neg_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg» [from_cv source])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«i»,from_cv source)]
        registered_case10173_fs_interval_neg_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_neg_lookup]
QED

Theorem registered_case10173_fs_interval_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv left);(«y»,from_cv right)]
        registered_case10173_fs_interval_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_interval_add_lookup]
QED

Theorem registered_case10173_fs_raw_interval_mul_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_mul» [from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv left);(«y»,from_cv right)]
        registered_case10173_fs_raw_interval_mul_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_interval_mul_lookup]
QED

Theorem registered_case10173_fs_angle_interval_mul_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«left»,from_cv left);(«right»,from_cv right)]
        registered_case10173_fs_angle_interval_mul_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_angle_interval_mul_lookup]
QED

Theorem registered_case10173_fs_canonical_eval:
  bounded_object_fs_canonical source = SOME result /\
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_canonical» [from_cv source])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `source`
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_def]
  >> Cases_on `n < n'`
  >> rpt strip_tac
  >> gvs [compute_execTheory.from_cv_def]
  >> Cases_on `clock`
  >> gvs
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_canonical_lookup,
        registered_case10173_fs_canonical_body_def,
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
QED

Theorem registered_case10173_fs_raw_min_eval:
  bounded_object_fs_raw_min left right = SOME result /\
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_min» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `bounded_object_fs_raw_le left right`
  >> fs [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_min_def]
  >> strip_tac
  >> gvs [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_min_def]
  >> simp [registered_case10173_fs_raw_min_unfold]
  >> simp
       [registered_case10173_fs_raw_min_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_le» [from_cv left;from_cv right]) refs =
      (M_success (Num (if x then 1 else 0)),refs)` by
       (irule
          compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_le_eval
        >> simp []
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (If (App «candle_cv_fs_raw_le» [from_cv left;from_cv right])
          (from_cv left) (from_cv right)) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (if x then from_cv left else from_cv right) refs` by
       (irule
          compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_compute_eval_if_bool
        >> simp [])
  >> Cases_on `x`
  >> fs [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem registered_case10173_fs_raw_mul_composed_eval:
  bounded_object_fs_raw_mul left right = SOME result /\
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_exp (refs:hol_refs) = (M_success (from_cv left),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_exp refs = (M_success (from_cv right),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_mul» [left_exp;right_exp]) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_mul» [left_exp;right_exp]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_mul» [from_cv left;from_cv right]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [])
  >> rw []
  >> irule
       compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_mul_eval
  >> simp []
QED

Theorem registered_case10173_fs_raw_min_composed_eval:
  bounded_object_fs_raw_min left right = SOME result /\
  1 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_exp (refs:hol_refs) = (M_success (from_cv left),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_exp refs = (M_success (from_cv right),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_min» [left_exp;right_exp]) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_min» [left_exp;right_exp]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_min» [from_cv left;from_cv right]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [])
  >> rw []
  >> irule registered_case10173_fs_raw_min_eval
  >> simp []
QED

Theorem registered_case10173_fs_raw_max_composed_eval:
  bounded_object_fs_raw_max left right = SOME result /\
  1 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_exp (refs:hol_refs) = (M_success (from_cv left),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_exp refs = (M_success (from_cv right),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_max» [left_exp;right_exp]) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_max» [left_exp;right_exp]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_max» [from_cv left;from_cv right]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [])
  >> rw []
  >> irule
       compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_max_eval
  >> simp []
QED

Theorem registered_case10173_fs_raw_interval_extrema_composed_eval:
  bounded_object_fs_raw_interval_extrema
      first_value second_value third_value fourth_value =
      SOME (Pair lower upper) /\
  1 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      first_exp (refs:hol_refs) =
        (M_success (from_cv first_value),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      second_exp refs = (M_success (from_cv second_value),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      third_exp refs = (M_success (from_cv third_value),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      fourth_exp refs = (M_success (from_cv fourth_value),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Pair
        (App «candle_cv_fs_raw_min»
          [App «candle_cv_fs_raw_min» [first_exp;second_exp];
           App «candle_cv_fs_raw_min» [third_exp;fourth_exp]])
        (App «candle_cv_fs_raw_max»
          [App «candle_cv_fs_raw_max» [first_exp;second_exp];
           App «candle_cv_fs_raw_max» [third_exp;fourth_exp]])) refs =
    (M_success (from_cv (Pair lower upper)),refs)
Proof
  Cases_on `bounded_object_fs_raw_min first_value second_value`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_extrema_def]
  >> Cases_on `bounded_object_fs_raw_min third_value fourth_value`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_extrema_def]
  >> Cases_on `bounded_object_fs_raw_min x x'`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_extrema_def]
  >> Cases_on `bounded_object_fs_raw_max first_value second_value`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_extrema_def]
  >> Cases_on `bounded_object_fs_raw_max third_value fourth_value`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_extrema_def]
  >> Cases_on `bounded_object_fs_raw_max x''' x''''`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_extrema_def]
  >> strip_tac
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac
  >- (irule registered_case10173_fs_raw_min_composed_eval
      >> simp []
      >> qexists_tac `x`
      >> qexists_tac `x'`
      >> simp []
      >> conj_tac
      >- (irule registered_case10173_fs_raw_min_composed_eval
          >> simp []
          >> qexists_tac `first_value`
          >> qexists_tac `second_value`
          >> simp [])
      >> irule registered_case10173_fs_raw_min_composed_eval
      >> simp []
      >> qexists_tac `third_value`
      >> qexists_tac `fourth_value`
      >> simp [])
  >> irule registered_case10173_fs_raw_max_composed_eval
  >> simp []
  >> qexists_tac `x'''`
  >> qexists_tac `x''''`
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_fs_raw_max_composed_eval
      >> simp []
      >> qexists_tac `first_value`
      >> qexists_tac `second_value`
      >> simp [])
  >> irule registered_case10173_fs_raw_max_composed_eval
  >> simp []
  >> qexists_tac `third_value`
  >> qexists_tac `fourth_value`
  >> simp []
QED

Theorem registered_case10173_fs_raw_interval_mul_eval:
  bounded_object_fs_raw_interval_mul left right =
      SOME (Pair lower upper) /\
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_mul» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv (Pair lower upper)),refs)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_def]
  >> Cases_on `bounded_object_fs_raw_mul c c'`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_def]
  >> Cases_on `bounded_object_fs_raw_mul c c0'`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_def]
  >> Cases_on `bounded_object_fs_raw_mul c0 c'`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_def]
  >> Cases_on `bounded_object_fs_raw_mul c0 c0'`
  >> fs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_def]
  >> strip_tac
  >> gvs []
  >> simp
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`left` |-> `(Pair c c0:cv)`,
             `right` |-> `(Pair c' c0':cv)`]
            registered_case10173_fs_raw_interval_mul_unfold))]
  >> simp
       [registered_case10173_fs_raw_interval_mul_body_def,
        compute_evalTheory.subst_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_raw_interval_extrema_composed_eval)
  >> simp []
  >> qexists_tac `x`
  >> qexists_tac `x'''`
  >> qexists_tac `x'`
  >> qexists_tac `x''`
  >> simp []
  >> rpt conj_tac
  >- (irule registered_case10173_fs_raw_mul_composed_eval
      >> simp []
      >> qexists_tac `c`
      >> qexists_tac `c'`
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
  >- (irule registered_case10173_fs_raw_mul_composed_eval
      >> simp []
      >> qexists_tac `c0`
      >> qexists_tac `c0'`
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >- (irule registered_case10173_fs_raw_mul_composed_eval
      >> simp []
      >> qexists_tac `c`
      >> qexists_tac `c0'`
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> irule registered_case10173_fs_raw_mul_composed_eval
  >> simp []
  >> qexists_tac `c0`
  >> qexists_tac `c'`
  >> simp
       [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
QED

Theorem registered_case10173_fs_angle_interval_mul_eval:
  bounded_object_fs_interval_mul_decimal left right = SOME result /\
  11 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw
    [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_def]
  >> Cases_on `bounded_object_fs_raw_interval_mul left right`
  >> gvs []
  >> Cases_on `x`
  >> gvs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_def]
  >> Cases_on `bounded_object_fs_floor_div c 1000000000000`
  >> gvs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_def]
  >> Cases_on `bounded_object_fs_ceil_div c0 1000000000000`
  >> gvs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_def]
  >> simp [registered_case10173_fs_angle_interval_mul_unfold]
  >> simp
       [registered_case10173_fs_angle_interval_mul_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_scale» []) refs =
      (M_success (Num 1000000000000),refs)` by
       (irule
          compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_mul»
          [from_cv left;from_cv right]) refs =
      (M_success (from_cv (Pair c c0)),refs)` by
       (irule registered_case10173_fs_raw_interval_mul_eval
        >> simp []
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_round»
          [App «candle_cv_fs_scale» [];
           App «candle_cv_fs_raw_interval_mul»
             [from_cv left;from_cv right]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_round»
          [from_cv (Num 1000000000000);
           from_cv (Pair c c0)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [compute_execTheory.from_cv_def])
  >> rw []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`denominator` |-> `1000000000000`,
            `interval` |-> `(Pair c c0:cv)`,
            `result` |-> `(Pair x x':cv)`,
            `clock` |-> `clock - 1`]
           compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_raw_interval_round_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> simp
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_def]
QED

Theorem registered_case10173_fs_add_eval:
  bounded_object_fs_add left right = SOME result /\
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw [compute_boundedObjectDecimalAddTheory.bounded_object_fs_add_def]
  >> every_case_tac
  >> gvs []
  >> simp
       [registered_case10173_fs_add_unfold,
        registered_case10173_fs_add_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_canonical»
          [App «candle_cv_fs_raw_add» [from_cv left;from_cv right]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_canonical» [from_cv x]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> irule
             compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_add_eval
        >> simp [])
  >> rw []
  >> irule registered_case10173_fs_canonical_eval
  >> simp []
QED

Theorem registered_case10173_fs_neg_eval:
  bounded_object_fs_neg source = SOME result /\
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_neg» [from_cv source]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw [compute_boundedObjectDecimalAddTheory.bounded_object_fs_neg_def]
  >> simp
       [registered_case10173_fs_neg_unfold,
        registered_case10173_fs_neg_body_def,
        compute_evalTheory.subst_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_neg_eval)
  >> simp []
QED

Theorem registered_case10173_fs_interval_neg_eval:
  bounded_object_fs_interval_neg source = SOME result /\
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg» [from_cv source])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `source`
  >> rw
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_def]
  >> every_case_tac
  >> gvs []
  >> simp
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`source` |-> `Pair c c0`]
            registered_case10173_fs_interval_neg_unfold))]
  >> simp
       [registered_case10173_fs_interval_neg_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_neg»
          [Uop Snd (Pair (from_cv c) (from_cv c0))]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_neg»
             [Uop Snd (Pair (from_cv c) (from_cv c0))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_neg» [from_cv c0]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> fs [registered_case10173_fs_neg_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_neg»
          [Uop Fst (Pair (from_cv c) (from_cv c0))]) refs =
      (M_success (from_cv x),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_neg»
             [Uop Fst (Pair (from_cv c) (from_cv c0))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_neg» [from_cv c]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> fs [registered_case10173_fs_neg_eval])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> simp []
QED

Theorem registered_case10173_fs_interval_add_eval:
  bounded_object_fs_interval_add left right = SOME result /\
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_def]
  >> every_case_tac
  >> gvs []
  >> simp
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`left` |-> `Pair c c0`, `right` |-> `Pair c' c0'`]
            registered_case10173_fs_interval_add_unfold))]
  >> simp
       [registered_case10173_fs_interval_add_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_add»
          [Uop Fst (Pair (from_cv c) (from_cv c0));
           Uop Fst (Pair (from_cv c') (from_cv c0'))]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_add»
             [Uop Fst (Pair (from_cv c) (from_cv c0));
              Uop Fst (Pair (from_cv c') (from_cv c0'))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_add» [from_cv c;from_cv c']) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> fs [registered_case10173_fs_add_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_add»
          [Uop Snd (Pair (from_cv c) (from_cv c0));
           Uop Snd (Pair (from_cv c') (from_cv c0'))]) refs =
      (M_success (from_cv x),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_add»
             [Uop Snd (Pair (from_cv c) (from_cv c0));
              Uop Snd (Pair (from_cv c') (from_cv c0'))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_add» [from_cv c0;from_cv c0']) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> fs [registered_case10173_fs_add_eval])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> simp []
QED

Theorem registered_case10173_fs_interval_lookup_object_list_eval:
  !index values clock refs.
    index < LENGTH values /\
    index + 2 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [from_cv (Num index);
           from_cv (bounded_interval64_object_cv_list values)])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_interval64_object_cv (EL index values))),refs)
Proof
  Induct_on `values`
  >- simp []
  >> Cases_on `index`
  >- (rw []
      >> simp
           [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`item` |-> `bounded_interval64_object_cv h`,
                `items` |-> `bounded_interval64_object_cv_list values`]
               compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_interval_lookup_head_eval))
      >> simp
           [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def])
  >> rw []
  >> simp
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`variable` |-> `n`,
            `item` |-> `bounded_interval64_object_cv h`,
            `items` |-> `bounded_interval64_object_cv_list values`]
           compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_interval_lookup_tail_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum (mp_tac o Q.SPECL [`n`,`clock - 1`,`refs`])
  >> impl_tac >- intLib.ARITH_TAC
  >> simp [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
