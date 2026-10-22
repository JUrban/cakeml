(*****************************************************************************
 * Registered evaluator semantics for historical interval-list scaling.
 *
 * The source program first forms an unrounded list of interval products and
 * then outward-rounds the whole list.  These object helpers preserve that
 * two-stage boundary so the proof follows the literal program rather than
 * replacing it with an extensionally similar list operation.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalListArithmeticEval
Ancestors
  compute_registeredCase10173HistoricalInverseEval
Libs
  bossLib preamble

Definition registered_case10173_fs_raw_interval_list_scale_body_def:
  registered_case10173_fs_raw_interval_list_scale_body =
    If (Uop Ispair (Var «items»))
      (Pair
        (App «candle_cv_fs_raw_interval_mul»
          [Var «scalar»;Uop Fst (Var «items»)])
        (App «candle_cv_fs_raw_interval_list_scale»
          [Var «scalar»;Uop Snd (Var «items»)]))
      (Num 0)
End

Definition registered_case10173_fs_raw_interval_list_round_body_def:
  registered_case10173_fs_raw_interval_list_round_body =
    If (Uop Ispair (Var «items»))
      (Pair
        (App «candle_cv_fs_raw_interval_round»
          [Var «denominator»;Uop Fst (Var «items»)])
        (App «candle_cv_fs_raw_interval_list_round»
          [Var «denominator»;Uop Snd (Var «items»)]))
      (Num 0)
End

Definition registered_case10173_fsn_interval_list_scale_body_def:
  registered_case10173_fsn_interval_list_scale_body =
    App «candle_cv_fs_raw_interval_list_round»
      [App «candle_cv_fs_scale» [];
       App «candle_cv_fs_raw_interval_list_scale»
         [Var «scalar»;Var «items»]]
End

Definition registered_case10173_fs_raw_interval_list_scale_object_def:
  registered_case10173_fs_raw_interval_list_scale_object scalar
      ([]:cv list) = SOME [] /\
  registered_case10173_fs_raw_interval_list_scale_object scalar
      (value::values) =
    case bounded_object_fs_raw_interval_mul scalar value of
    | NONE => NONE
    | SOME product =>
      case registered_case10173_fs_raw_interval_list_scale_object
        scalar values of
      | NONE => NONE
      | SOME products => SOME (product::products)
End

Definition registered_case10173_fs_raw_interval_list_round_object_def:
  registered_case10173_fs_raw_interval_list_round_object denominator
      ([]:cv list) = SOME [] /\
  registered_case10173_fs_raw_interval_list_round_object denominator
      (value::values) =
    case bounded_object_fs_raw_interval_round denominator value of
    | NONE => NONE
    | SOME rounded =>
      case registered_case10173_fs_raw_interval_list_round_object
        denominator values of
      | NONE => NONE
      | SOME rounded_values => SOME (rounded::rounded_values)
End

Definition registered_case10173_fsn_interval_list_scale_object_def:
  registered_case10173_fsn_interval_list_scale_object scalar values =
    case registered_case10173_fs_raw_interval_list_scale_object
      scalar values of
    | NONE => NONE
    | SOME raw_values =>
        registered_case10173_fs_raw_interval_list_round_object
          1000000000000 raw_values
End

Theorem registered_case10173_fs_raw_interval_list_scale_object_length:
  !scalar values products.
    registered_case10173_fs_raw_interval_list_scale_object
      scalar values = SOME products ==>
    LENGTH products = LENGTH values
Proof
  Induct_on `values`
  >> rw [registered_case10173_fs_raw_interval_list_scale_object_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_fs_raw_interval_list_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_interval_list_scale» =
    SOME
      ([«scalar»;«items»],
       registered_case10173_fs_raw_interval_list_scale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_interval_list_round_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_interval_list_round» =
    SOME
      ([«denominator»;«items»],
       registered_case10173_fs_raw_interval_list_round_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsn_interval_list_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsn_interval_list_scale» =
    SOME
      ([«scalar»;«items»],
       registered_case10173_fsn_interval_list_scale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_interval_list_scale_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_list_scale»
        [from_cv scalar;
         from_cv (registered_case10173_cv_list values)])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«scalar»,from_cv scalar);
         («items»,from_cv (registered_case10173_cv_list values))]
        registered_case10173_fs_raw_interval_list_scale_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_interval_list_scale_lookup]
QED

Theorem registered_case10173_fs_raw_interval_list_round_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_list_round»
        [from_cv (Num denominator);
         from_cv (registered_case10173_cv_list values)])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«denominator»,from_cv (Num denominator));
         («items»,from_cv (registered_case10173_cv_list values))]
        registered_case10173_fs_raw_interval_list_round_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_interval_list_round_lookup]
QED

Theorem registered_case10173_fsn_interval_list_scale_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_list_scale»
        [from_cv scalar;
         from_cv (registered_case10173_cv_list values)])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«scalar»,from_cv scalar);
         («items»,from_cv (registered_case10173_cv_list values))]
        registered_case10173_fsn_interval_list_scale_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fsn_interval_list_scale_lookup]
QED

Theorem registered_case10173_fs_raw_interval_list_scale_object_eval:
  !scalar values products clock refs.
    registered_case10173_fs_raw_interval_list_scale_object
        scalar values = SOME products /\
    LENGTH values + 3 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_scale»
          [from_cv scalar;
           from_cv (registered_case10173_cv_list values)])
        (refs:hol_refs) =
      (M_success
        (from_cv (registered_case10173_cv_list products)),refs)
Proof
  Induct_on `values`
  >- (rpt strip_tac
      >> gvs
           [registered_case10173_fs_raw_interval_list_scale_object_def]
      >> simp [registered_case10173_fs_raw_interval_list_scale_unfold]
      >> simp
           [registered_case10173_fs_raw_interval_list_scale_body_def,
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
  >> rpt strip_tac
  >> Cases_on `bounded_object_fs_raw_interval_mul scalar h`
  >> gvs [registered_case10173_fs_raw_interval_list_scale_object_def]
  >> Cases_on
       `registered_case10173_fs_raw_interval_list_scale_object
          scalar values`
  >> gvs [registered_case10173_fs_raw_interval_list_scale_object_def]
  >> Cases_on `x`
  >> gvs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_def]
  >- (Cases_on `scalar`
      >> Cases_on `h`
      >> gvs
           [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_def]
      >> BasicProvers.every_case_tac
      >> gvs
           [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_extrema_def]
      >> BasicProvers.every_case_tac
      >> gvs [])
  >> simp [registered_case10173_fs_raw_interval_list_scale_unfold]
  >> simp
       [registered_case10173_fs_raw_interval_list_scale_body_def,
        compute_evalTheory.subst_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair h (registered_case10173_cv_list values):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `(Pair c c0:cv)`,
            `right_result` |-> `registered_case10173_cv_list x'`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_mul»
            [from_cv scalar;
             Uop Fst
               (Pair (from_cv h)
                 (from_cv (registered_case10173_cv_list values)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_mul»
            [from_cv scalar;from_cv h]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
        >> intLib.ARITH_TAC)
      >> rw []
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST [`lower` |-> `c`, `upper` |-> `c0`]
               compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_raw_interval_mul_eval))
      >> simp []
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_scale»
          [from_cv scalar;
           Uop Snd
             (Pair (from_cv h)
               (from_cv (registered_case10173_cv_list values)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_scale»
          [from_cv scalar;
           from_cv (registered_case10173_cv_list values)]) refs` by
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

Theorem registered_case10173_fs_raw_interval_list_round_object_eval:
  !denominator values rounded_values clock refs.
    registered_case10173_fs_raw_interval_list_round_object
        denominator values = SOME rounded_values /\
    0 < denominator /\
    LENGTH values + 11 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_round»
          [from_cv (Num denominator);
           from_cv (registered_case10173_cv_list values)])
        (refs:hol_refs) =
      (M_success
        (from_cv (registered_case10173_cv_list rounded_values)),refs)
Proof
  Induct_on `values`
  >- (rpt strip_tac
      >> gvs
           [registered_case10173_fs_raw_interval_list_round_object_def]
      >> rw
           [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST [`values` |-> `[]`]
                registered_case10173_fs_raw_interval_list_round_unfold)]
      >> simp
           [registered_case10173_fs_raw_interval_list_round_body_def,
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
  >> rpt strip_tac
  >> Cases_on `bounded_object_fs_raw_interval_round denominator h`
  >> gvs [registered_case10173_fs_raw_interval_list_round_object_def]
  >> Cases_on
       `registered_case10173_fs_raw_interval_list_round_object
          denominator values`
  >> gvs [registered_case10173_fs_raw_interval_list_round_object_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`values` |-> `h::values`]
            registered_case10173_fs_raw_interval_list_round_unfold)]
  >> simp
       [registered_case10173_fs_raw_interval_list_round_body_def,
        compute_evalTheory.subst_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair h (registered_case10173_cv_list values):cv)`]
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
          (App «candle_cv_fs_raw_interval_round»
            [Num denominator;
             Uop Fst
               (Pair (from_cv h)
                 (from_cv (registered_case10173_cv_list values)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_round»
            [from_cv (Num denominator);from_cv h]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> conj_tac
        >- intLib.ARITH_TAC
        >> conj_tac
        >- simp
             [Once compute_evalTheory.compute_eval_def,
              compute_execTheory.from_cv_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components)
      >> rw []
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_raw_interval_round_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_round»
          [Num denominator;
           Uop Snd
             (Pair (from_cv h)
               (from_cv (registered_case10173_cv_list values)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_round»
          [from_cv (Num denominator);
           from_cv (registered_case10173_cv_list values)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> conj_tac
        >- intLib.ARITH_TAC
        >> conj_tac
        >- simp
             [Once compute_evalTheory.compute_eval_def,
              compute_execTheory.from_cv_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components)
  >> rw []
  >> first_x_assum irule
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fsn_interval_list_scale_object_eval:
  !scalar values scaled_values clock refs.
    registered_case10173_fsn_interval_list_scale_object
        scalar values = SOME scaled_values /\
    LENGTH values + 12 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsn_interval_list_scale»
          [from_cv scalar;
           from_cv (registered_case10173_cv_list values)])
        (refs:hol_refs) =
      (M_success
        (from_cv (registered_case10173_cv_list scaled_values)),refs)
Proof
  rw [registered_case10173_fsn_interval_list_scale_object_def]
  >> Cases_on
       `registered_case10173_fs_raw_interval_list_scale_object
          scalar values`
  >> gvs []
  >> simp [registered_case10173_fsn_interval_list_scale_unfold]
  >> simp
       [registered_case10173_fsn_interval_list_scale_body_def,
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
        (App «candle_cv_fs_raw_interval_list_scale»
          [from_cv scalar;
           from_cv (registered_case10173_cv_list values)]) refs =
      (M_success (from_cv (registered_case10173_cv_list x)),refs)` by
       (irule registered_case10173_fs_raw_interval_list_scale_object_eval
        >> simp []
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_round»
          [App «candle_cv_fs_scale» [];
           App «candle_cv_fs_raw_interval_list_scale»
             [from_cv scalar;
              from_cv (registered_case10173_cv_list values)]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_list_round»
          [from_cv (Num 1000000000000);
           from_cv (registered_case10173_cv_list x)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [compute_execTheory.from_cv_def])
  >> rw []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_raw_interval_list_round_object_eval)
  >> simp []
  >> imp_res_tac
       registered_case10173_fs_raw_interval_list_scale_object_length
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
