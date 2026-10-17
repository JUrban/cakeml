(*****************************************************************************
 * Registered evaluator semantics for historical u point selection.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalUPointsEval
Ancestors
  compute_registeredCase10173HistoricalUThreeGradientEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_u_points_body_def:
  registered_case10173_fs_hist_u_points_body =
    Let «lower_point»
      (App «candle_cv_fs_hist_point» [Uop Fst (Var «x»)])
      (Let «upper_point»
        (App «candle_cv_fs_hist_point» [Uop Snd (Var «x»)])
        (If
          (App «candle_cv_fs_raw_le»
            [App «candle_cv_fs_zero» [];Uop Fst (Var «gradient»)])
          (App «candle_cv_fs_hist_four»
            [Var «upper_point»;Var «upper_point»;
             Var «lower_point»;Var «lower_point»])
          (If
            (App «candle_cv_fs_raw_le»
              [Uop Snd (Var «gradient»);
               App «candle_cv_fs_zero» []])
            (App «candle_cv_fs_hist_four»
              [Var «lower_point»;Var «lower_point»;
               Var «upper_point»;Var «upper_point»])
            (App «candle_cv_fs_hist_four»
              [Var «lower_point»;Var «upper_point»;
               Var «upper_point»;Var «lower_point»]))))
End

Definition registered_case10173_fs_hist_u_points_object_def:
  registered_case10173_fs_hist_u_points_object lower upper
      lower_nonnegative upper_nonpositive =
    let lower_point = Pair lower lower;
        upper_point = Pair upper upper
    in
      if lower_nonnegative then
        registered_case10173_cv_list
          [upper_point;upper_point;lower_point;lower_point]
      else if upper_nonpositive then
        registered_case10173_cv_list
          [lower_point;lower_point;upper_point;upper_point]
      else
        registered_case10173_cv_list
          [lower_point;upper_point;upper_point;lower_point]
End

Theorem registered_case10173_fs_hist_u_points_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_u_points» =
    SOME ([«x»;«gradient»],registered_case10173_fs_hist_u_points_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_u_points_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_points»
        [from_cv x;from_cv gradient]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv x);(«gradient»,from_cv gradient)]
        registered_case10173_fs_hist_u_points_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_hist_u_points_lookup]
QED

Theorem registered_case10173_fs_hist_point_object_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_point» [from_cv endpoint])
      (refs:hol_refs) =
    (M_success (from_cv (Pair endpoint endpoint)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173HistoricalTupleEvalTheory.registered_case10173_fs_hist_point_lookup,
        compute_registeredCase10173HistoricalTupleEvalTheory.registered_case10173_fs_hist_point_body_def,
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

Theorem registered_case10173_fs_raw_le_zero_fst_pair_eval:
  bounded_object_fs_raw_le (Pair (Num 0) (Num 0)) lower = SOME answer /\
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_le»
        [App «candle_cv_fs_zero» [];
         Uop Fst (from_cv (Pair lower upper))]) (refs:hol_refs) =
    (M_success (Num (if answer then 1 else 0)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_le»
            [from_cv (Pair (Num 0) (Num 0));from_cv lower]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_fs_zero_eval,
            compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_le_eval
  >> simp []
QED

Theorem registered_case10173_fs_raw_le_snd_pair_zero_eval:
  bounded_object_fs_raw_le upper (Pair (Num 0) (Num 0)) = SOME answer /\
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_le»
        [Uop Snd (from_cv (Pair lower upper));
         App «candle_cv_fs_zero» []]) (refs:hol_refs) =
    (M_success (Num (if answer then 1 else 0)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_le»
            [from_cv upper;from_cv (Pair (Num 0) (Num 0))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_fs_zero_eval,
            compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_le_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_point_fst_pair_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_point»
        [Uop Fst (from_cv (Pair lower upper))]) (refs:hol_refs) =
    (M_success (from_cv (Pair lower lower)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_point» [from_cv lower]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_fs_hist_point_object_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_point_snd_pair_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_point»
        [Uop Snd (from_cv (Pair lower upper))]) (refs:hol_refs) =
    (M_success (from_cv (Pair upper upper)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_point» [from_cv upper]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_fs_hist_point_object_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_u_points_object_eval:
  bounded_object_fs_raw_le (Pair (Num 0) (Num 0)) gradient_lower =
      SOME lower_nonnegative /\
  bounded_object_fs_raw_le gradient_upper (Pair (Num 0) (Num 0)) =
      SOME upper_nonpositive /\
  12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_points»
        [from_cv (Pair lower upper);
         from_cv (Pair gradient_lower gradient_upper)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_fs_hist_u_points_object lower upper
          lower_nonnegative upper_nonpositive)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_u_points_unfold]
  >> simp
       [registered_case10173_fs_hist_u_points_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `Pair (from_cv lower) (from_cv lower)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_hist_point_fst_pair_eval)
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `Pair (from_cv upper) (from_cv upper)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_hist_point_snd_pair_eval)
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 3)
          registered_case10173_historical_chunk16_ceqs
          (if lower_nonnegative then
             App «candle_cv_fs_hist_four»
               [Pair (from_cv upper) (from_cv upper);
                Pair (from_cv upper) (from_cv upper);
                Pair (from_cv lower) (from_cv lower);
                Pair (from_cv lower) (from_cv lower)]
           else
             If
               (App «candle_cv_fs_raw_le»
                 [Uop Snd
                    (Pair (from_cv gradient_lower) (from_cv gradient_upper));
                  App «candle_cv_fs_zero» []])
               (App «candle_cv_fs_hist_four»
                 [Pair (from_cv lower) (from_cv lower);
                  Pair (from_cv lower) (from_cv lower);
                  Pair (from_cv upper) (from_cv upper);
                  Pair (from_cv upper) (from_cv upper)])
               (App «candle_cv_fs_hist_four»
                 [Pair (from_cv lower) (from_cv lower);
                  Pair (from_cv upper) (from_cv upper);
                  Pair (from_cv upper) (from_cv upper);
                  Pair (from_cv lower) (from_cv lower)])) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_compute_eval_if_bool
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_raw_le_zero_fst_pair_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> Cases_on `lower_nonnegative`
  >- (simp [registered_case10173_fs_hist_u_points_object_def]
      >> simp_tac std_ss
           [GSYM (CONJUNCT2 compute_execTheory.from_cv_def)]
      >> irule
           compute_registeredCase10173HistoricalTupleEvalTheory.registered_case10173_fs_hist_four_eval
      >> intLib.ARITH_TAC)
  >> simp []
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 3)
          registered_case10173_historical_chunk16_ceqs
          (if upper_nonpositive then
             App «candle_cv_fs_hist_four»
               [Pair (from_cv lower) (from_cv lower);
                Pair (from_cv lower) (from_cv lower);
                Pair (from_cv upper) (from_cv upper);
                Pair (from_cv upper) (from_cv upper)]
           else
             App «candle_cv_fs_hist_four»
               [Pair (from_cv lower) (from_cv lower);
                Pair (from_cv upper) (from_cv upper);
                Pair (from_cv upper) (from_cv upper);
                Pair (from_cv lower) (from_cv lower)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_compute_eval_if_bool
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_raw_le_snd_pair_zero_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> Cases_on `upper_nonpositive`
  >> simp [registered_case10173_fs_hist_u_points_object_def]
  >> simp_tac std_ss
       [GSYM (CONJUNCT2 compute_execTheory.from_cv_def)]
  >> irule
       compute_registeredCase10173HistoricalTupleEvalTheory.registered_case10173_fs_hist_four_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
