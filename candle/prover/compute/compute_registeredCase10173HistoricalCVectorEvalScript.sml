(*****************************************************************************
 * Registered evaluator semantics for the historical first-order c vector.
 *
 * Each of the six entries is
 *   -(delta_gradient[i] * b) + delta_x4 * b_gradient[i]
 * in the source-exact decimal interval arithmetic.  The theorem below keeps
 * that per-entry calculation explicit and connects the literal six-way
 * registered program to the recursive bounded-object checker.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalCVectorEval
Ancestors
  compute_registeredCase10173HistoricalCombinatorEval
  compute_registeredCase10173CertifiedCheckEval
  compute_boundedObjectHistoricalListDecimal
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_c_vector_body_def:
  registered_case10173_fs_hist_c_vector_body =
    App «candle_cv_fs_angle_six»
      [App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_neg»
          [App «candle_cv_fs_angle_interval_mul»
            [App «candle_cv_fs_interval_lookup»
              [Num 0;Var «delta_x4_gradient»];
             Var «b»]];
         App «candle_cv_fs_angle_interval_mul»
          [Var «delta_x4_value»;
           App «candle_cv_fs_interval_lookup»
            [Num 0;Var «b_gradient»]]];
       App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_neg»
          [App «candle_cv_fs_angle_interval_mul»
            [App «candle_cv_fs_interval_lookup»
              [Num 1;Var «delta_x4_gradient»];
             Var «b»]];
         App «candle_cv_fs_angle_interval_mul»
          [Var «delta_x4_value»;
           App «candle_cv_fs_interval_lookup»
            [Num 1;Var «b_gradient»]]];
       App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_neg»
          [App «candle_cv_fs_angle_interval_mul»
            [App «candle_cv_fs_interval_lookup»
              [Num 2;Var «delta_x4_gradient»];
             Var «b»]];
         App «candle_cv_fs_angle_interval_mul»
          [Var «delta_x4_value»;
           App «candle_cv_fs_interval_lookup»
            [Num 2;Var «b_gradient»]]];
       App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_neg»
          [App «candle_cv_fs_angle_interval_mul»
            [App «candle_cv_fs_interval_lookup»
              [Num 3;Var «delta_x4_gradient»];
             Var «b»]];
         App «candle_cv_fs_angle_interval_mul»
          [Var «delta_x4_value»;
           App «candle_cv_fs_interval_lookup»
            [Num 3;Var «b_gradient»]]];
       App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_neg»
          [App «candle_cv_fs_angle_interval_mul»
            [App «candle_cv_fs_interval_lookup»
              [Num 4;Var «delta_x4_gradient»];
             Var «b»]];
         App «candle_cv_fs_angle_interval_mul»
          [Var «delta_x4_value»;
           App «candle_cv_fs_interval_lookup»
            [Num 4;Var «b_gradient»]]];
       App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_neg»
          [App «candle_cv_fs_angle_interval_mul»
            [App «candle_cv_fs_interval_lookup»
              [Num 5;Var «delta_x4_gradient»];
             Var «b»]];
         App «candle_cv_fs_angle_interval_mul»
          [Var «delta_x4_value»;
           App «candle_cv_fs_interval_lookup»
            [Num 5;Var «b_gradient»]]]]
End

Definition registered_case10173_fs_hist_c_entry_object_def:
  registered_case10173_fs_hist_c_entry_object
      delta_x4_value b delta_gradient b_gradient =
    case bounded_object_fs_interval_mul_decimal delta_gradient b of
    | NONE => NONE
    | SOME first_product =>
      case bounded_object_fs_interval_mul_decimal
        delta_x4_value b_gradient of
      | NONE => NONE
      | SOME second_product =>
        case bounded_object_fs_interval_neg first_product of
        | NONE => NONE
        | SOME negative_first =>
            bounded_object_fs_interval_add negative_first second_product
End

Theorem registered_case10173_fs_hist_c_vector_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_c_vector» =
    SOME
      ([«delta_x4_value»;«b»;«delta_x4_gradient»;«b_gradient»],
       registered_case10173_fs_hist_c_vector_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_c_vector_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_c_vector»
        [from_cv delta_x4_value;from_cv b;
         from_cv delta_x4_gradient;from_cv b_gradient])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«delta_x4_value»,from_cv delta_x4_value);
         («b»,from_cv b);
         («delta_x4_gradient»,from_cv delta_x4_gradient);
         («b_gradient»,from_cv b_gradient)]
        registered_case10173_fs_hist_c_vector_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_fs_hist_c_vector_lookup]
QED

Theorem registered_case10173_fs_interval_lookup_cv_list_eval:
  !index values clock refs.
    index < LENGTH values /\
    index + 2 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [Num index;from_cv (registered_case10173_cv_list values)])
        (refs:hol_refs) =
      (M_success (from_cv (EL index values)),refs)
Proof
  Induct_on `values`
  >- simp []
  >> Cases_on `index`
  >- (rw []
      >> simp
           [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`item` |-> `h`,
                `items` |-> `registered_case10173_cv_list values`]
               compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_interval_lookup_head_eval))
      >> simp
           [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def])
  >> rw []
  >> simp
       [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`variable` |-> `n`, `item` |-> `h`,
            `items` |-> `registered_case10173_cv_list values`]
           compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_interval_lookup_tail_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum (mp_tac o Q.SPECL [`n`,`clock - 1`,`refs`])
  >> impl_tac >- intLib.ARITH_TAC
  >> simp []
QED

Theorem registered_case10173_fs_hist_c_entry_eval:
  registered_case10173_fs_hist_c_entry_object
      delta_x4_value b delta_gradient b_gradient = SOME result /\
  11 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_neg»
          [App «candle_cv_fs_angle_interval_mul»
            [from_cv delta_gradient;from_cv b]];
         App «candle_cv_fs_angle_interval_mul»
          [from_cv delta_x4_value;from_cv b_gradient]])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw [registered_case10173_fs_hist_c_entry_object_def]
  >> every_case_tac
  >> gvs []
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_add»
            [from_cv x'';from_cv x]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp []
      >> conj_tac
      >- (irule EQ_TRANS
          >> qexists_tac
               `compute_eval clock
                  registered_case10173_historical_chunk16_ceqs
                  (App «candle_cv_fs_interval_neg» [from_cv x']) refs`
          >> conj_tac
          >- (irule
                compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
              >> simp []
              >> irule
                   compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
              >> simp [])
          >> irule
               compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
          >> simp [])
      >> irule
           compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
      >> simp [])
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_add_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_c_entry_lookup_eval:
  index < LENGTH delta_values /\
  index < LENGTH b_values /\
  registered_case10173_fs_hist_c_entry_object
      delta_x4_value b (EL index delta_values) (EL index b_values) =
    SOME result /\
  index + 12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_neg»
          [App «candle_cv_fs_angle_interval_mul»
            [App «candle_cv_fs_interval_lookup»
              [Num index;
               from_cv (registered_case10173_cv_list delta_values)];
             from_cv b]];
         App «candle_cv_fs_angle_interval_mul»
          [from_cv delta_x4_value;
           App «candle_cv_fs_interval_lookup»
            [Num index;from_cv (registered_case10173_cv_list b_values)]]])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw [registered_case10173_fs_hist_c_entry_object_def]
  >> every_case_tac
  >> gvs []
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_add»
            [from_cv x'';from_cv x]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp []
      >> conj_tac
      >- (irule EQ_TRANS
          >> qexists_tac
               `compute_eval clock
                  registered_case10173_historical_chunk16_ceqs
                  (App «candle_cv_fs_interval_neg» [from_cv x']) refs`
          >> conj_tac
          >- (irule
                compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
              >> simp []
              >> irule EQ_TRANS
              >> qexists_tac
                   `compute_eval clock
                      registered_case10173_historical_chunk16_ceqs
                      (App «candle_cv_fs_angle_interval_mul»
                        [from_cv (EL index delta_values);from_cv b]) refs`
              >> conj_tac
              >- (irule
                    compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
                  >> simp [compute_execProofTheory.compute_eval_from_cv]
                  >> irule
                       registered_case10173_fs_interval_lookup_cv_list_eval
                  >> intLib.ARITH_TAC)
              >> irule
                   compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
              >> simp [])
          >> irule
               compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
          >> simp [])
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_angle_interval_mul»
                [from_cv delta_x4_value;from_cv (EL index b_values)]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
          >> simp [compute_execProofTheory.compute_eval_from_cv]
          >> irule registered_case10173_fs_interval_lookup_cv_list_eval
          >> intLib.ARITH_TAC)
      >> irule
           compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
      >> simp [])
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_add_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_c_vector_six_eval:
  registered_case10173_fs_hist_c_entry_object
      delta_x4_value b d0 b0 = SOME c0 /\
  registered_case10173_fs_hist_c_entry_object
      delta_x4_value b d1 b1 = SOME c1 /\
  registered_case10173_fs_hist_c_entry_object
      delta_x4_value b d2 b2 = SOME c2 /\
  registered_case10173_fs_hist_c_entry_object
      delta_x4_value b d3 b3 = SOME c3 /\
  registered_case10173_fs_hist_c_entry_object
      delta_x4_value b d4 b4 = SOME c4 /\
  registered_case10173_fs_hist_c_entry_object
      delta_x4_value b d5 b5 = SOME c5 /\
  18 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_c_vector»
        [from_cv delta_x4_value;from_cv b;
         from_cv (registered_case10173_cv_list [d0;d1;d2;d3;d4;d5]);
         from_cv (registered_case10173_cv_list [b0;b1;b2;b3;b4;b5])])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_list [c0;c1;c2;c3;c4;c5])),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_c_vector_unfold]
  >> simp
       [registered_case10173_fs_hist_c_vector_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv c0;from_cv c1;from_cv c2;
             from_cv c3;from_cv c4;from_cv c5]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp []
      >> rpt conj_tac
      >> irule registered_case10173_fs_hist_c_entry_lookup_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
