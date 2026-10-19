(*****************************************************************************
 * Complete registered exact-rational square-root certificate evaluation.
 *
 * The six source conditions are stated as their exact cross-multiplied
 * natural-number obligations.  Packet authentication can therefore discharge
 * them once, while every source use reuses this evaluator theorem.
 *****************************************************************************)
Theory compute_registeredCase10173SqrtCertificateCompleteEval
Ancestors
  compute_registeredCase10173SqrtCertificateEval
Libs
  bossLib preamble intLib

Theorem compute_eval_six_if_success:
  compute_eval clock ceqs condition1 (refs:hol_refs) =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs condition2 refs =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs condition3 refs =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs condition4 refs =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs condition5 refs =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs condition6 refs =
      (M_success (Num 1),refs) ==>
  compute_eval clock ceqs
      (If condition1
        (If condition2
          (If condition3
            (If condition4
              (If condition5
                (If condition6 (Num 1) (Num 0))
                (Num 0))
              (Num 0))
            (Num 0))
          (Num 0))
        (Num 0)) refs =
    (M_success (Num 1),refs)
Proof
  rpt strip_tac
  >> fs
       [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_interval_sqrt_certificate_positive_eval:
  input_lower_value * (input_upper_denominator_minus_one + 1) <=
      input_upper_value * (input_lower_denominator_minus_one + 1) /\
  output_lower_value * (output_upper_denominator_minus_one + 1) <=
      output_upper_value * (output_lower_denominator_minus_one + 1) /\
  (output_lower_value * output_lower_value) *
      (input_lower_denominator_minus_one + 1) <=
    input_lower_value *
      (((output_lower_denominator_minus_one + 1) *
        (output_lower_denominator_minus_one + 1) - 1) + 1) /\
  input_upper_value *
      (((output_upper_denominator_minus_one + 1) *
        (output_upper_denominator_minus_one + 1) - 1) + 1) <=
    (output_upper_value * output_upper_value) *
      (input_upper_denominator_minus_one + 1) /\
  5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [from_cv
          (Pair
            (Pair (Pair (Num input_lower_value) (Num 0))
              (Num input_lower_denominator_minus_one))
            (Pair (Pair (Num input_upper_value) (Num 0))
              (Num input_upper_denominator_minus_one)));
         from_cv
          (Pair
            (Pair (Pair (Num output_lower_value) (Num 0))
              (Num output_lower_denominator_minus_one))
            (Pair (Pair (Num output_upper_value) (Num 0))
              (Num output_upper_denominator_minus_one)))]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  rpt strip_tac
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_le»
          [from_cv (Pair (Pair (Num 0) (Num 0)) (Num 0));
           Uop Fst
             (from_cv
               (Pair
                 (Pair (Pair (Num input_lower_value) (Num 0))
                   (Num input_lower_denominator_minus_one))
                 (Pair (Pair (Num input_upper_value) (Num 0))
                   (Num input_upper_denominator_minus_one))))]) refs =
      (M_success (Num 1),refs)` by
     (irule registered_case10173_q_le_positive_results_eval
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_pair]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_le»
          [Uop Fst
             (from_cv
               (Pair
                 (Pair (Pair (Num input_lower_value) (Num 0))
                   (Num input_lower_denominator_minus_one))
                 (Pair (Pair (Num input_upper_value) (Num 0))
                   (Num input_upper_denominator_minus_one))));
           Uop Snd
             (from_cv
               (Pair
                 (Pair (Pair (Num input_lower_value) (Num 0))
                   (Num input_lower_denominator_minus_one))
                 (Pair (Pair (Num input_upper_value) (Num 0))
                   (Num input_upper_denominator_minus_one))))]) refs =
      (M_success (Num 1),refs)` by
     (irule registered_case10173_q_le_positive_results_eval
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_pair,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_pair]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_le»
          [from_cv (Pair (Pair (Num 0) (Num 0)) (Num 0));
           Uop Fst
             (from_cv
               (Pair
                 (Pair (Pair (Num output_lower_value) (Num 0))
                   (Num output_lower_denominator_minus_one))
                 (Pair (Pair (Num output_upper_value) (Num 0))
                   (Num output_upper_denominator_minus_one))))]) refs =
      (M_success (Num 1),refs)` by
     (irule registered_case10173_q_le_positive_results_eval
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_pair]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_le»
          [Uop Fst
             (from_cv
               (Pair
                 (Pair (Pair (Num output_lower_value) (Num 0))
                   (Num output_lower_denominator_minus_one))
                 (Pair (Pair (Num output_upper_value) (Num 0))
                   (Num output_upper_denominator_minus_one))));
           Uop Snd
             (from_cv
               (Pair
                 (Pair (Pair (Num output_lower_value) (Num 0))
                   (Num output_lower_denominator_minus_one))
                 (Pair (Pair (Num output_upper_value) (Num 0))
                   (Num output_upper_denominator_minus_one))))]) refs =
      (M_success (Num 1),refs)` by
     (irule registered_case10173_q_le_positive_results_eval
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_pair,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_pair]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_mul»
          [Uop Fst
             (from_cv
               (Pair
                 (Pair (Pair (Num output_lower_value) (Num 0))
                   (Num output_lower_denominator_minus_one))
                 (Pair (Pair (Num output_upper_value) (Num 0))
                   (Num output_upper_denominator_minus_one))));
           Uop Fst
             (from_cv
               (Pair
                 (Pair (Pair (Num output_lower_value) (Num 0))
                   (Num output_lower_denominator_minus_one))
                 (Pair (Pair (Num output_upper_value) (Num 0))
                   (Num output_upper_denominator_minus_one))))]) refs =
      (M_success
        (from_cv
          (Pair
            (Pair (Num (output_lower_value * output_lower_value)) (Num 0))
            (Num
              ((output_lower_denominator_minus_one + 1) *
               (output_lower_denominator_minus_one + 1) - 1)))),refs)` by
     (irule registered_case10173_q_mul_positive_results_eval
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_pair]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_mul»
          [Uop Snd
             (from_cv
               (Pair
                 (Pair (Pair (Num output_lower_value) (Num 0))
                   (Num output_lower_denominator_minus_one))
                 (Pair (Pair (Num output_upper_value) (Num 0))
                   (Num output_upper_denominator_minus_one))));
           Uop Snd
             (from_cv
               (Pair
                 (Pair (Pair (Num output_lower_value) (Num 0))
                   (Num output_lower_denominator_minus_one))
                 (Pair (Pair (Num output_upper_value) (Num 0))
                   (Num output_upper_denominator_minus_one))))]) refs =
      (M_success
        (from_cv
          (Pair
            (Pair (Num (output_upper_value * output_upper_value)) (Num 0))
            (Num
              ((output_upper_denominator_minus_one + 1) *
               (output_upper_denominator_minus_one + 1) - 1)))),refs)` by
     (irule registered_case10173_q_mul_positive_results_eval
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_pair]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_le»
          [App «candle_cv_q_mul»
             [Uop Fst
                (from_cv
                  (Pair
                    (Pair (Pair (Num output_lower_value) (Num 0))
                      (Num output_lower_denominator_minus_one))
                    (Pair (Pair (Num output_upper_value) (Num 0))
                      (Num output_upper_denominator_minus_one))));
              Uop Fst
                (from_cv
                  (Pair
                    (Pair (Pair (Num output_lower_value) (Num 0))
                      (Num output_lower_denominator_minus_one))
                    (Pair (Pair (Num output_upper_value) (Num 0))
                      (Num output_upper_denominator_minus_one))))];
           Uop Fst
             (from_cv
               (Pair
                 (Pair (Pair (Num input_lower_value) (Num 0))
                   (Num input_lower_denominator_minus_one))
                 (Pair (Pair (Num input_upper_value) (Num 0))
                   (Num input_upper_denominator_minus_one))))]) refs =
      (M_success (Num 1),refs)` by
     (irule registered_case10173_q_le_positive_results_eval
      >> fs
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_pair]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_le»
          [Uop Snd
             (from_cv
               (Pair
                 (Pair (Pair (Num input_lower_value) (Num 0))
                   (Num input_lower_denominator_minus_one))
                 (Pair (Pair (Num input_upper_value) (Num 0))
                   (Num input_upper_denominator_minus_one))));
           App «candle_cv_q_mul»
             [Uop Snd
                (from_cv
                  (Pair
                    (Pair (Pair (Num output_lower_value) (Num 0))
                      (Num output_lower_denominator_minus_one))
                    (Pair (Pair (Num output_upper_value) (Num 0))
                      (Num output_upper_denominator_minus_one))));
              Uop Snd
                (from_cv
                  (Pair
                    (Pair (Pair (Num output_lower_value) (Num 0))
                      (Num output_lower_denominator_minus_one))
                    (Pair (Pair (Num output_upper_value) (Num 0))
                      (Num output_upper_denominator_minus_one))))]]) refs =
      (M_success (Num 1),refs)` by
     (irule registered_case10173_q_le_positive_results_eval
      >> fs
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_pair]
      >> intLib.ARITH_TAC)
  >> rw [registered_case10173_q_interval_sqrt_certificate_unfold]
  >> simp
       [registered_case10173_q_interval_sqrt_certificate_body_def,
        compute_evalTheory.subst_def]
  >> irule compute_eval_six_if_success
  >> fs [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
