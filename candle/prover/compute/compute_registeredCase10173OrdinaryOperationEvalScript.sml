(*****************************************************************************
 * Registered evaluator seams for fixed ordinary-program operations.
 *
 * The authenticated case-10173 source program uses the ordinary evaluator for
 * polynomial terms, coordinate square roots, products, and additions.  This
 * theory connects the fixed-item wrappers for square root and multiplication
 * to their already-normalized numerical result calls without re-evaluating
 * either operation in the proof.
 *****************************************************************************)
Theory compute_registeredCase10173OrdinaryOperationEval
Ancestors
  compute_registeredCase10173OrdinaryItemEval
Libs
  bossLib preamble

Definition registered_case10173_fso_item_mul_body_def:
  registered_case10173_fso_item_mul_body =
    App «candle_cv_fsa_item_fixed»
      [App «candle_cv_fs_result_mul»
        [App «candle_cv_fs_list_of_q» [Var «radii»];
         App «candle_cv_fsa_item_to_fixed» [Var «left»];
         App «candle_cv_fsa_item_to_fixed» [Var «right»]]]
End

Definition registered_case10173_fsn_item_sqrt_body_def:
  registered_case10173_fsn_item_sqrt_body =
    App «candle_cv_fsa_item_fixed»
      [App «candle_cv_fsn_result_sqrt»
        [App «candle_cv_fs_list_of_q» [Var «radii»];
         Var «center_certificate»;Var «box_certificate»;
         App «candle_cv_fsa_item_to_fixed» [Var «item»]]]
End

Theorem registered_case10173_fso_item_mul_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fso_item_mul» =
    SOME
      ([«radii»;«left»;«right»],
       registered_case10173_fso_item_mul_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsn_item_sqrt_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsn_item_sqrt» =
    SOME
      ([«radii»;«center_certificate»;«box_certificate»;«item»],
       registered_case10173_fsn_item_sqrt_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fso_item_mul_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_item_mul»
        [from_cv radii;from_cv left;from_cv right]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);(«left»,from_cv left);
         («right»,from_cv right)]
        registered_case10173_fso_item_mul_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fso_item_mul_lookup]
QED

Theorem registered_case10173_fsn_item_sqrt_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_item_sqrt»
        [from_cv radii;from_cv center_certificate;
         from_cv box_certificate;from_cv item]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_certificate»,from_cv center_certificate);
         («box_certificate»,from_cv box_certificate);
         («item»,from_cv item)]
        registered_case10173_fsn_item_sqrt_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_fsn_item_sqrt_lookup]
QED

Theorem registered_case10173_fso_item_mul_fixed_subst:
  subst
      [(«radii»,from_cv radii);
       («left»,from_cv (Pair (Num 1) left_result));
       («right»,from_cv (Pair (Num 1) right_result))]
      registered_case10173_fso_item_mul_body =
    App «candle_cv_fsa_item_fixed»
      [App «candle_cv_fs_result_mul»
        [App «candle_cv_fs_list_of_q» [from_cv radii];
         App «candle_cv_fsa_item_to_fixed»
           [from_cv (Pair (Num 1) left_result)];
         App «candle_cv_fsa_item_to_fixed»
           [from_cv (Pair (Num 1) right_result)]]]
Proof
  simp
    [registered_case10173_fso_item_mul_body_def,
     compute_evalTheory.subst_def]
QED

Theorem registered_case10173_fsn_item_sqrt_fixed_subst:
  subst
      [(«radii»,from_cv radii);
       («center_certificate»,from_cv center_certificate);
       («box_certificate»,from_cv box_certificate);
       («item»,from_cv (Pair (Num 1) item_result))]
      registered_case10173_fsn_item_sqrt_body =
    App «candle_cv_fsa_item_fixed»
      [App «candle_cv_fsn_result_sqrt»
        [App «candle_cv_fs_list_of_q» [from_cv radii];
         from_cv center_certificate;from_cv box_certificate;
         App «candle_cv_fsa_item_to_fixed»
           [from_cv (Pair (Num 1) item_result)]]]
Proof
  simp
    [registered_case10173_fsn_item_sqrt_body_def,
     compute_evalTheory.subst_def]
QED

Theorem registered_case10173_fso_item_mul_fixed_eval_from_result:
  2 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_list_of_q» [from_cv radii])
      (refs:hol_refs) =
    (M_success (from_cv fixed_radii),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_mul»
        [from_cv fixed_radii;from_cv left_result;
         from_cv right_result]) refs =
    (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_item_mul»
        [from_cv radii;from_cv (Pair (Num 1) left_result);
         from_cv (Pair (Num 1) right_result)]) refs =
    (M_success (from_cv (Pair (Num 1) result)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«radii»,from_cv radii);
             («left»,from_cv (Pair (Num 1) left_result));
             («right»,from_cv (Pair (Num 1) right_result))]
            registered_case10173_fso_item_mul_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fso_item_mul_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [registered_case10173_fso_item_mul_fixed_subst]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_result_mul»
          [App «candle_cv_fs_list_of_q» [from_cv radii];
           App «candle_cv_fsa_item_to_fixed»
             [from_cv (Pair (Num 1) left_result)];
           App «candle_cv_fsa_item_to_fixed»
             [from_cv (Pair (Num 1) right_result)]]) refs =
      (M_success (from_cv result),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval (clock - 1)
                registered_case10173_historical_chunk16_ceqs
                (App «candle_cv_fs_result_mul»
                  [from_cv fixed_radii;from_cv left_result;
                   from_cv right_result]) refs`
        >> conj_tac
        >- (irule
              compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
            >> conj_tac >- intLib.ARITH_TAC
            >> conj_tac >- fs []
            >> conj_tac
            >- (irule registered_case10173_fsa_item_to_fixed_fixed_eval
                >> intLib.ARITH_TAC)
            >> irule registered_case10173_fsa_item_to_fixed_fixed_eval
            >> intLib.ARITH_TAC)
        >> fs [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsa_item_fixed»
          [App «candle_cv_fs_result_mul»
            [App «candle_cv_fs_list_of_q» [from_cv radii];
             App «candle_cv_fsa_item_to_fixed»
               [from_cv (Pair (Num 1) left_result)];
             App «candle_cv_fsa_item_to_fixed»
               [from_cv (Pair (Num 1) right_result)]]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsa_item_fixed» [from_cv result]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> fs [])
  >> fs
       [compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fsa_item_fixed_eval]
QED

Theorem registered_case10173_fsn_item_sqrt_fixed_eval_from_result:
  2 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_list_of_q» [from_cv radii])
      (refs:hol_refs) =
    (M_success (from_cv fixed_radii),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_result_sqrt»
        [from_cv fixed_radii;from_cv center_certificate;
         from_cv box_certificate;from_cv item_result]) refs =
    (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_item_sqrt»
        [from_cv radii;from_cv center_certificate;
         from_cv box_certificate;
         from_cv (Pair (Num 1) item_result)]) refs =
    (M_success (from_cv (Pair (Num 1) result)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«radii»,from_cv radii);
             («center_certificate»,from_cv center_certificate);
             («box_certificate»,from_cv box_certificate);
             («item»,from_cv (Pair (Num 1) item_result))]
            registered_case10173_fsn_item_sqrt_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fsn_item_sqrt_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [registered_case10173_fsn_item_sqrt_fixed_subst]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsn_result_sqrt»
          [App «candle_cv_fs_list_of_q» [from_cv radii];
           from_cv center_certificate;from_cv box_certificate;
           App «candle_cv_fsa_item_to_fixed»
             [from_cv (Pair (Num 1) item_result)]]) refs =
      (M_success (from_cv result),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval (clock - 1)
                registered_case10173_historical_chunk16_ceqs
                (App «candle_cv_fsn_result_sqrt»
                  [from_cv fixed_radii;from_cv center_certificate;
                   from_cv box_certificate;from_cv item_result]) refs`
        >> conj_tac
        >- (irule
              compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
            >> conj_tac >- intLib.ARITH_TAC
            >> conj_tac >- fs []
            >> conj_tac >- irule compute_execProofTheory.compute_eval_from_cv
            >> conj_tac >- irule compute_execProofTheory.compute_eval_from_cv
            >> irule registered_case10173_fsa_item_to_fixed_fixed_eval
            >> intLib.ARITH_TAC)
        >> fs [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsa_item_fixed»
          [App «candle_cv_fsn_result_sqrt»
            [App «candle_cv_fs_list_of_q» [from_cv radii];
             from_cv center_certificate;from_cv box_certificate;
             App «candle_cv_fsa_item_to_fixed»
               [from_cv (Pair (Num 1) item_result)]]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsa_item_fixed» [from_cv result]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> fs [])
  >> fs
       [compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fsa_item_fixed_eval]
QED

val _ = export_theory ();
