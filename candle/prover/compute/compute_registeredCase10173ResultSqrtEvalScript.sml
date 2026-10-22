(*****************************************************************************
 * Registered evaluator seam for the historical Taylor square root.
 *
 * The fast decimal checker supplies and authenticates the square-root and
 * reciprocal witnesses.  This theory records the exact decomposition of the
 * unchanged historical [fsn_result_sqrt] source into its domain, center,
 * Hessian, and final Taylor-completion calls.  Later object refinements can
 * discharge those components without replaying the generic source evaluator.
 *****************************************************************************)
Theory compute_registeredCase10173ResultSqrtEval
Ancestors
  compute_registeredCase10173ResultAddEval
  compute_registeredCase10173AnalyticSqrtEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fsn_sqrt_domain_body_def:
  registered_case10173_fsn_sqrt_domain_body =
    Let «input»
      (App «candle_cv_fs_interval_to_q» [Var «fixed_interval»])
      (If
        (App «candle_cv_q_interval_sqrt_certificate»
          [Var «input»;Var «certificate»])
        (If
          (App «candle_cv_q_interval_not_zero»
            [App «candle_cv_q_interval_add_normalized»
              [Var «certificate»;Var «certificate»]])
          (App «candle_cv_q_interval_not_zero»
            [App «candle_cv_q_interval_mul_normalized»
              [App «candle_cv_q_interval_add_normalized»
                 [Var «certificate»;Var «certificate»];
               App «candle_cv_q_interval_add_normalized»
                 [Var «input»;Var «input»]]])
          (Num 0))
        (Num 0))
End

Definition registered_case10173_fsn_first_sqrt_body_def:
  registered_case10173_fsn_first_sqrt_body =
    Let «value»
      (App «candle_cv_fs_interval_of_q» [Var «certificate»])
      (Let «d»
        (App «candle_cv_fs_interval_of_q»
          [App «candle_cv_q_dim_jet_sqrt_d» [Var «certificate»]])
        (App «candle_cv_fs_first_make»
          [Var «value»;
           App «candle_cv_fsn_interval_list_scale»
             [Var «d»;
              App «candle_cv_fs_first_gradient» [Var «first»]]]))
End

Definition registered_case10173_fsn_sqrt_hessian_body_def:
  registered_case10173_fsn_sqrt_hessian_body =
    Let «input»
      (App «candle_cv_fs_interval_to_q» [Var «value»])
      (Let «d»
        (App «candle_cv_fs_interval_of_q»
          [App «candle_cv_q_dim_jet_sqrt_d» [Var «certificate»]])
        (Let «dd»
          (App «candle_cv_fs_interval_of_q»
            [App «candle_cv_q_dim_jet_sqrt_dd»
              [Var «certificate»;Var «input»]])
          (App «candle_cv_fs_interval_matrix_add»
            [App «candle_cv_fsn_interval_matrix_scale»
               [Var «dd»;
                App «candle_cv_fsn_interval_outer»
                  [Var «gradient»;Var «gradient»]];
             App «candle_cv_fsn_interval_matrix_scale»
               [Var «d»;Var «hessian»]])))
End

Definition registered_case10173_fsn_result_sqrt_domain_body_def:
  registered_case10173_fsn_result_sqrt_domain_body =
    App «candle_cv_bool_and»
      [App «candle_cv_fs_result_domain» [Var «result»];
       App «candle_cv_bool_and»
         [App «candle_cv_fsn_sqrt_domain»
            [Var «center_certificate»;
             App «candle_cv_fs_first_value»
               [App «candle_cv_fs_result_center» [Var «result»]]];
          App «candle_cv_fsn_sqrt_domain»
            [Var «box_certificate»;
             App «candle_cv_fs_result_value_bound» [Var «result»]]]]
End

Definition registered_case10173_fsn_result_sqrt_center_body_def:
  registered_case10173_fsn_result_sqrt_center_body =
    App «candle_cv_fsn_first_sqrt»
      [Var «center_certificate»;
       App «candle_cv_fs_result_center» [Var «result»]]
End

Definition registered_case10173_fsn_result_sqrt_hessian_body_def:
  registered_case10173_fsn_result_sqrt_hessian_body =
    App «candle_cv_fsn_sqrt_hessian»
      [Var «box_certificate»;
       App «candle_cv_fs_result_value_bound» [Var «result»];
       App «candle_cv_fs_result_gradient_bounds» [Var «result»];
       App «candle_cv_fs_result_hessian» [Var «result»]]
End

Definition registered_case10173_fsn_result_sqrt_body_def:
  registered_case10173_fsn_result_sqrt_body =
    App «candle_cv_fs_result_complete_rounded»
      [Var «radii»;
       registered_case10173_fsn_result_sqrt_domain_body;
       registered_case10173_fsn_result_sqrt_center_body;
       registered_case10173_fsn_result_sqrt_hessian_body]
End

Theorem registered_case10173_fsn_sqrt_domain_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsn_sqrt_domain» =
    SOME
      ([«certificate»;«fixed_interval»],
       registered_case10173_fsn_sqrt_domain_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsn_first_sqrt_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsn_first_sqrt» =
    SOME
      ([«certificate»;«first»],
       registered_case10173_fsn_first_sqrt_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsn_sqrt_hessian_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsn_sqrt_hessian» =
    SOME
      ([«certificate»;«value»;«gradient»;«hessian»],
       registered_case10173_fsn_sqrt_hessian_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsn_result_sqrt_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsn_result_sqrt» =
    SOME
      ([«radii»;«center_certificate»;«box_certificate»;«result»],
       registered_case10173_fsn_result_sqrt_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsn_sqrt_domain_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_domain»
        [from_cv certificate;from_cv fixed_interval]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«certificate»,from_cv certificate);
         («fixed_interval»,from_cv fixed_interval)]
        registered_case10173_fsn_sqrt_domain_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fsn_sqrt_domain_lookup]
QED

Theorem registered_case10173_fsn_first_sqrt_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_first_sqrt»
        [from_cv certificate;from_cv first_value]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«certificate»,from_cv certificate);
         («first»,from_cv first_value)]
        registered_case10173_fsn_first_sqrt_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fsn_first_sqrt_lookup]
QED

Theorem registered_case10173_fsn_sqrt_hessian_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_hessian»
        [from_cv certificate;from_cv value;from_cv gradient;from_cv hessian])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«certificate»,from_cv certificate);(«value»,from_cv value);
         («gradient»,from_cv gradient);(«hessian»,from_cv hessian)]
        registered_case10173_fsn_sqrt_hessian_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_fsn_sqrt_hessian_lookup]
QED

Theorem registered_case10173_fsn_result_sqrt_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_result_sqrt»
        [from_cv radii;from_cv center_certificate;
         from_cv box_certificate;from_cv result]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_certificate»,from_cv center_certificate);
         («box_certificate»,from_cv box_certificate);
         («result»,from_cv result)]
        registered_case10173_fsn_result_sqrt_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_fsn_result_sqrt_lookup]
QED

Theorem registered_case10173_fsn_result_sqrt_eval_from_components:
  1 < clock /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_certificate»,from_cv center_certificate);
         («box_certificate»,from_cv box_certificate);
         («result»,from_cv source_result)]
        registered_case10173_fsn_result_sqrt_domain_body) (refs:hol_refs) =
    (M_success (from_cv result_domain),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_certificate»,from_cv center_certificate);
         («box_certificate»,from_cv box_certificate);
         («result»,from_cv source_result)]
        registered_case10173_fsn_result_sqrt_center_body) refs =
    (M_success (from_cv center_result),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_certificate»,from_cv center_certificate);
         («box_certificate»,from_cv box_certificate);
         («result»,from_cv source_result)]
        registered_case10173_fsn_result_sqrt_hessian_body) refs =
    (M_success (from_cv hessian_result),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_rounded»
        [from_cv radii;from_cv result_domain;
         from_cv center_result;from_cv hessian_result]) refs =
    (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_result_sqrt»
        [from_cv radii;from_cv center_certificate;
         from_cv box_certificate;from_cv source_result]) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> rw [registered_case10173_fsn_result_sqrt_unfold]
  >> simp
       [registered_case10173_fsn_result_sqrt_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_complete_rounded»
            [from_cv radii;from_cv result_domain;
             from_cv center_result;from_cv hessian_result]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            registered_case10173_fsn_result_sqrt_domain_body_def,
            registered_case10173_fsn_result_sqrt_center_body_def,
            registered_case10173_fsn_result_sqrt_hessian_body_def]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
