(*****************************************************************************
 * Structural refinement of the historical Taylor square-root components.
 *
 * This layer removes the five-field result accessors surrounding the three
 * square-root operations.  It leaves only the numerical domain, first-order,
 * and Hessian calls to be related to the checked decimal witnesses.
 *****************************************************************************)
Theory compute_registeredCase10173ResultSqrtAccessorEval
Ancestors
  compute_registeredCase10173ResultSqrtEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fsn_result_sqrt_center_domain_direct_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_domain»
        [from_cv center_certificate;from_cv center_value])
      (refs:hol_refs) = (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_domain»
        [from_cv center_certificate;
         App «candle_cv_fs_first_value»
           [App «candle_cv_fs_result_center»
             [from_cv
               (Pair (Num 1)
                 (Pair (Pair center_value center_gradient)
                   (Pair value_bound
                     (Pair gradient_bounds hessian))))]]]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fsn_sqrt_domain»
            [from_cv center_certificate;from_cv center_value]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac
      >- irule compute_execProofTheory.compute_eval_from_cv
      >> irule
           compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_center_value_eval
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fsn_result_sqrt_box_domain_direct_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_domain»
        [from_cv box_certificate;from_cv value_bound])
      (refs:hol_refs) = (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_domain»
        [from_cv box_certificate;
         App «candle_cv_fs_result_value_bound»
           [from_cv
             (Pair (Num 1)
               (Pair (Pair center_value center_gradient)
                 (Pair value_bound
                   (Pair gradient_bounds hessian))))]]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fsn_sqrt_domain»
            [from_cv box_certificate;from_cv value_bound]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac
      >- irule compute_execProofTheory.compute_eval_from_cv
      >> irule
           compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_value_bound_eval
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fsn_result_sqrt_domain_direct_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_domain»
        [from_cv center_certificate;from_cv center_value])
      (refs:hol_refs) = (M_success (Num 1),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_domain»
        [from_cv box_certificate;from_cv value_bound]) refs =
    (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_certificate»,from_cv center_certificate);
         («box_certificate»,from_cv box_certificate);
         («result»,
          from_cv
            (Pair (Num 1)
              (Pair (Pair center_value center_gradient)
                (Pair value_bound (Pair gradient_bounds hessian)))))]
        registered_case10173_fsn_result_sqrt_domain_body) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173ResultSqrtEvalTheory.registered_case10173_fsn_result_sqrt_domain_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173RawWrapperEvalTheory.registered_case10173_bool_and_true_one_eval
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (match_mp_tac
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`center:cv` |-> `Pair center_value center_gradient`]
            compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_true_domain_normalized_eval))
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173RawWrapperEvalTheory.registered_case10173_bool_and_true_one_eval
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (match_mp_tac
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fsn_result_sqrt_center_domain_direct_eval)
      >> asm_rewrite_tac [])
  >> match_mp_tac
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fsn_result_sqrt_box_domain_direct_eval)
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fsn_result_sqrt_center_direct_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_first_sqrt»
        [from_cv center_certificate;
         from_cv (Pair center_value center_gradient)])
      (refs:hol_refs) = (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_certificate»,from_cv center_certificate);
         («box_certificate»,from_cv box_certificate);
         («result»,
          from_cv
            (Pair result_domain
              (Pair (Pair center_value center_gradient)
                (Pair value_bound (Pair gradient_bounds hessian)))))]
        registered_case10173_fsn_result_sqrt_center_body) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173ResultSqrtEvalTheory.registered_case10173_fsn_result_sqrt_center_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fsn_first_sqrt»
            [from_cv center_certificate;
             from_cv (Pair center_value center_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac
      >- irule compute_execProofTheory.compute_eval_from_cv
      >> simp [compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST [`center:cv` |-> `Pair center_value center_gradient`]
               compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_center_eval))
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fsn_result_sqrt_hessian_direct_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_hessian»
        [from_cv box_certificate;from_cv value_bound;
         from_cv gradient_bounds;from_cv hessian])
      (refs:hol_refs) = (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_certificate»,from_cv center_certificate);
         («box_certificate»,from_cv box_certificate);
         («result»,
          from_cv
            (Pair result_domain
              (Pair center
                (Pair value_bound (Pair gradient_bounds hessian)))))]
        registered_case10173_fsn_result_sqrt_hessian_body) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173ResultSqrtEvalTheory.registered_case10173_fsn_result_sqrt_hessian_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fsn_sqrt_hessian»
            [from_cv box_certificate;from_cv value_bound;
             from_cv gradient_bounds;from_cv hessian]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac
      >- irule compute_execProofTheory.compute_eval_from_cv
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_value_bound_eval)
          >> asm_rewrite_tac [])
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_gradient_bounds_eval)
          >> asm_rewrite_tac [])
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_hessian_eval)
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
