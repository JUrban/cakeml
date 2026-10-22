(*****************************************************************************
 * Structural evaluator facts for fixed-scale Taylor-result projections.
 *
 * Ordinary polynomial, square-root, product, and addition refinements all
 * consume the same five-field source result.  Proving its projections once
 * keeps the packet-parametric numerical bridge independent of closed source
 * evaluation and of any particular certificate cell.
 *****************************************************************************)
Theory compute_registeredCase10173ResultAccessorEval
Ancestors
  compute_registeredCase10173TaylorCompleteObjectEval
Libs
  bossLib preamble

Definition registered_case10173_fs_result_domain_body_def:
  registered_case10173_fs_result_domain_body =
    Uop Fst (Var «result»)
End

Definition registered_case10173_fs_result_center_body_def:
  registered_case10173_fs_result_center_body =
    Uop Fst (Uop Snd (Var «result»))
End

Definition registered_case10173_fs_result_value_bound_body_def:
  registered_case10173_fs_result_value_bound_body =
    Uop Fst (Uop Snd (Uop Snd (Var «result»)))
End

Definition registered_case10173_fs_result_gradient_bounds_body_def:
  registered_case10173_fs_result_gradient_bounds_body =
    Uop Fst (Uop Snd (Uop Snd (Uop Snd (Var «result»))))
End

Definition registered_case10173_fs_result_hessian_body_def:
  registered_case10173_fs_result_hessian_body =
    Uop Snd (Uop Snd (Uop Snd (Uop Snd (Var «result»))))
End

Theorem registered_case10173_fs_result_domain_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_domain» =
    SOME ([«result»],registered_case10173_fs_result_domain_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_center_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_center» =
    SOME ([«result»],registered_case10173_fs_result_center_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_value_bound_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_value_bound» =
    SOME ([«result»],registered_case10173_fs_result_value_bound_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_gradient_bounds_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_gradient_bounds» =
    SOME ([«result»],registered_case10173_fs_result_gradient_bounds_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_hessian_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_hessian» =
    SOME ([«result»],registered_case10173_fs_result_hessian_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_domain_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_domain»
        [from_cv
          (Pair (result_domain:cv)
            (Pair center
              (Pair value_bound (Pair gradient_bounds hessian))))])
      (refs:hol_refs) =
    (M_success (from_cv result_domain),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_result_domain_lookup,
        registered_case10173_fs_result_domain_body_def,
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

Theorem registered_case10173_fs_result_center_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_center»
        [from_cv
          (Pair (result_domain:cv)
            (Pair center
              (Pair value_bound (Pair gradient_bounds hessian))))])
      (refs:hol_refs) =
    (M_success (from_cv center),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_result_center_lookup,
        registered_case10173_fs_result_center_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_result_value_bound_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_value_bound»
        [from_cv
          (Pair (result_domain:cv)
            (Pair center
              (Pair value_bound (Pair gradient_bounds hessian))))])
      (refs:hol_refs) =
    (M_success (from_cv value_bound),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_result_value_bound_lookup,
        registered_case10173_fs_result_value_bound_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_result_gradient_bounds_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_gradient_bounds»
        [from_cv
          (Pair (result_domain:cv)
            (Pair center
              (Pair value_bound (Pair gradient_bounds hessian))))])
      (refs:hol_refs) =
    (M_success (from_cv gradient_bounds),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_result_gradient_bounds_lookup,
        registered_case10173_fs_result_gradient_bounds_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_result_hessian_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_hessian»
        [from_cv
          (Pair (result_domain:cv)
            (Pair center
              (Pair value_bound (Pair gradient_bounds hessian))))])
      (refs:hol_refs) =
    (M_success (from_cv hessian),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_result_hessian_lookup,
        registered_case10173_fs_result_hessian_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_result_center_value_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_value»
        [App «candle_cv_fs_result_center»
          [from_cv
            (Pair (result_domain:cv)
              (Pair (Pair center_value center_gradient)
                (Pair value_bound (Pair gradient_bounds hessian))))]])
      (refs:hol_refs) =
    (M_success (from_cv center_value),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_first_value»
          [App «candle_cv_fs_result_center»
            [from_cv
              (Pair (result_domain:cv)
                (Pair (Pair center_value center_gradient)
                  (Pair value_bound (Pair gradient_bounds hessian))))]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_first_value»
          [from_cv (Pair center_value center_gradient)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- asm_rewrite_tac []
        >> irule registered_case10173_fs_result_center_eval
        >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
  >> irule
       compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_first_value_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_center_gradient_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_gradient»
        [App «candle_cv_fs_result_center»
          [from_cv
            (Pair (result_domain:cv)
              (Pair (Pair center_value center_gradient)
                (Pair value_bound (Pair gradient_bounds hessian))))]])
      (refs:hol_refs) =
    (M_success (from_cv center_gradient),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_first_gradient»
          [App «candle_cv_fs_result_center»
            [from_cv
              (Pair (result_domain:cv)
                (Pair (Pair center_value center_gradient)
                  (Pair value_bound (Pair gradient_bounds hessian))))]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_first_gradient»
          [from_cv (Pair center_value center_gradient)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- asm_rewrite_tac []
        >> irule registered_case10173_fs_result_center_eval
        >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
  >> irule
       compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_first_gradient_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_true_domain_normalized_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_domain»
        [Pair (Num 1)
          (Pair (from_cv center)
            (Pair (from_cv value_bound)
              (Pair (from_cv gradient_bounds) (from_cv hessian))))])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  mp_tac
    (Q.INST [`result_domain:cv` |-> `Num 1`]
      registered_case10173_fs_result_domain_eval)
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_fs_result_center_value_normalized_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_value»
        [App «candle_cv_fs_result_center»
          [Pair (from_cv result_domain)
            (Pair (Pair (from_cv center_value) (from_cv center_gradient))
              (Pair (from_cv value_bound)
                (Pair (from_cv gradient_bounds) (from_cv hessian))))]])
      (refs:hol_refs) =
    (M_success (from_cv center_value),refs)
Proof
  mp_tac registered_case10173_fs_result_center_value_eval
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_fs_result_center_gradient_normalized_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_gradient»
        [App «candle_cv_fs_result_center»
          [Pair (from_cv result_domain)
            (Pair (Pair (from_cv center_value) (from_cv center_gradient))
              (Pair (from_cv value_bound)
                (Pair (from_cv gradient_bounds) (from_cv hessian))))]])
      (refs:hol_refs) =
    (M_success (from_cv center_gradient),refs)
Proof
  mp_tac registered_case10173_fs_result_center_gradient_eval
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_fs_result_hessian_normalized_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_hessian»
        [Pair (from_cv result_domain)
          (Pair (from_cv center)
            (Pair (from_cv value_bound)
              (Pair (from_cv gradient_bounds) (from_cv hessian))))])
      (refs:hol_refs) =
    (M_success (from_cv hessian),refs)
Proof
  mp_tac registered_case10173_fs_result_hessian_eval
  >> simp [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
