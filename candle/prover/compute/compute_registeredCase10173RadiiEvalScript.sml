(*****************************************************************************
 * Registered evaluator semantics for the fixed-radius projection.
 *
 * The historical program stores each already-rounded fixed radius as a
 * rational pair.  [candle_cv_fs_list_of_q] deliberately discards the common
 * denominator and retains the signed fixed numerator.  This theory proves
 * that structural projection once, independently of the numerical checker.
 *****************************************************************************)
Theory compute_registeredCase10173RadiiEval
Ancestors
  compute_registeredCase10173HistCompletionEval
Libs
  bossLib preamble

Definition registered_case10173_q_cv_list_def:
  registered_case10173_q_cv_list ([]:(cv # cv) list) = (Num 0 : cv) /\
  registered_case10173_q_cv_list ((numerator,denominator)::rest) =
    Pair (Pair numerator denominator)
      (registered_case10173_q_cv_list rest)
End

Definition registered_case10173_q_numerator_cv_list_def:
  registered_case10173_q_numerator_cv_list ([]:(cv # cv) list) =
      (Num 0 : cv) /\
  registered_case10173_q_numerator_cv_list
      ((numerator,denominator)::rest) =
    Pair numerator (registered_case10173_q_numerator_cv_list rest)
End

Definition registered_case10173_fs_list_of_q_body_def:
  registered_case10173_fs_list_of_q_body =
    If (Uop Ispair (Var «items»))
      (Pair
        (Uop Fst (Uop Fst (Var «items»)))
        (App «candle_cv_fs_list_of_q» [Uop Snd (Var «items»)]))
      (Num 0)
End

Theorem registered_case10173_fs_list_of_q_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_list_of_q» =
    SOME ([«items»],registered_case10173_fs_list_of_q_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_list_of_q_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_list_of_q» [from_cv items])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«items»,from_cv items)]
        registered_case10173_fs_list_of_q_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_list_of_q_lookup]
QED

Theorem registered_case10173_fs_list_of_q_nil_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_list_of_q» [from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success (Num 0),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_list_of_q_unfold]
  >> simp
       [registered_case10173_fs_list_of_q_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_list_of_q_cons_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (Uop Fst (from_cv item))
      (refs:hol_refs) =
    (M_success (from_cv numerator),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_list_of_q» [from_cv rest])
      refs =
    (M_success (from_cv converted_rest),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_list_of_q»
        [from_cv (Pair item rest)]) refs =
    (M_success (from_cv (Pair numerator converted_rest)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_list_of_q_unfold]
  >> simp
       [registered_case10173_fs_list_of_q_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Uop Fst
          (Uop Fst
            (Pair (from_cv item) (from_cv rest)))) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Uop Fst (from_cv item)) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_uop_argument_cong
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
              compute_execProofTheory.compute_eval_from_cv])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_list_of_q»
          [Uop Snd
            (Pair (from_cv item) (from_cv rest))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_list_of_q» [from_cv rest]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_list_of_q_projection_eval:
  !items clock refs.
    LENGTH items + 1 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_list_of_q»
          [from_cv (registered_case10173_q_cv_list items)])
        (refs:hol_refs) =
      (M_success
        (from_cv (registered_case10173_q_numerator_cv_list items)),refs)
Proof
  Induct
  >- (rw
        [registered_case10173_q_cv_list_def,
         registered_case10173_q_numerator_cv_list_def]
      >> irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_list_of_q_nil_eval)
      >> intLib.ARITH_TAC)
  >> Cases
  >> rw
       [registered_case10173_q_cv_list_def,
        registered_case10173_q_numerator_cv_list_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_execTheory.from_cv_def]
         (Q.INST
           [`item` |-> `(Pair q r:cv)`,
            `rest` |-> `registered_case10173_q_cv_list items`,
            `numerator` |-> `q`,
            `converted_rest` |->
              `registered_case10173_q_numerator_cv_list items`]
           registered_case10173_fs_list_of_q_cons_eval))
  >> conj_tac
  >- intLib.ARITH_TAC
  >> conj_tac
  >- (qpat_x_assum `!clock refs. _`
        (qspecl_then [`clock - 1`,`refs`] assume_tac)
      >> qpat_x_assum `_ ==> _` mp_tac
      >> impl_tac >- intLib.ARITH_TAC
      >> simp [])
  >- simp
       [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
QED

val _ = export_theory ();
