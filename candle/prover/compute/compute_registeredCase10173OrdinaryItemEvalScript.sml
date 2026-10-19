(*****************************************************************************
 * Structural evaluator semantics for fixed ordinary-program items.
 *
 * The case-10173 source prefix, historical instruction, and suffix all carry
 * fixed Taylor results with tag 1.  Prove the item selectors once so the
 * numerical prefix/suffix refinement can work directly with their payloads.
 *****************************************************************************)
Theory compute_registeredCase10173OrdinaryItemEval
Ancestors
  compute_registeredCase10173ProgramTemplatePacketEval
Libs
  bossLib preamble

Definition registered_case10173_fsa_item_is_fixed_body_def:
  registered_case10173_fsa_item_is_fixed_body =
    Binop Eq (Uop Fst (Var «item»)) (Num 1)
End

Definition registered_case10173_fsa_item_payload_body_def:
  registered_case10173_fsa_item_payload_body = Uop Snd (Var «item»)
End

Definition registered_case10173_fsa_item_to_fixed_body_def:
  registered_case10173_fsa_item_to_fixed_body =
    If (App «candle_cv_fsa_item_is_fixed» [Var «item»])
      (App «candle_cv_fsa_item_payload» [Var «item»])
      (App «candle_cv_fsa_result_of_q»
        [App «candle_cv_fsa_item_payload» [Var «item»]])
End

Definition registered_case10173_fsa_item_head_body_def:
  registered_case10173_fsa_item_head_body =
    If (Uop Ispair (Var «stack»))
      (Uop Fst (Var «stack»))
      (App «candle_cv_fsa_item_default»
        [Var «center_boxes»;Var «boxes»])
End

Definition registered_case10173_fsa_item_tail_body_def:
  registered_case10173_fsa_item_tail_body =
    If (Uop Ispair (Var «stack»))
      (Uop Snd (Var «stack»)) (Num 0)
End

Theorem registered_case10173_fsa_item_is_fixed_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsa_item_is_fixed» =
    SOME ([«item»],registered_case10173_fsa_item_is_fixed_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsa_item_payload_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsa_item_payload» =
    SOME ([«item»],registered_case10173_fsa_item_payload_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsa_item_to_fixed_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsa_item_to_fixed» =
    SOME ([«item»],registered_case10173_fsa_item_to_fixed_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsa_item_head_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsa_item_head» =
    SOME
      ([«center_boxes»;«boxes»;«stack»],
       registered_case10173_fsa_item_head_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsa_item_tail_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsa_item_tail» =
    SOME ([«stack»],registered_case10173_fsa_item_tail_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsa_item_to_fixed_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_to_fixed» [from_cv item])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«item»,from_cv item)]
        registered_case10173_fsa_item_to_fixed_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fsa_item_to_fixed_lookup]
QED

Theorem registered_case10173_fsa_item_is_fixed_fixed_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_is_fixed»
        [from_cv (Pair (Num 1) result)])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fsa_item_is_fixed_lookup,
        registered_case10173_fsa_item_is_fixed_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fsa_item_payload_fixed_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_payload»
        [from_cv (Pair (Num 1) result)])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fsa_item_payload_lookup,
        registered_case10173_fsa_item_payload_body_def,
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

Theorem registered_case10173_fsa_item_to_fixed_body_fixed_subst:
  subst [(«item»,from_cv (Pair (Num 1) result))]
      registered_case10173_fsa_item_to_fixed_body =
    If
      (App «candle_cv_fsa_item_is_fixed»
        [from_cv (Pair (Num 1) result)])
      (App «candle_cv_fsa_item_payload»
        [from_cv (Pair (Num 1) result)])
      (App «candle_cv_fsa_result_of_q»
        [App «candle_cv_fsa_item_payload»
          [from_cv (Pair (Num 1) result)]])
Proof
  simp
    [registered_case10173_fsa_item_to_fixed_body_def,
     compute_evalTheory.subst_def]
QED

Theorem registered_case10173_fsa_item_to_fixed_fixed_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_to_fixed»
        [from_cv (Pair (Num 1) result)])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst [(«item»,from_cv (Pair (Num 1) result))]
            registered_case10173_fsa_item_to_fixed_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fsa_item_to_fixed_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_fsa_item_to_fixed_body_fixed_subst]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fsa_item_payload»
            [from_cv (Pair (Num 1) result)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success
      >> qexists_tac `0`
      >> simp [registered_case10173_fsa_item_is_fixed_fixed_eval])
  >> irule registered_case10173_fsa_item_payload_fixed_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fsa_item_head_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_head»
        [from_cv center_boxes;from_cv boxes;from_cv (Pair item stack)])
      (refs:hol_refs) = (M_success (from_cv item),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fsa_item_head_lookup,
        registered_case10173_fsa_item_head_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fsa_item_tail_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_tail» [from_cv (Pair item stack)])
      (refs:hol_refs) = (M_success (from_cv stack),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fsa_item_tail_lookup,
        registered_case10173_fsa_item_tail_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
