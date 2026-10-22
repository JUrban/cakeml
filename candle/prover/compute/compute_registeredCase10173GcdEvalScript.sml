(*****************************************************************************
 * Registered evaluator semantics for the bounded rational-normalizer GCD.
 *
 * The source uses a cv-encoded fuel list to keep Euclid iteration total.  We
 * prove the literal registered program returns the exact encoded bounded
 * state.  Later rational proofs deliberately depend only on the fact that the
 * result is numeric: q_normalize_verified independently validates every
 * proposed divisor before using it.
 *****************************************************************************)
Theory compute_registeredCase10173GcdEval
Ancestors
  compute_registeredCase10173TaylorWeightedRowsEval
Libs
  bossLib preamble intLib

Definition bounded_case10173_num_fuel_cv_def:
  bounded_case10173_num_fuel_cv 0 = Num 0 /\
  bounded_case10173_num_fuel_cv (SUC fuel) =
    Pair (Num 0) (bounded_case10173_num_fuel_cv fuel)
End

Definition bounded_case10173_gcd_state_def:
  bounded_case10173_gcd_state 0 a b = (a,b) /\
  bounded_case10173_gcd_state (SUC fuel) a b =
    if b = 0 then (a,b)
    else bounded_case10173_gcd_state fuel b (a MOD b)
End

Definition bounded_case10173_gcd_state_cv_def:
  bounded_case10173_gcd_state_cv fuel a b =
    Pair
      (Num (FST (bounded_case10173_gcd_state fuel a b)))
      (Num (SND (bounded_case10173_gcd_state fuel a b)))
End

Definition bounded_case10173_gcd_resume_state_def:
  bounded_case10173_gcd_resume_state (pair_state:num#num) =
    if SND pair_state = 0 then pair_state
    else
      bounded_case10173_gcd_state 128
        (FST pair_state) (SND pair_state)
End

Definition bounded_case10173_gcd_resume_cv_def:
  bounded_case10173_gcd_resume_cv left right =
    Pair
      (Num
        (FST
          (bounded_case10173_gcd_resume_state (left,right))))
      (Num
        (SND
          (bounded_case10173_gcd_resume_state (left,right))))
End

Definition bounded_case10173_gcd_finish_def:
  (bounded_case10173_gcd_finish (left:num) (right:num) : num) =
    if right = 0 then left else 1
End

Definition bounded_case10173_num_gcd_def:
  bounded_case10173_num_gcd a b =
    let first = bounded_case10173_gcd_state 128 a b in
    let final = bounded_case10173_gcd_resume_state first in
      bounded_case10173_gcd_finish (FST final) (SND final)
End

Definition registered_case10173_num_gcd_state_fuel_body_def:
  registered_case10173_num_gcd_state_fuel_body =
    If (Uop Ispair (Var «fuel»))
      (If (Binop Eq (Var «b») (Num 0))
        (Pair (Var «a») (Var «b»))
        (App «candle_cv_num_gcd_state_fuel»
          [Uop Snd (Var «fuel»);Var «b»;
           Binop Mod (Var «a») (Var «b»)]))
      (Pair (Var «a») (Var «b»))
End

Definition registered_case10173_num_gcd_state_chunk_body_def:
  registered_case10173_num_gcd_state_chunk_body =
    App «candle_cv_num_gcd_state_fuel»
      [from_cv (bounded_case10173_num_fuel_cv 128);
       Var «a»;Var «b»]
End

Definition registered_case10173_num_gcd_state_resume_body_def:
  registered_case10173_num_gcd_state_resume_body =
    If (Binop Eq (Uop Snd (Var «state»)) (Num 0))
      (Var «state»)
      (App «candle_cv_num_gcd_state_chunk»
        [Uop Fst (Var «state»);Uop Snd (Var «state»)])
End

Definition registered_case10173_num_gcd_state_finish_body_def:
  registered_case10173_num_gcd_state_finish_body =
    If (Binop Eq (Uop Snd (Var «state»)) (Num 0))
      (Uop Fst (Var «state»))
      (Num 1)
End

Definition registered_case10173_num_gcd_body_def:
  registered_case10173_num_gcd_body =
    App «candle_cv_num_gcd_state_finish»
      [App «candle_cv_num_gcd_state_resume»
        [App «candle_cv_num_gcd_state_chunk»
          [Var «a»;Var «b»]]]
End

Theorem registered_case10173_num_gcd_state_fuel_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_num_gcd_state_fuel» =
    SOME
      ([«fuel»;«a»;«b»],
       registered_case10173_num_gcd_state_fuel_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_num_gcd_state_chunk_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_num_gcd_state_chunk» =
    SOME
      ([«a»;«b»],
       registered_case10173_num_gcd_state_chunk_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_num_gcd_state_resume_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_num_gcd_state_resume» =
    SOME
      ([«state»],
       registered_case10173_num_gcd_state_resume_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_num_gcd_state_finish_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_num_gcd_state_finish» =
    SOME
      ([«state»],
       registered_case10173_num_gcd_state_finish_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_num_gcd_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_num_gcd» =
    SOME ([«a»;«b»],registered_case10173_num_gcd_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_num_gcd_state_fuel_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_state_fuel»
        [from_cv fuel;from_cv (Num a);from_cv (Num b)])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«fuel»,from_cv fuel);(«a»,from_cv (Num a));
         («b»,from_cv (Num b))]
        registered_case10173_num_gcd_state_fuel_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_num_gcd_state_fuel_lookup]
QED

Theorem registered_case10173_num_gcd_state_chunk_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_state_chunk»
        [from_cv (Num a);from_cv (Num b)]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«a»,from_cv (Num a));(«b»,from_cv (Num b))]
        registered_case10173_num_gcd_state_chunk_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_num_gcd_state_chunk_lookup]
QED

Theorem registered_case10173_num_gcd_state_resume_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_state_resume» [from_cv pair_state])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«state»,from_cv pair_state)]
        registered_case10173_num_gcd_state_resume_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_num_gcd_state_resume_lookup]
QED

Theorem registered_case10173_num_gcd_state_finish_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_state_finish» [from_cv pair_state])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«state»,from_cv pair_state)]
        registered_case10173_num_gcd_state_finish_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_num_gcd_state_finish_lookup]
QED

Theorem registered_case10173_num_gcd_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd»
        [from_cv (Num a);from_cv (Num b)]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«a»,from_cv (Num a));(«b»,from_cv (Num b))]
        registered_case10173_num_gcd_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_num_gcd_lookup]
QED

Theorem registered_case10173_num_gcd_state_fuel_subst:
  subst
      [(«fuel»,from_cv fuel);(«a»,Num a);(«b»,Num b)]
      registered_case10173_num_gcd_state_fuel_body =
    If (Uop Ispair (from_cv fuel))
      (If (Binop Eq (Num b) (Num 0))
        (Pair (Num a) (Num b))
        (App «candle_cv_num_gcd_state_fuel»
          [Uop Snd (from_cv fuel);Num b;Binop Mod (Num a) (Num b)]))
      (Pair (Num a) (Num b))
Proof
  simp
    [registered_case10173_num_gcd_state_fuel_body_def,
     compute_evalTheory.subst_def]
QED

Theorem registered_case10173_num_eq_zero_eval:
  compute_eval clock ceqs
      (Binop Eq (Num value) (Num 0)) (refs:hol_refs) =
    (M_success (Num (if value = 0 then 1 else 0)),refs)
Proof
  Cases_on `value = 0`
  >> simp
       [compute_execTheory.from_cv_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_num_gcd_state_fuel_eval:
  !fuel clock a b refs.
    fuel + 1 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd_state_fuel»
          [from_cv (bounded_case10173_num_fuel_cv fuel);
           from_cv (Num a);from_cv (Num b)]) (refs:hol_refs) =
      (M_success
        (from_cv (bounded_case10173_gcd_state_cv fuel a b)),refs)
Proof
  Induct_on `fuel`
  >- (rpt gen_tac
      >> strip_tac
      >> simp [registered_case10173_num_gcd_state_fuel_unfold]
      >> PURE_REWRITE_TAC
           [registered_case10173_num_gcd_state_fuel_subst]
      >> PURE_REWRITE_TAC [bounded_case10173_num_fuel_cv_def]
      >> PURE_REWRITE_TAC
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv]
      >> PURE_REWRITE_TAC [compute_execTheory.cv_case_def]
      >> BETA_TAC
      >> simp
           [bounded_case10173_gcd_state_cv_def,
            bounded_case10173_gcd_state_def,
            compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt gen_tac
  >> strip_tac
  >> simp [registered_case10173_num_gcd_state_fuel_unfold]
  >> PURE_REWRITE_TAC
       [registered_case10173_num_gcd_state_fuel_subst]
  >> PURE_REWRITE_TAC [bounded_case10173_num_fuel_cv_def]
  >> PURE_REWRITE_TAC
       [compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv]
  >> PURE_REWRITE_TAC [compute_execTheory.cv_case_def]
  >> BETA_TAC
  >> Cases_on `b = 0`
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (Binop Eq (Num b) (Num 0)) refs =
        (M_success (Num 1),refs)` by
        simp [registered_case10173_num_eq_zero_eval]
      >> simp
           [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
            bounded_case10173_gcd_state_cv_def,
            bounded_case10173_gcd_state_def,
            compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Binop Eq (Num b) (Num 0)) refs =
      (M_success (Num 0),refs)` by
       simp [registered_case10173_num_eq_zero_eval]
  >> simp
       [compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd_state_fuel»
          [Uop Snd
             (Pair (Num 0)
               (from_cv (bounded_case10173_num_fuel_cv fuel)));
           Num b;Binop Mod (Num a) (Num b)]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd_state_fuel»
          [from_cv (bounded_case10173_num_fuel_cv fuel);
           from_cv (Num b);from_cv (Num (a MOD b))]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> conj_tac
        >- simp
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_snd_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> conj_tac
        >- simp
             [compute_evalTheory.compute_eval_def,
              compute_execTheory.from_cv_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> simp
             [compute_evalTheory.compute_eval_def,
              compute_execTheory.from_cv_def,
              compute_evalTheory.do_binop_def,
              compute_evalTheory.do_arith_def,
              compute_syntaxTheory.SAFEMOD_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
  >> asm_rewrite_tac []
  >> qpat_x_assum `!clock a b refs. _`
       (qspecl_then [`clock - 1`,`b`,`a MOD b`,`refs`] mp_tac)
  >> impl_tac >- intLib.ARITH_TAC
  >> simp
       [bounded_case10173_gcd_state_cv_def,
        bounded_case10173_gcd_state_def]
QED

Theorem registered_case10173_num_gcd_state_chunk_eval:
  130 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_state_chunk»
        [from_cv (Num a);from_cv (Num b)]) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_case10173_gcd_state_cv 128 a b)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_num_gcd_state_chunk_unfold]
  >> simp
       [registered_case10173_num_gcd_state_chunk_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_num_gcd_state_fuel_eval)
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_num_gcd_state_resume_subst:
  subst
      [(«state»,from_cv (Pair (Num left) (Num right)))]
      registered_case10173_num_gcd_state_resume_body =
    If
      (Binop Eq
        (Uop Snd (from_cv (Pair (Num left) (Num right))))
        (Num 0))
      (from_cv (Pair (Num left) (Num right)))
      (App «candle_cv_num_gcd_state_chunk»
        [Uop Fst (from_cv (Pair (Num left) (Num right)));
         Uop Snd (from_cv (Pair (Num left) (Num right)))])
Proof
  simp
    [registered_case10173_num_gcd_state_resume_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv]
QED

Theorem registered_case10173_num_gcd_state_resume_eval:
  132 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_state_resume»
        [from_cv (Pair (Num left) (Num right))]) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_case10173_gcd_resume_cv left right)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_num_gcd_state_resume_unfold]
  >> PURE_REWRITE_TAC
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_num_gcd_state_resume_subst]
  >> Cases_on `right = 0`
  >- (simp
       [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        bounded_case10173_gcd_resume_cv_def,
        bounded_case10173_gcd_resume_state_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Binop Eq
          (Uop Snd (Pair (Num left) (Num right))) (Num 0)) refs =
      (M_success (Num 0),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_snd_def,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_eq_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd_state_chunk»
          [Uop Fst (from_cv (Pair (Num left) (Num right)));
           Uop Snd (from_cv (Pair (Num left) (Num right)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd_state_chunk»
          [from_cv (Num left);from_cv (Num right)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_pair,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_pair]
        >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
  >> fs [compute_execTheory.from_cv_def]
  >> simp
       [bounded_case10173_gcd_resume_cv_def,
        bounded_case10173_gcd_resume_state_def,
        bounded_case10173_gcd_state_cv_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_execTheory.from_cv_def,
          bounded_case10173_gcd_state_cv_def]
         registered_case10173_num_gcd_state_chunk_eval)
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_num_gcd_state_finish_subst:
  subst
      [(«state»,from_cv (Pair (Num left) (Num right)))]
      registered_case10173_num_gcd_state_finish_body =
    If
      (Binop Eq
        (Uop Snd (from_cv (Pair (Num left) (Num right))))
        (Num 0))
      (Uop Fst (from_cv (Pair (Num left) (Num right))))
      (Num 1)
Proof
  simp
    [registered_case10173_num_gcd_state_finish_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv]
QED

Theorem registered_case10173_num_gcd_state_finish_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd_state_finish»
        [from_cv (Pair (Num left) (Num right))]) (refs:hol_refs) =
    (M_success
      (from_cv (Num (bounded_case10173_gcd_finish left right))),refs)
Proof
  strip_tac
  >> simp [registered_case10173_num_gcd_state_finish_unfold]
  >> PURE_REWRITE_TAC
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_num_gcd_state_finish_subst]
  >> Cases_on `right = 0`
  >- simp
       [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success,
        bounded_case10173_gcd_finish_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Binop Eq
          (Uop Snd (Pair (Num left) (Num right))) (Num 0)) refs =
      (M_success (Num 0),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_snd_def,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_eq_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero,
        bounded_case10173_gcd_finish_def,
        compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_num_gcd_subst:
  subst
      [(«a»,from_cv (Num a));(«b»,from_cv (Num b))]
      registered_case10173_num_gcd_body =
    App «candle_cv_num_gcd_state_finish»
      [App «candle_cv_num_gcd_state_resume»
        [App «candle_cv_num_gcd_state_chunk»
          [from_cv (Num a);from_cv (Num b)]]]
Proof
  simp
    [registered_case10173_num_gcd_body_def,
     compute_evalTheory.subst_def]
QED

Theorem registered_case10173_num_gcd_eval:
  134 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_num_gcd»
        [from_cv (Num a);from_cv (Num b)]) (refs:hol_refs) =
    (M_success
      (from_cv (Num (bounded_case10173_num_gcd a b))),refs)
Proof
  strip_tac
  >> simp [registered_case10173_num_gcd_unfold]
  >> PURE_REWRITE_TAC
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_num_gcd_subst]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd_state_resume»
          [App «candle_cv_num_gcd_state_chunk»
            [Num a;Num b]]) refs =
      (M_success
        (from_cv
          (bounded_case10173_gcd_resume_cv
            (FST (bounded_case10173_gcd_state 128 a b))
            (SND (bounded_case10173_gcd_state 128 a b)))),refs)` by
       (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_num_gcd_state_resume»
            [App «candle_cv_num_gcd_state_chunk»
              [Num a;Num b]]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_num_gcd_state_resume»
            [from_cv (bounded_case10173_gcd_state_cv 128 a b)]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> conj_tac >- intLib.ARITH_TAC
           >> irule
                (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                  registered_case10173_num_gcd_state_chunk_eval)
           >> intLib.ARITH_TAC)
        >> asm_rewrite_tac []
        >> simp
             [bounded_case10173_gcd_state_cv_def,
              bounded_case10173_gcd_resume_cv_def,
              compute_execTheory.from_cv_def]
        >> irule
             (SIMP_RULE std_ss
               [compute_execTheory.from_cv_def,
                bounded_case10173_gcd_resume_cv_def,
                pairTheory.PAIR]
               (Q.INST
                 [`left` |->
                    `FST (bounded_case10173_gcd_state 128 a b)`,
                  `right` |->
                    `SND (bounded_case10173_gcd_state 128 a b)`]
                 registered_case10173_num_gcd_state_resume_eval))
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd_state_finish»
          [App «candle_cv_num_gcd_state_resume»
            [App «candle_cv_num_gcd_state_chunk»
              [Num a;Num b]]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_num_gcd_state_finish»
          [from_cv
            (bounded_case10173_gcd_resume_cv
              (FST (bounded_case10173_gcd_state 128 a b))
              (SND (bounded_case10173_gcd_state 128 a b)))]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp [])
  >> asm_rewrite_tac []
  >> simp
       [bounded_case10173_gcd_resume_cv_def,
        bounded_case10173_num_gcd_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_num_gcd_state_finish_eval)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
