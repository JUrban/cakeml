(*****************************************************************************
 * Exact evaluator semantics for the linear object-q negation primitives.
 *
 * These lemmas cross the first numerical part of the object-state bridge:
 * the authenticated rational and interval negation bodies, recursive list
 * negation, and the canonical zero gradient/Hessian vectors all evaluate to
 * their exact cv representations under the production equation environment.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectLinearEval
Ancestors
  compute_boundedCase16594ObjectPolyStepControlEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_compute_eval_app1_argument_result:
  0 < clock /\
  compute_eval clock ceqs argument (refs:hol_refs) =
      (M_success (from_cv argument_result),refs) ==>
  compute_eval clock ceqs (App function_name [argument]) refs =
    compute_eval clock ceqs
      (App function_name [from_cv argument_result]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 1`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_pair_fst:
  compute_eval clock ceqs
      (Uop Fst (from_cv (Pair left right))) (refs:hol_refs) =
    (M_success (from_cv left),refs)
Proof
  simp
    [compute_execTheory.from_cv_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
     compute_execProofTheory.compute_eval_from_cv,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_pair_snd:
  compute_eval clock ceqs
      (Uop Snd (from_cv (Pair left right))) (refs:hol_refs) =
    (M_success (from_cv right),refs)
Proof
  simp
    [compute_execTheory.from_cv_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
     compute_execProofTheory.compute_eval_from_cv,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Definition bounded_case16594_object_q_neg_body_def:
  bounded_case16594_object_q_neg_body =
    Pair
      (Pair (Uop Snd (Uop Fst (Var «x»)))
        (Uop Fst (Uop Fst (Var «x»))))
      (Uop Snd (Var «x»))
End

Theorem bounded_case16594_object_q_neg_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_neg» =
    SOME ([«x»],bounded_case16594_object_q_neg_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_q_neg_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_neg» [from_cv rational_cv]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«x»,from_cv rational_cv)]
        bounded_case16594_object_q_neg_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_q_neg_lookup
QED

Theorem bounded_case16594_object_q_neg_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_neg»
        [from_cv (Pair (Pair positive negative) denominator)])
      (refs:hol_refs) =
    (M_success
      (from_cv (Pair (Pair negative positive) denominator)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_q_neg_unfold]
  >> simp
       [bounded_case16594_object_q_neg_body_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Definition bounded_case16594_object_q_interval_neg_body_def:
  bounded_case16594_object_q_interval_neg_body =
    Pair
      (App «candle_cv_q_neg» [Uop Snd (Var «x»)])
      (App «candle_cv_q_neg» [Uop Fst (Var «x»)])
End

Theorem bounded_case16594_object_q_interval_neg_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_interval_neg» =
    SOME ([«x»],bounded_case16594_object_q_interval_neg_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_q_interval_neg_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_neg» [from_cv interval_cv])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«x»,from_cv interval_cv)]
        bounded_case16594_object_q_interval_neg_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_q_interval_neg_lookup
QED

Theorem bounded_case16594_object_q_neg_after_fst_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_neg»
        [Uop Fst (from_cv
          (Pair
            (Pair (Pair lower_positive lower_negative) lower_denominator)
            (Pair (Pair upper_positive upper_negative) upper_denominator)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair lower_negative lower_positive) lower_denominator)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_neg»
            [from_cv
              (Pair (Pair lower_positive lower_negative)
                lower_denominator)]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app1_argument_result
      >> asm_rewrite_tac [bounded_case16594_object_compute_eval_pair_fst])
  >> irule bounded_case16594_object_q_neg_eval
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_q_neg_after_snd_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_neg»
        [Uop Snd (from_cv
          (Pair
            (Pair (Pair lower_positive lower_negative) lower_denominator)
            (Pair (Pair upper_positive upper_negative) upper_denominator)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair upper_negative upper_positive) upper_denominator)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_neg»
            [from_cv
              (Pair (Pair upper_positive upper_negative)
                upper_denominator)]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app1_argument_result
      >> asm_rewrite_tac [bounded_case16594_object_compute_eval_pair_snd])
  >> irule bounded_case16594_object_q_neg_eval
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_q_interval_neg_eval:
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_neg»
        [from_cv
          (Pair
            (Pair (Pair lower_positive lower_negative) lower_denominator)
            (Pair (Pair upper_positive upper_negative) upper_denominator))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Pair upper_negative upper_positive) upper_denominator)
          (Pair (Pair lower_negative lower_positive) lower_denominator))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_q_interval_neg_unfold]
  >> simp
       [bounded_case16594_object_q_interval_neg_body_def,
        compute_evalTheory.subst_def]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          bounded_case16594_object_q_neg_after_snd_eval)
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_q_neg_after_fst_eval)
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_interval_list_neg_body_def:
  bounded_case16594_object_interval_list_neg_body =
    If (Uop Ispair (Var «items»))
      (Pair
        (App «candle_cv_q_interval_neg» [Uop Fst (Var «items»)])
        (App «candle_cv_q_dim_interval_list_neg» [Uop Snd (Var «items»)]))
      (Num 0)
End

Theorem bounded_case16594_object_interval_list_neg_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_dim_interval_list_neg» =
    SOME ([«items»],bounded_case16594_object_interval_list_neg_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_interval_list_neg_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg» [from_cv items])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«items»,from_cv items)]
        bounded_case16594_object_interval_list_neg_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_interval_list_neg_lookup
QED

Theorem bounded_case16594_object_interval_list_neg_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg» [from_cv (Num 0)])
      (refs:hol_refs) = (M_success (from_cv (Num 0)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_interval_list_neg_unfold]
  >> simp
       [bounded_case16594_object_interval_list_neg_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_interval_neg_after_fst_eval:
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_neg»
        [Uop Fst
          (from_cv
            (Pair
              (Pair
                (Pair (Pair lower_positive lower_negative) lower_denominator)
                (Pair (Pair upper_positive upper_negative) upper_denominator))
              rest))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Pair upper_negative upper_positive) upper_denominator)
          (Pair (Pair lower_negative lower_positive) lower_denominator))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_neg»
            [from_cv
              (Pair
                (Pair (Pair lower_positive lower_negative) lower_denominator)
                (Pair (Pair upper_positive upper_negative) upper_denominator))])
          refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app1_argument_result
      >> asm_rewrite_tac [bounded_case16594_object_compute_eval_pair_fst]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_q_interval_neg_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_list_neg_after_snd_eval:
  0 < clock /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg» [from_cv rest])
      (refs:hol_refs) = (M_success (from_cv result),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [Uop Snd (from_cv (Pair item rest))]) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_dim_interval_list_neg» [from_cv rest]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app1_argument_result
      >> asm_rewrite_tac [bounded_case16594_object_compute_eval_pair_snd])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_compute_eval_if_ispair_from_cv_pair:
  compute_eval clock ceqs
      (If (Uop Ispair (from_cv (Pair left right)))
        yes_branch no_branch) (refs:hol_refs) =
    compute_eval clock ceqs yes_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_interval_list_neg_subst_cons:
  subst [(«items»,from_cv (Pair item rest))]
      bounded_case16594_object_interval_list_neg_body =
    If (Uop Ispair (from_cv (Pair item rest)))
      (Pair
        (App «candle_cv_q_interval_neg»
          [Uop Fst (from_cv (Pair item rest))])
        (App «candle_cv_q_dim_interval_list_neg»
          [Uop Snd (from_cv (Pair item rest))]))
      (Num 0)
Proof
  simp_tac (pure_ss)
    [bounded_case16594_object_interval_list_neg_body_def,
     compute_evalTheory.subst_def,listTheory.MAP,
     alistTheory.ALOOKUP_def,boolTheory.EQ_REFL,
     boolTheory.COND_CLAUSES,optionTheory.option_case_def]
QED

Theorem bounded_case16594_object_interval_list_neg_cons_eval:
  2 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg» [from_cv rest])
      (refs:hol_refs) = (M_success (from_cv negated_rest),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [from_cv
          (Pair
            (Pair
              (Pair (Pair lower_positive lower_negative) lower_denominator)
              (Pair (Pair upper_positive upper_negative) upper_denominator))
            rest)]) refs =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Pair (Pair upper_negative upper_positive) upper_denominator)
            (Pair (Pair lower_negative lower_positive) lower_denominator))
          negated_rest)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«items»,from_cv
              (Pair
                (Pair
                  (Pair (Pair lower_positive lower_negative) lower_denominator)
                  (Pair (Pair upper_positive upper_negative) upper_denominator))
                rest))]
            bounded_case16594_object_interval_list_neg_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_interval_list_neg_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [bounded_case16594_object_interval_list_neg_subst_cons]
  >> rw [bounded_case16594_object_compute_eval_if_ispair_from_cv_pair]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          bounded_case16594_object_interval_neg_after_fst_eval)
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`item` |->
              `Pair
                (Pair (Pair lower_positive lower_negative) lower_denominator)
                (Pair (Pair upper_positive upper_negative) upper_denominator)`]
           bounded_case16594_object_list_neg_after_snd_eval))
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_interval_list_neg_zero_replicate_eval:
  !count clock refs.
    count + 2 < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [from_cv
          (bounded_case16594_object_cv_list
            (REPLICATE count
              bounded_case16594_object_zero_interval_cv))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_cv_list
          (REPLICATE count
            bounded_case16594_object_zero_interval_cv))),refs)
Proof
  Induct
  >- (rpt strip_tac
      >> PURE_REWRITE_TAC
           [rich_listTheory.REPLICATE,
            bounded_case16594_object_cv_list_def]
      >> irule bounded_case16594_object_interval_list_neg_nil_eval
      >> intLib.ARITH_TAC)
  >> rpt strip_tac
  >> PURE_REWRITE_TAC
       [rich_listTheory.REPLICATE,
        bounded_case16594_object_cv_list_def,
        bounded_case16594_object_zero_interval_cv_def]
  >> irule bounded_case16594_object_interval_list_neg_cons_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> PURE_REWRITE_TAC [GSYM bounded_case16594_object_zero_interval_cv_def]
  >> first_x_assum irule
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_zero_gradient6_neg_eval:
  8 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [from_cv bounded_case16594_object_zero_gradient6_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_zero_gradient6_cv),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_zero_gradient6_cv_def]
  >> irule bounded_case16594_object_interval_list_neg_zero_replicate_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_zero_hessian21_neg_eval:
  23 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [from_cv bounded_case16594_object_zero_hessian21_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_zero_hessian21_cv),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_zero_hessian21_cv_def]
  >> irule bounded_case16594_object_interval_list_neg_zero_replicate_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
