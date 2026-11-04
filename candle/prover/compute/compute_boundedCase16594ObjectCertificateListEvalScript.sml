(*****************************************************************************
 * Exact evaluator semantics for the production certificate-list helpers.
 * These generic results are shared by sqrt, inverse, and atan steps.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectCertificateListEval
Ancestors
  compute_boundedCase16594ObjectSqrtRuntimeCertificateContract
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_cval_list_has_body_def:
  bounded_case16594_object_cval_list_has_body =
    If (Uop Ispair (Var «position»))
      (compute_syntax$Num 0)
      (If (Binop Eq (Var «position») (compute_syntax$Num 0))
        (compute_syntax$Num 1)
        (If (Uop Ispair (Var «values»))
          (App «candle_cv_cval_list_has»
            [Binop Sub (Var «position») (compute_syntax$Num 1);
             Uop Snd (Var «values»)])
          (compute_syntax$Num 0)))
End

Definition bounded_case16594_object_cval_list_drop_body_def:
  bounded_case16594_object_cval_list_drop_body =
    If (Uop Ispair (Var «position»))
      (compute_syntax$Num 0)
      (If (Binop Eq (Var «position») (compute_syntax$Num 0))
        (Var «values»)
        (If (Uop Ispair (Var «values»))
          (App «candle_cv_cval_list_drop»
            [Binop Sub (Var «position») (compute_syntax$Num 1);
             Uop Snd (Var «values»)])
          (compute_syntax$Num 0)))
End

Definition bounded_case16594_object_cval_list_nth_body_def:
  bounded_case16594_object_cval_list_nth_body =
    Uop Fst
      (App «candle_cv_cval_list_drop»
        [Var «position»;Var «values»])
End

Theorem bounded_case16594_object_cval_list_has_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_cval_list_has» =
    SOME
      ([«position»;«values»],
       bounded_case16594_object_cval_list_has_body)
Proof
  rw [bounded_case16594_object_cval_list_has_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_cval_list_drop_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_cval_list_drop» =
    SOME
      ([«position»;«values»],
       bounded_case16594_object_cval_list_drop_body)
Proof
  rw [bounded_case16594_object_cval_list_drop_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_cval_list_nth_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_cval_list_nth» =
    SOME
      ([«position»;«values»],
       bounded_case16594_object_cval_list_nth_body)
Proof
  rw [bounded_case16594_object_cval_list_nth_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_cval_list_has_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_has»
        [from_cv position;from_cv values]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«position»,from_cv position);(«values»,from_cv values)]
        bounded_case16594_object_cval_list_has_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> simp [bounded_case16594_object_cval_list_has_lookup]
QED

Theorem bounded_case16594_object_cval_list_drop_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_drop»
        [from_cv position;from_cv values]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«position»,from_cv position);(«values»,from_cv values)]
        bounded_case16594_object_cval_list_drop_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> simp [bounded_case16594_object_cval_list_drop_lookup]
QED

Theorem bounded_case16594_object_cval_list_nth_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_nth»
        [from_cv position;from_cv values]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«position»,from_cv position);(«values»,from_cv values)]
        bounded_case16594_object_cval_list_nth_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> simp [bounded_case16594_object_cval_list_nth_lookup]
QED

Theorem bounded_case16594_object_cval_list_has_zero_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_has»
        [from_cv (compute_exec$Num 0);from_cv values]) (refs:hol_refs) =
    (M_success (from_cv (compute_exec$Num 1)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_cval_list_has_unfold]
  >> simp
       [bounded_case16594_object_cval_list_has_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> rw
       [compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_ispair_num,
        compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_eq_zero]
  >> simp
       [compute_boundedCase16594ObjectMulHessianCompleteEvalTheory.bounded_case16594_object_compute_eval_source_num,
        compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_cval_list_has_cons_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_has»
        [from_cv (compute_exec$Num position);from_cv rest])
      (refs:hol_refs) =
    (M_success (from_cv (compute_exec$Num 1)),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_has»
        [from_cv (compute_exec$Num (SUC position));
         from_cv (Pair item rest)]) refs =
    (M_success (from_cv (compute_exec$Num 1)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_cval_list_has_unfold]
  >> simp
       [bounded_case16594_object_cval_list_has_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> rw
       [compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_ispair_num,
        compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_eq_suc_zero,
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_if_ispair_pair]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_cval_list_has»
            [from_cv (compute_exec$Num position);from_cv rest]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> conj_tac
      >- simp
           [compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_binop_def,
            compute_evalTheory.do_arith_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [SIMP_RULE std_ss
              [compute_execTheory.from_cv_def]
              compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_snd])
  >> asm_rewrite_tac []
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_cval_list_has_eval:
  !position values clock refs.
    position <= LENGTH values /\
    3 * (position + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_has»
        [from_cv (compute_exec$Num position);
         from_cv (bounded_object_q_cv_list values)])
      (refs:hol_refs) =
    (M_success (from_cv (compute_exec$Num 1)),refs)
Proof
  Induct_on `position`
  >- (rpt strip_tac
      >> irule bounded_case16594_object_cval_list_has_zero_eval
      >> intLib.ARITH_TAC)
  >> Cases_on `values`
  >> rpt strip_tac
  >> gvs []
  >> PURE_REWRITE_TAC
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          bounded_case16594_object_cval_list_has_cons_eval)
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qpat_x_assum `!values clock refs. _`
       (qspecl_then [`t`,`clock - 1`,`refs`] mp_tac)
  >> impl_tac
  >- (conj_tac >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem bounded_case16594_object_cval_list_drop_zero_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_drop»
        [from_cv (compute_exec$Num 0);from_cv values]) (refs:hol_refs) =
    (M_success (from_cv values),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_cval_list_drop_unfold]
  >> simp
       [bounded_case16594_object_cval_list_drop_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_ispair_num,
        compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_eq_zero,
        compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_case16594_object_cval_list_drop_cons_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_drop»
        [from_cv (compute_exec$Num position);from_cv rest])
      (refs:hol_refs) =
    (M_success (from_cv completed_rest),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_drop»
        [from_cv (compute_exec$Num (SUC position));
         from_cv (Pair item rest)]) refs =
    (M_success (from_cv completed_rest),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_cval_list_drop_unfold]
  >> simp
       [bounded_case16594_object_cval_list_drop_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> rw
       [compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_ispair_num,
        compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_eq_suc_zero,
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_if_ispair_pair]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_cval_list_drop»
            [from_cv (compute_exec$Num position);from_cv rest]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> conj_tac
      >- simp
           [compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_binop_def,
            compute_evalTheory.do_arith_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [SIMP_RULE std_ss
              [compute_execTheory.from_cv_def]
              compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_snd])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_cval_list_drop_eval:
  !position values clock refs.
    position <= LENGTH values /\
    3 * (position + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_drop»
        [from_cv (compute_exec$Num position);
         from_cv (bounded_object_q_cv_list values)])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_cv_list (DROP position values))),refs)
Proof
  Induct_on `position`
  >- (rpt strip_tac
      >> simp
           [bounded_case16594_object_cval_list_drop_zero_eval])
  >> Cases_on `values`
  >> rpt strip_tac
  >> gvs []
  >> PURE_REWRITE_TAC
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        rich_listTheory.DROP]
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          bounded_case16594_object_cval_list_drop_cons_eval)
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qpat_x_assum `!values clock refs. _`
       (qspecl_then [`t`,`clock - 1`,`refs`] mp_tac)
  >> impl_tac
  >- (conj_tac >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem bounded_case16594_object_compute_eval_uop_fst_argument_result:
  compute_eval clock ceqs expression (refs:hol_refs) =
      (M_success (from_cv (Pair left right)),refs) ==>
  compute_eval clock ceqs (Uop Fst expression) refs =
    (M_success (from_cv left),refs)
Proof
  strip_tac
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_cval_list_nth_eval:
  position < LENGTH values /\
  4 * (position + 1) < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_cval_list_nth»
        [from_cv (compute_exec$Num position);
         from_cv (bounded_object_q_cv_list values)])
      (refs:hol_refs) =
    (M_success (from_cv (EL position values)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_cval_list_nth_unfold]
  >> simp
       [bounded_case16594_object_cval_list_nth_body_def,
        compute_evalTheory.subst_def]
  >> irule bounded_case16594_object_compute_eval_uop_fst_argument_result
  >> qexists_tac `bounded_object_q_cv_list (DROP (SUC position) values)`
  >> PURE_REWRITE_TAC
       [GSYM
          (CONJUNCT2
             compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def)]
  >> simp [GSYM rich_listTheory.DROP_CONS_EL]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          bounded_case16594_object_cval_list_drop_eval)
  >> conj_tac
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
