(*****************************************************************************
 * Exact evaluator semantics for the production object-addition list core.
 * State recompletion and the semantic Taylor relation are composed above
 * this reusable matched-list evaluator.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAddEval
Ancestors
  compute_boundedCase16594ObjectPolyBaseStepSemanticEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_interval_list_add_body_def:
  bounded_case16594_object_interval_list_add_body =
    If (Uop Ispair (Var «xs»))
      (If (Uop Ispair (Var «ys»))
        (Pair
          (App «candle_cv_q_interval_add»
            [Uop Fst (Var «xs»);Uop Fst (Var «ys»)])
          (App «candle_cv_q_packed_object_interval_list_add»
            [Uop Snd (Var «xs»);Uop Snd (Var «ys»)]))
        (compute_syntax$Num 0))
      (compute_syntax$Num 0)
End

Theorem bounded_case16594_object_interval_list_add_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_interval_list_add» =
    SOME
      ([«xs»;«ys»],bounded_case16594_object_interval_list_add_body)
Proof
  rw [bounded_case16594_object_interval_list_add_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_interval_list_add_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_add»
        [from_cv xs;from_cv ys]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«xs»,from_cv xs);(«ys»,from_cv ys)]
        bounded_case16594_object_interval_list_add_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_interval_list_add_lookup
QED

Theorem bounded_case16594_object_interval_list_add_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_add»
        [from_cv (compute_exec$Num 0);from_cv (compute_exec$Num 0)])
      (refs:hol_refs) =
    (M_success (from_cv (compute_exec$Num 0)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_interval_list_add_unfold]
  >> simp
       [bounded_case16594_object_interval_list_add_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_interval_list_add_cons_eval:
  bounded_packed_q_interval_encoded left_entry /\
  bounded_packed_q_interval_encoded right_entry /\
  6 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_add»
        [from_cv left_rest;from_cv right_rest]) (refs:hol_refs) =
    (M_success (from_cv completed_rest),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_add»
        [from_cv (Pair left_entry left_rest);
         from_cv (Pair right_entry right_rest)]) refs =
    (M_success
      (from_cv
        (Pair (bounded_object_q_interval_add_cv left_entry right_entry)
          completed_rest)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_interval_list_add_unfold]
  >> simp
       [bounded_case16594_object_interval_list_add_body_def,
        compute_evalTheory.subst_def,
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_if_ispair_pair_components]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_pair_fst_components]
      >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_interval_list_add»
            [from_cv left_rest;from_cv right_rest]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_pair_snd_components]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_interval_list_add_eval:
  !left right clock refs.
    EVERY bounded_packed_q_interval_encoded left /\
    EVERY bounded_packed_q_interval_encoded right /\
    LENGTH left = LENGTH right /\
    8 * (LENGTH left + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_add»
        [from_cv (bounded_object_q_cv_list left);
         from_cv (bounded_object_q_cv_list right)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (MAP2 bounded_object_q_interval_add_cv left right))),refs)
Proof
  Induct_on `left`
  >- (rpt gen_tac
      >> Cases_on `right`
      >> simp []
      >> strip_tac
      >> PURE_REWRITE_TAC
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            listTheory.MAP2]
      >> irule bounded_case16594_object_interval_list_add_nil_eval
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> Cases_on `right`
  >- simp []
  >> strip_tac
  >> gvs []
  >> PURE_REWRITE_TAC
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        listTheory.MAP2]
  >> irule bounded_case16594_object_interval_list_add_cons_eval
  >> simp []
  >> first_x_assum irule
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
