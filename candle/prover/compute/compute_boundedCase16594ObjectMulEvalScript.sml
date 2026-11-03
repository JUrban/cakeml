(*****************************************************************************
 * Exact evaluator semantics for the production object multiplication core.
 *
 * This first layer reuses the already authenticated exact interval
 * arithmetic and proves the recursive fused six-gradient calculation.  The
 * fixed 21-entry Hessian calculation and state composition are added above
 * these reusable lemmas.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectMulEval
Ancestors
  compute_boundedCase16594ObjectInverseCoreCongruence
  compute_boundedCase16594ObjectGradientCompleteEval
  compute_boundedCase16594ObjectMulRelation
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_products_sum2_body_def:
  bounded_case16594_object_products_sum2_body =
    App «candle_cv_q_interval_add»
      [App «candle_cv_q_interval_add»
        [App «candle_cv_q_zero_interval» [];
         App «candle_cv_q_interval_mul»
           [Var «first_left»;Var «first_right»]];
       App «candle_cv_q_interval_mul»
         [Var «second_left»;Var «second_right»]]
End

Definition bounded_case16594_object_fused_scale_add_body_def:
  bounded_case16594_object_fused_scale_add_body =
    If (Uop Ispair (Var «left»))
      (If (Uop Ispair (Var «right»))
        (Pair
          (App «candle_cv_q_packed_object_products_sum2»
            [Var «left_scale»;Uop Fst (Var «left»);
             Var «right_scale»;Uop Fst (Var «right»)])
          (App «candle_cv_q_packed_object_fused_scale_add»
            [Var «left_scale»;Uop Snd (Var «left»);
             Var «right_scale»;Uop Snd (Var «right»)]))
        (Num 0))
      (Num 0)
End

Theorem bounded_case16594_packed_interval_object_encoded:
  bounded_packed_q_interval_encoded value ==>
  bounded_object_q_interval_encoded value
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def,
     compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> qexists_tac `(fraction,fraction')`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
QED

Theorem bounded_case16594_object_interval_packed_encoded:
  bounded_object_q_interval_encoded value ==>
  bounded_packed_q_interval_encoded value
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> simp
       [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
QED

Theorem bounded_case16594_object_zero_interval_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_zero_interval» []) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_analytic_source_q_interval_cv 0 0 0)),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app0
  >> asm_rewrite_tac []
  >> simp
       [compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
        compute_execTheory.from_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_interval_add_eval:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right /\
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_add_cv left right)),refs)
Proof
  strip_tac
  >> `compute_exp_uses_only bounded_case16594_object_core
        (App «candle_cv_q_interval_add» [from_cv left;from_cv right])` by
       (simp
          [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
           compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_def,
           compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_uses_only_from_cv]
        >> EVAL_TAC)
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_interval_add» [from_cv left;from_cv right])
        (refs:hol_refs) =
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_add» [from_cv left;from_cv right]) refs` by
       metis_tac
         [compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_eval_cong]
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_interval_add» [from_cv left;from_cv right])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_packed_q_source_interval_add_cv left right)),refs)` by
       metis_tac
         [compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_interval_add_eval]
  >> `bounded_packed_q_source_interval_add_cv left right =
      bounded_object_q_interval_add_cv left right` by
       (Cases_on `left`
        >> Cases_on `right`
        >> simp
             [compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_interval_add_cv_def,
              compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_def])
  >> metis_tac []
QED

Theorem bounded_case16594_object_interval_add_argument_results:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      left_expression (refs:hol_refs) = (M_success (from_cv left),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      right_expression refs = (M_success (from_cv right),refs) /\
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_add»
        [left_expression;right_expression]) refs =
    (M_success
      (from_cv (bounded_object_q_interval_add_cv left right)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_add»
            [from_cv left;from_cv right]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [])
  >> irule bounded_case16594_object_interval_add_eval
  >> simp []
QED

Theorem bounded_case16594_object_interval_mul_argument_results:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      left_expression (refs:hol_refs) = (M_success (from_cv left),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      right_expression refs = (M_success (from_cv right),refs) /\
  8 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_mul»
        [left_expression;right_expression]) refs =
    (M_success
      (from_cv (bounded_object_q_interval_mul_cv left right)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_mul»
            [from_cv left;from_cv right]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [])
  >> irule bounded_case16594_object_q_interval_mul_eval
  >> simp []
QED

Theorem bounded_case16594_object_products_sum2_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_products_sum2» =
    SOME
      ([«first_left»;«first_right»;«second_left»;«second_right»],
       bounded_case16594_object_products_sum2_body)
Proof
  rw [bounded_case16594_object_products_sum2_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_products_sum2_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_products_sum2»
        [from_cv first_left;from_cv first_right;
         from_cv second_left;from_cv second_right]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«first_left»,from_cv first_left);
         («first_right»,from_cv first_right);
         («second_left»,from_cv second_left);
         («second_right»,from_cv second_right)]
        bounded_case16594_object_products_sum2_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectInverseControlEvalTheory.bounded_case16594_object_compute_eval_literal_app4
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_products_sum2_lookup
QED

Theorem bounded_case16594_object_products_sum2_eval:
  bounded_packed_q_interval_encoded first_left /\
  bounded_packed_q_interval_encoded first_right /\
  bounded_packed_q_interval_encoded second_left /\
  bounded_packed_q_interval_encoded second_right /\
  16 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_products_sum2»
        [from_cv first_left;from_cv first_right;
         from_cv second_left;from_cv second_right]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_interval_products_sum_acc_cv
          [(first_left,first_right);(second_left,second_right)]
          (bounded_analytic_source_q_interval_cv 0 0 0))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_products_sum2_unfold]
  >> simp
       [bounded_case16594_object_products_sum2_body_def,
        compute_evalTheory.subst_def]
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_products_sum_acc_cv_def]
  >> simp []
  >> irule bounded_case16594_object_interval_add_argument_results
  >> simp
       [bounded_case16594_packed_interval_object_encoded,
        bounded_case16594_object_interval_packed_encoded,
        compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded,
        compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded]
  >> conj_tac
  >- (irule bounded_case16594_object_interval_add_argument_results
      >> simp
           [bounded_case16594_packed_interval_object_encoded,
            bounded_case16594_object_interval_packed_encoded,
            compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded,
            bounded_case16594_object_zero_interval_eval,
            bounded_case16594_object_q_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_q_interval_mul_eval
      >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_fused_scale_add_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_fused_scale_add» =
    SOME
      ([«left_scale»;«left»;«right_scale»;«right»],
       bounded_case16594_object_fused_scale_add_body)
Proof
  rw [bounded_case16594_object_fused_scale_add_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_fused_scale_add_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_fused_scale_add»
        [from_cv left_scale;from_cv left;
         from_cv right_scale;from_cv right]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«left_scale»,from_cv left_scale);(«left»,from_cv left);
         («right_scale»,from_cv right_scale);(«right»,from_cv right)]
        bounded_case16594_object_fused_scale_add_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectInverseControlEvalTheory.bounded_case16594_object_compute_eval_literal_app4
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_fused_scale_add_lookup
QED

Theorem bounded_case16594_object_fused_scale_add_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_fused_scale_add»
        [from_cv left_scale;from_cv (Num 0);
         from_cv right_scale;from_cv (Num 0)]) (refs:hol_refs) =
    (M_success (from_cv (Num 0)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_fused_scale_add_unfold]
  >> simp
       [bounded_case16594_object_fused_scale_add_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_fused_scale_add_cons_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_products_sum2»
        [from_cv left_scale;from_cv left_entry;
         from_cv right_scale;from_cv right_entry]) (refs:hol_refs) =
    (M_success (from_cv completed_entry),refs) /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_fused_scale_add»
        [from_cv left_scale;from_cv left_rest;
         from_cv right_scale;from_cv right_rest]) refs =
    (M_success (from_cv completed_rest),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_fused_scale_add»
        [from_cv left_scale;from_cv (Pair left_entry left_rest);
         from_cv right_scale;from_cv (Pair right_entry right_rest)]) refs =
    (M_success (from_cv (Pair completed_entry completed_rest)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_fused_scale_add_unfold]
  >> simp
       [bounded_case16594_object_fused_scale_add_body_def,
        compute_evalTheory.subst_def,
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_if_ispair_pair_components]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_object_products_sum2»
                [from_cv left_scale;from_cv left_entry;
                 from_cv right_scale;from_cv right_entry]) refs`
      >> conj_tac
      >- (irule
            compute_boundedPackedObjectQuadraticTermAtEvalTheory.bounded_packed_compute_eval_app4_argument_results
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_pair_fst_components]
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_fused_scale_add»
            [from_cv left_scale;from_cv left_rest;
             from_cv right_scale;from_cv right_rest]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectQuadraticTermAtEvalTheory.bounded_packed_compute_eval_app4_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_pair_snd_components]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_fused_scale_add_eval:
  !left right clock refs.
    bounded_packed_q_interval_encoded left_scale /\
    EVERY bounded_packed_q_interval_encoded left /\
    bounded_packed_q_interval_encoded right_scale /\
    EVERY bounded_packed_q_interval_encoded right /\
    LENGTH left = LENGTH right /\
    64 * (LENGTH left + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_fused_scale_add»
          [from_cv left_scale;
           from_cv (bounded_object_q_cv_list left);
           from_cv right_scale;
           from_cv (bounded_object_q_cv_list right)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_object_q_cv_list
            (bounded_object_q_interval_fused_scale_add_cv
              left_scale left right_scale right))),refs)
Proof
  Induct_on `left`
  >- (rpt gen_tac
      >> Cases_on `right`
      >> simp []
      >> strip_tac
      >> PURE_REWRITE_TAC
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_scale_add_cv_def]
      >> irule bounded_case16594_object_fused_scale_add_nil_eval
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> Cases_on `right`
  >- simp []
  >> strip_tac
  >> gvs []
  >> PURE_REWRITE_TAC
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_scale_add_cv_def]
  >> irule bounded_case16594_object_fused_scale_add_cons_eval
  >> conj_tac
  >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_products_sum2_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> first_x_assum irule
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
