(*****************************************************************************
 * Exact evaluator semantics for the shared object unary arithmetic.
 *
 * The production list-scale and self-outer routines are proved once here,
 * then composed with the existing list-add and list-append evaluators into
 * the six-coordinate unary Hessian operation used by sqrt, inverse, and atan.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectUnaryCoreEval
Ancestors
  compute_boundedCase16594ObjectAddEval
  compute_boundedCase16594ObjectMulHessianCompleteEval
  compute_boundedCase16594ObjectUnaryControlEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_interval_list_scale_body_def:
  bounded_case16594_object_interval_list_scale_body =
    If (Uop Ispair (Var «values»))
      (Pair
        (App «candle_cv_q_interval_mul»
          [Var «scalar»;Uop Fst (Var «values»)])
        (App «candle_cv_q_packed_object_interval_list_scale»
          [Var «scalar»;Uop Snd (Var «values»)]))
      (compute_syntax$Num 0)
End

Theorem bounded_case16594_object_interval_list_scale_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_interval_list_scale» =
    SOME
      ([«scalar»;«values»],
       bounded_case16594_object_interval_list_scale_body)
Proof
  rw [bounded_case16594_object_interval_list_scale_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_interval_list_scale_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_scale»
        [from_cv scalar;from_cv values]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«scalar»,from_cv scalar);(«values»,from_cv values)]
        bounded_case16594_object_interval_list_scale_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_interval_list_scale_lookup
QED

Theorem bounded_case16594_object_interval_list_scale_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_scale»
        [from_cv scalar;from_cv (compute_exec$Num 0)])
      (refs:hol_refs) =
    (M_success (from_cv (compute_exec$Num 0)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_interval_list_scale_unfold]
  >> simp
       [bounded_case16594_object_interval_list_scale_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_interval_list_scale_cons_eval:
  bounded_packed_q_interval_encoded scalar /\
  bounded_packed_q_interval_encoded entry /\
  9 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_scale»
        [from_cv scalar;from_cv rest]) (refs:hol_refs) =
    (M_success (from_cv completed_rest),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_scale»
        [from_cv scalar;from_cv (Pair entry rest)]) refs =
    (M_success
      (from_cv
        (Pair (bounded_object_q_interval_mul_cv scalar entry)
          completed_rest)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_interval_list_scale_unfold]
  >> simp
       [bounded_case16594_object_interval_list_scale_body_def,
        compute_evalTheory.subst_def,
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_if_ispair_pair_components]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_mul_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_pair_fst_components]
      >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_interval_list_scale»
            [from_cv scalar;from_cv rest]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_pair_snd_components]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_interval_list_scale_eval:
  !values clock refs.
    bounded_packed_q_interval_encoded scalar /\
    EVERY bounded_packed_q_interval_encoded values /\
    10 * (LENGTH values + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_scale»
        [from_cv scalar;from_cv (bounded_object_q_cv_list values)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (MAP (bounded_object_q_interval_mul_cv scalar) values))),refs)
Proof
  Induct_on `values`
  >- (rpt strip_tac
      >> PURE_REWRITE_TAC
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            listTheory.MAP]
      >> irule bounded_case16594_object_interval_list_scale_nil_eval
      >> intLib.ARITH_TAC)
  >> rpt strip_tac
  >> gvs []
  >> PURE_REWRITE_TAC
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        listTheory.MAP]
  >> irule bounded_case16594_object_interval_list_scale_cons_eval
  >> simp []
  >> first_x_assum irule
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_interval_self_outer_body_def:
  bounded_case16594_object_interval_self_outer_body =
    If (Uop Ispair (Var «values»))
      (App «candle_cv_q_packed_object_interval_list_append»
        [App «candle_cv_q_packed_object_interval_list_scale»
          [Uop Fst (Var «values»);Var «values»];
         App «candle_cv_q_packed_object_interval_self_outer»
          [Uop Snd (Var «values»)]])
      (compute_syntax$Num 0)
End

Theorem bounded_case16594_object_interval_self_outer_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_interval_self_outer» =
    SOME ([«values»],bounded_case16594_object_interval_self_outer_body)
Proof
  rw [bounded_case16594_object_interval_self_outer_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_interval_self_outer_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_self_outer»
        [from_cv values]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«values»,from_cv values)]
        bounded_case16594_object_interval_self_outer_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_interval_self_outer_lookup
QED

Theorem bounded_case16594_object_interval_self_outer_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_self_outer»
        [from_cv (compute_exec$Num 0)]) (refs:hol_refs) =
    (M_success (from_cv (compute_exec$Num 0)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_interval_self_outer_unfold]
  >> simp
       [bounded_case16594_object_interval_self_outer_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_cv_list_cons_eval:
  0 < clock ==>
  compute_eval clock ceqs
      (Pair (from_cv entry) (from_cv (bounded_object_q_cv_list rest)))
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_cv_list (entry::rest))),refs)
Proof
  strip_tac
  >> rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_execTheory.from_cv_def]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_case16594_object_interval_self_outer_cons_eval:
  bounded_packed_q_interval_encoded entry /\
  EVERY bounded_packed_q_interval_encoded rest /\
  20 * (LENGTH rest + 2) < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_self_outer»
        [from_cv (bounded_object_q_cv_list rest)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_interval_self_outer_cv rest))),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_self_outer»
        [from_cv (bounded_object_q_cv_list (entry::rest))]) refs =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_interval_self_outer_cv (entry::rest)))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_interval_self_outer_unfold]
  >> simp
       [bounded_case16594_object_interval_self_outer_body_def,
        compute_evalTheory.subst_def,
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_if_ispair_pair_components,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> rewrite_tac
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_self_outer_cv_def]
  >> irule
       compute_boundedCase16594ObjectMulHessianCompleteEvalTheory.bounded_case16594_object_interval_list_append_argument_results
  >> conj_tac
  >- (simp
        [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_object_interval_list_scale»
                [from_cv entry;
                 from_cv (bounded_object_q_cv_list (entry::rest))]) refs`
      >> conj_tac
      >- (irule
            compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_pair_fst_components,
                bounded_case16594_object_cv_list_cons_eval]
          >> intLib.ARITH_TAC)
      >> rewrite_tac
           [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
      >> irule bounded_case16594_object_interval_list_scale_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_interval_self_outer»
            [from_cv (bounded_object_q_cv_list rest)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_pair_snd_components])
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_interval_self_outer_eval:
  !values clock refs.
    EVERY bounded_packed_q_interval_encoded values /\
    20 * (LENGTH values + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_self_outer»
        [from_cv (bounded_object_q_cv_list values)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_interval_self_outer_cv values))),refs)
Proof
  Induct_on `values`
  >- (rpt strip_tac
      >> rewrite_tac
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_self_outer_cv_def]
      >> irule bounded_case16594_object_interval_self_outer_nil_eval
      >> intLib.ARITH_TAC)
  >> rpt strip_tac
  >> gvs []
  >> irule bounded_case16594_object_interval_self_outer_cons_eval
  >> simp []
QED

Definition bounded_case16594_object_unary_hessian6_body_def:
  bounded_case16594_object_unary_hessian6_body =
    App «candle_cv_q_packed_object_interval_list_add»
      [App «candle_cv_q_packed_object_interval_list_scale»
        [Var «second_interval»;
         App «candle_cv_q_packed_object_interval_self_outer»
           [Var «gradient»]];
       App «candle_cv_q_packed_object_interval_list_scale»
        [Var «first_interval»;Var «packed_hessian»]]
End

Theorem bounded_case16594_object_unary_hessian6_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_unary_hessian6» =
    SOME
      ([«first_interval»;«second_interval»;«gradient»;
        «packed_hessian»],
       bounded_case16594_object_unary_hessian6_body)
Proof
  rw [bounded_case16594_object_unary_hessian6_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_unary_hessian6_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_unary_hessian6»
        [from_cv first_interval;from_cv second_interval;
         from_cv gradient;from_cv packed_hessian]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«first_interval»,from_cv first_interval);
         («second_interval»,from_cv second_interval);
         («gradient»,from_cv gradient);
         («packed_hessian»,from_cv packed_hessian)]
        bounded_case16594_object_unary_hessian6_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectInverseControlEvalTheory.bounded_case16594_object_compute_eval_literal_app4
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_unary_hessian6_lookup
QED

Theorem bounded_case16594_object_self_outer_length6:
  LENGTH values = 6 ==>
  LENGTH (bounded_object_q_interval_self_outer_cv values) = 21
Proof
  Cases_on `values` >> simp []
  >> Cases_on `t` >> simp []
  >> Cases_on `t'` >> simp []
  >> Cases_on `t` >> simp []
  >> Cases_on `t'` >> simp []
  >> Cases_on `t` >> simp []
  >> Cases_on `t'`
  >> simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_self_outer_cv_def,
        compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
QED

Theorem bounded_case16594_object_interval_list_scale_length:
  LENGTH (bounded_object_q_interval_list_scale_cv scalar values) =
  LENGTH values
Proof
  simp
    [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
QED

Theorem bounded_case16594_object_interval_list_scale_packed_encoded:
  !values.
    bounded_packed_q_interval_encoded scalar /\
    EVERY bounded_packed_q_interval_encoded values ==>
    EVERY bounded_packed_q_interval_encoded
      (bounded_object_q_interval_list_scale_cv scalar values)
Proof
  Induct
  >- simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
  >> strip_tac
  >> gvs
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
  >> strip_tac
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded]
QED

Theorem bounded_case16594_object_interval_self_outer_packed_encoded:
  !values.
    EVERY bounded_packed_q_interval_encoded values ==>
    EVERY bounded_packed_q_interval_encoded
      (bounded_object_q_interval_self_outer_cv values)
Proof
  Induct
  >- simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_self_outer_cv_def]
  >> strip_tac
  >> gvs
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_self_outer_cv_def,
        listTheory.EVERY_APPEND]
  >> strip_tac
  >> irule bounded_case16594_object_interval_list_scale_packed_encoded
  >> simp []
QED

Theorem bounded_case16594_object_interval_list_scale_self_outer_eval:
  bounded_packed_q_interval_encoded scalar /\
  EVERY bounded_packed_q_interval_encoded gradient /\
  LENGTH gradient = 6 /\
  512 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_scale»
        [from_cv scalar;
         App «candle_cv_q_packed_object_interval_self_outer»
           [from_cv (bounded_object_q_cv_list gradient)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_interval_list_scale_cv scalar
            (bounded_object_q_interval_self_outer_cv gradient)))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_interval_list_scale»
            [from_cv scalar;
             from_cv
               (bounded_object_q_cv_list
                 (bounded_object_q_interval_self_outer_cv gradient))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule bounded_case16594_object_interval_self_outer_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> rewrite_tac
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
  >> irule bounded_case16594_object_interval_list_scale_eval
  >> simp
       [bounded_case16594_object_interval_self_outer_packed_encoded,
        bounded_case16594_object_self_outer_length6]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_unary_hessian6_eval:
  bounded_packed_q_interval_encoded first_interval /\
  bounded_packed_q_interval_encoded second_interval /\
  EVERY bounded_packed_q_interval_encoded gradient /\
  LENGTH gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  1024 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_unary_hessian6»
        [from_cv first_interval;from_cv second_interval;
         from_cv (bounded_object_q_cv_list gradient);
         from_cv (bounded_object_q_cv_list packed_hessian)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_taylor_unary_hessian_cv
            first_interval second_interval gradient packed_hessian))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_unary_hessian6_unfold]
  >> simp
       [bounded_case16594_object_unary_hessian6_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_interval_list_add»
            [from_cv
              (bounded_object_q_cv_list
                (bounded_object_q_interval_list_scale_cv second_interval
                  (bounded_object_q_interval_self_outer_cv gradient)));
             from_cv
              (bounded_object_q_cv_list
                (bounded_object_q_interval_list_scale_cv first_interval
                  packed_hessian))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule bounded_case16594_object_interval_list_scale_self_outer_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> rewrite_tac
           [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
      >> irule bounded_case16594_object_interval_list_scale_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> rewrite_tac
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_taylor_unary_hessian_cv_def]
  >> irule
       compute_boundedCase16594ObjectAddEvalTheory.bounded_case16594_object_interval_list_add_eval
  >> simp
       [bounded_case16594_object_interval_self_outer_packed_encoded,
        bounded_case16594_object_interval_list_scale_packed_encoded,
        bounded_case16594_object_interval_list_scale_length,
        bounded_case16594_object_self_outer_length6]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
