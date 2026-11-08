(*****************************************************************************
 * Exact evaluator semantics for production gradient recompletion.
 *
 * The arithmetic body is evaluated first in the authenticated 27-function
 * packed-object core.  Restricted evaluator congruence then transports that
 * result into the complete case-16594 dispatcher.  Later lemmas add the
 * fixed 21-to-6 Hessian expansion and the six-row traversal.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectGradientCompleteEval
Ancestors
  compute_boundedCase16594ObjectRuntimePreservation
  compute_boundedCase16594ObjectCoreCongruence
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_gradient_row_complete_body_def:
  bounded_case16594_object_gradient_row_complete_body =
    Let «variation»
      (App «candle_cv_q_dot_abs_upper»
        [Var «radii»;Var «interval_row»])
      (Let «error»
        (App «candle_cv_q_add» [Var «variation»;Var «variation»])
        (Let «half_error»
          (App «candle_cv_q_mul»
            [Var «error»;App «candle_cv_q_half» []])
          (App «candle_cv_q_interval_add»
            [Var «center_entry»;
             Pair (App «candle_cv_q_neg» [Var «half_error»])
               (Var «half_error»)])))
End

Theorem bounded_case16594_object_gradient_row_complete_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_gradient_row_complete» =
    SOME
      ([«radii»;«center_entry»;«interval_row»],
       bounded_case16594_object_gradient_row_complete_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_gradient_row_complete_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_row_complete»
        [from_cv radii;from_cv center_entry;from_cv interval_row])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_entry»,from_cv center_entry);
         («interval_row»,from_cv interval_row)]
        bounded_case16594_object_gradient_row_complete_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_gradient_row_complete_lookup
QED

Theorem bounded_packed_q_source_gradient_row_complete_cv_encoded:
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_encoded center_entry /\
  EVERY bounded_packed_q_interval_encoded interval_row ==>
  bounded_packed_q_interval_encoded
    (bounded_packed_q_source_gradient_row_complete_cv
      radii center_entry interval_row)
Proof
  strip_tac
  >> rw [bounded_packed_q_source_gradient_row_complete_cv_def,LET_THM]
  >> irule
       compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_interval_add_encoded
  >> simp []
  >> rw
       [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> simp
       [compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_neg_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded,
        compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_encoded,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded]
QED

Theorem bounded_case16594_object_gradient_row_complete_body_core_only:
  compute_exp_uses_only bounded_case16594_object_core
    (subst
      [(«radii»,from_cv (bounded_object_q_cv_list radii));
       («center_entry»,from_cv center_entry);
       («interval_row»,from_cv (bounded_object_q_cv_list interval_row))]
      bounded_case16594_object_gradient_row_complete_body)
Proof
  simp
    [bounded_case16594_object_gradient_row_complete_body_def,
     compute_evalTheory.subst_def,
     compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
     compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_def,
     compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_uses_only_from_cv]
  >> EVAL_TAC
QED

Theorem bounded_packed_q_gradient_variation_eval:
  EVERY bounded_object_q_encoded radii /\
  EVERY bounded_packed_q_interval_encoded interval_row /\
  12 * (LENGTH radii + 1) < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_dot_abs_upper»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv (bounded_object_q_cv_list interval_row)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_dot_abs_upper_cv radii interval_row)),refs)
Proof
  metis_tac
    [compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_q_dot_abs_upper_recursive_eval]
QED

Theorem bounded_packed_q_gradient_error_eval:
  EVERY bounded_object_q_encoded radii /\
  EVERY bounded_packed_q_interval_encoded interval_row /\
  3 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_add»
        [from_cv
           (bounded_packed_q_source_dot_abs_upper_cv radii interval_row);
         from_cv
           (bounded_packed_q_source_dot_abs_upper_cv radii interval_row)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_add_cv
          (bounded_packed_q_source_dot_abs_upper_cv radii interval_row)
          (bounded_packed_q_source_dot_abs_upper_cv radii interval_row))),refs)
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_add_eval
  >> simp
       [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_encoded]
QED

Theorem bounded_packed_q_gradient_half_error_eval:
  EVERY bounded_object_q_encoded radii /\
  EVERY bounded_packed_q_interval_encoded interval_row /\
  3 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_mul»
        [from_cv
           (bounded_object_q_add_cv
             (bounded_packed_q_source_dot_abs_upper_cv radii interval_row)
             (bounded_packed_q_source_dot_abs_upper_cv radii interval_row));
         App «candle_cv_q_half» []])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_mul_cv
          (bounded_object_q_add_cv
            (bounded_packed_q_source_dot_abs_upper_cv radii interval_row)
            (bounded_packed_q_source_dot_abs_upper_cv radii interval_row))
          (bounded_analytic_source_q_cv 1 0 1))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_mul»
            [from_cv
               (bounded_object_q_add_cv
                 (bounded_packed_q_source_dot_abs_upper_cv radii interval_row)
                 (bounded_packed_q_source_dot_abs_upper_cv radii interval_row));
             from_cv (bounded_analytic_source_q_cv 1 0 1)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_half_eval])
  >> irule
       compute_boundedPackedObjectPrimitiveMulEvalTheory.bounded_packed_q_mul_eval
  >> simp
       [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded,
        compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_encoded,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded]
QED

Theorem bounded_packed_q_gradient_symmetric_error_eval:
  bounded_object_q_encoded half_error /\ 1 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (Pair (App «candle_cv_q_neg» [from_cv half_error])
        (from_cv half_error)) (refs:hol_refs) =
    (M_success
      (from_cv (Pair (bounded_object_q_neg_cv half_error) half_error)),refs)
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results
  >> simp [compute_execProofTheory.compute_eval_from_cv]
  >> irule
       compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_neg_eval
  >> simp []
QED

Theorem bounded_packed_q_gradient_final_interval_eval:
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_encoded center_entry /\
  EVERY bounded_packed_q_interval_encoded interval_row /\
  5 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_interval_add»
        [from_cv center_entry;
         Pair
           (App «candle_cv_q_neg»
             [from_cv
               (bounded_object_q_mul_cv
                 (bounded_object_q_add_cv
                   (bounded_packed_q_source_dot_abs_upper_cv
                     radii interval_row)
                   (bounded_packed_q_source_dot_abs_upper_cv
                     radii interval_row))
                 (bounded_analytic_source_q_cv 1 0 1))])
           (from_cv
             (bounded_object_q_mul_cv
               (bounded_object_q_add_cv
                 (bounded_packed_q_source_dot_abs_upper_cv
                   radii interval_row)
                 (bounded_packed_q_source_dot_abs_upper_cv
                   radii interval_row))
               (bounded_analytic_source_q_cv 1 0 1)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_gradient_row_complete_cv
          radii center_entry interval_row)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_interval_add»
            [from_cv center_entry;
             from_cv
               (Pair
                 (bounded_object_q_neg_cv
                   (bounded_object_q_mul_cv
                     (bounded_object_q_add_cv
                       (bounded_packed_q_source_dot_abs_upper_cv
                         radii interval_row)
                       (bounded_packed_q_source_dot_abs_upper_cv
                         radii interval_row))
                     (bounded_analytic_source_q_cv 1 0 1)))
                 (bounded_object_q_mul_cv
                   (bounded_object_q_add_cv
                     (bounded_packed_q_source_dot_abs_upper_cv
                       radii interval_row)
                     (bounded_packed_q_source_dot_abs_upper_cv
                       radii interval_row))
                   (bounded_analytic_source_q_cv 1 0 1)))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_packed_q_gradient_symmetric_error_eval)
      >> simp
           [compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
            compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded,
            compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_encoded,
            compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded]
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [bounded_packed_q_source_gradient_row_complete_cv_def,LET_THM]
  >> BETA_TAC
  >> irule
       compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_interval_add_eval
  >> simp []
  >> rw
       [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> simp
       [compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_neg_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded,
        compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_encoded,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded]
QED

Theorem bounded_packed_q_gradient_row_complete_body_eval:
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_encoded center_entry /\
  EVERY bounded_packed_q_interval_encoded interval_row /\
  64 * (LENGTH radii + 1) < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (subst
        [(«radii»,from_cv (bounded_object_q_cv_list radii));
         («center_entry»,from_cv center_entry);
         («interval_row»,from_cv (bounded_object_q_cv_list interval_row))]
        bounded_case16594_object_gradient_row_complete_body)
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_gradient_row_complete_cv
          radii center_entry interval_row)),refs)
Proof
  strip_tac
  >> simp
       [bounded_case16594_object_gradient_row_complete_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_dot_abs_upper_cv radii interval_row`
  >> conj_tac
  >- (irule bounded_packed_q_gradient_variation_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_add_cv
          (bounded_packed_q_source_dot_abs_upper_cv radii interval_row)
          (bounded_packed_q_source_dot_abs_upper_cv radii interval_row)`
  >> conj_tac
  >- (irule bounded_packed_q_gradient_error_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_mul_cv
          (bounded_object_q_add_cv
            (bounded_packed_q_source_dot_abs_upper_cv radii interval_row)
            (bounded_packed_q_source_dot_abs_upper_cv radii interval_row))
          (bounded_analytic_source_q_cv 1 0 1)`
  >> conj_tac
  >- (irule bounded_packed_q_gradient_half_error_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule bounded_packed_q_gradient_final_interval_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_gradient_row_complete_eval:
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_encoded center_entry /\
  EVERY bounded_packed_q_interval_encoded interval_row /\
  64 * (LENGTH radii + 1) + 1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_row_complete»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv center_entry;
         from_cv (bounded_object_q_cv_list interval_row)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_gradient_row_complete_cv
          radii center_entry interval_row)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_gradient_row_complete_unfold]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1) bounded_packed_object_entry_ceqs
          (subst
            [(«radii»,from_cv (bounded_object_q_cv_list radii));
             («center_entry»,from_cv center_entry);
             («interval_row»,from_cv
               (bounded_object_q_cv_list interval_row))]
            bounded_case16594_object_gradient_row_complete_body) refs`
  >> conj_tac
  >- (sym_tac
      >> irule
           compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_eval_cong
      >> ACCEPT_TAC
           bounded_case16594_object_gradient_row_complete_body_core_only)
  >> irule bounded_packed_q_gradient_row_complete_body_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_delta_six_body_def:
  bounded_case16594_object_delta_six_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d»)
            (Pair (Var «e») (Pair (Var «f») (Num 0))))))
End

Theorem bounded_case16594_object_delta_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_six» =
    SOME
      ([«a»;«b»;«c»;«d»;«e»;«f»],
       bounded_case16594_object_delta_six_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_delta_six_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_six»
        [from_cv a;from_cv b;from_cv c;from_cv d;from_cv e;from_cv f])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list [a;b;c;d;e;f])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«a»,from_cv a);(«b»,from_cv b);(«c»,from_cv c);
             («d»,from_cv d);(«e»,from_cv e);(«f»,from_cv f)]
            bounded_case16594_object_delta_six_body) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
      >> asm_rewrite_tac []
      >> ACCEPT_TAC bounded_case16594_object_delta_six_lookup)
  >> simp
       [bounded_case16594_object_delta_six_body_def,
        compute_evalTheory.subst_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_interval_lookup_el_eval:
  n < LENGTH items /\ n + 2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_lookup»
        [Num n;from_cv (bounded_object_q_cv_list items)])
      (refs:hol_refs) =
    (M_success (from_cv (EL n items)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_interval_lookup»
            [Num n;from_cv (bounded_object_q_cv_list items)]) refs`
  >> conj_tac
  >- (sym_tac
      >> irule
           compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_eval_cong
      >> simp
           [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
            compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_def,
            compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_uses_only_from_cv]
      >> EVAL_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_boundedPackedObjectLookupEvalTheory.bounded_packed_q_interval_lookup_el_eval)
  >> simp []
QED

Theorem bounded_case16594_object_delta_six_lookup_eval:
  i0 < LENGTH items /\ i1 < LENGTH items /\
  i2 < LENGTH items /\ i3 < LENGTH items /\
  i4 < LENGTH items /\ i5 < LENGTH items /\
  i0 + 2 < clock /\ i1 + 2 < clock /\
  i2 + 2 < clock /\ i3 + 2 < clock /\
  i4 + 2 < clock /\ i5 + 2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_six»
        [App «candle_cv_q_interval_lookup»
           [Num i0;from_cv (bounded_object_q_cv_list items)];
         App «candle_cv_q_interval_lookup»
           [Num i1;from_cv (bounded_object_q_cv_list items)];
         App «candle_cv_q_interval_lookup»
           [Num i2;from_cv (bounded_object_q_cv_list items)];
         App «candle_cv_q_interval_lookup»
           [Num i3;from_cv (bounded_object_q_cv_list items)];
         App «candle_cv_q_interval_lookup»
           [Num i4;from_cv (bounded_object_q_cv_list items)];
         App «candle_cv_q_interval_lookup»
           [Num i5;from_cv (bounded_object_q_cv_list items)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          [EL i0 items;EL i1 items;EL i2 items;
           EL i3 items;EL i4 items;EL i5 items])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_six»
            [from_cv (EL i0 items);from_cv (EL i1 items);
             from_cv (EL i2 items);from_cv (EL i3 items);
             from_cv (EL i4 items);from_cv (EL i5 items)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
      >> simp
           [bounded_case16594_object_interval_lookup_el_eval]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_delta_six_eval
  >> intLib.ARITH_TAC
QED

Definition bounded_packed_q_source_hessian6_rows_def:
  bounded_packed_q_source_hessian6_rows packed =
    [[EL 0 packed;EL 1 packed;EL 2 packed;EL 3 packed;EL 4 packed;EL 5 packed];
     [EL 1 packed;EL 6 packed;EL 7 packed;EL 8 packed;EL 9 packed;EL 10 packed];
     [EL 2 packed;EL 7 packed;EL 11 packed;EL 12 packed;EL 13 packed;EL 14 packed];
     [EL 3 packed;EL 8 packed;EL 12 packed;EL 15 packed;EL 16 packed;EL 17 packed];
     [EL 4 packed;EL 9 packed;EL 13 packed;EL 16 packed;EL 18 packed;EL 19 packed];
     [EL 5 packed;EL 10 packed;EL 14 packed;EL 17 packed;EL 19 packed;EL 20 packed]]
End

Theorem bounded_packed_q_source_hessian6_rows_exact:
  LENGTH packed = 21 ==>
  bounded_hessian64_rows packed =
    SOME (bounded_packed_q_source_hessian6_rows packed)
Proof
  rw
    [listTheory.LENGTH_EQ_NUM_compute,
     bounded_packed_q_source_hessian6_rows_def,
     compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> EVAL_TAC
QED

Definition bounded_case16594_object_hessian_lookup_exp_def:
  bounded_case16594_object_hessian_lookup_exp index =
    App «candle_cv_q_interval_lookup» [Num index;Var «packed»]
End

Definition bounded_case16594_object_hessian_row_exp_def:
  bounded_case16594_object_hessian_row_exp i0 i1 i2 i3 i4 i5 =
    App «candle_cv_q_packed_delta_six»
      [bounded_case16594_object_hessian_lookup_exp i0;
       bounded_case16594_object_hessian_lookup_exp i1;
       bounded_case16594_object_hessian_lookup_exp i2;
       bounded_case16594_object_hessian_lookup_exp i3;
       bounded_case16594_object_hessian_lookup_exp i4;
       bounded_case16594_object_hessian_lookup_exp i5]
End

Definition bounded_case16594_object_hessian6_expand_body_def:
  bounded_case16594_object_hessian6_expand_body =
    App «candle_cv_q_packed_delta_six»
      [bounded_case16594_object_hessian_row_exp 0 1 2 3 4 5;
       bounded_case16594_object_hessian_row_exp 1 6 7 8 9 10;
       bounded_case16594_object_hessian_row_exp 2 7 11 12 13 14;
       bounded_case16594_object_hessian_row_exp 3 8 12 15 16 17;
       bounded_case16594_object_hessian_row_exp 4 9 13 16 18 19;
       bounded_case16594_object_hessian_row_exp 5 10 14 17 19 20]
End

Theorem bounded_case16594_object_hessian6_expand_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_hessian6_expand» =
    SOME ([«packed»],bounded_case16594_object_hessian6_expand_body)
Proof
  rw
    [bounded_case16594_object_hessian6_expand_body_def,
     bounded_case16594_object_hessian_row_exp_def,
     bounded_case16594_object_hessian_lookup_exp_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_hessian6_expand_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_hessian6_expand» [from_cv packed])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«packed»,from_cv packed)]
        bounded_case16594_object_hessian6_expand_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_hessian6_expand_lookup
QED

Theorem bounded_case16594_object_hessian6_expand_eval:
  LENGTH packed = 21 /\ 64 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_hessian6_expand»
        [from_cv (bounded_object_q_cv_list packed)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (MAP bounded_object_q_cv_list
            (bounded_packed_q_source_hessian6_rows packed)))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_hessian6_expand_unfold]
  >> simp
       [bounded_case16594_object_hessian6_expand_body_def,
        bounded_case16594_object_hessian_row_exp_def,
        bounded_case16594_object_hessian_lookup_exp_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_six»
            [from_cv (bounded_object_q_cv_list
               [EL 0 packed;EL 1 packed;EL 2 packed;
                EL 3 packed;EL 4 packed;EL 5 packed]);
             from_cv (bounded_object_q_cv_list
               [EL 1 packed;EL 6 packed;EL 7 packed;
                EL 8 packed;EL 9 packed;EL 10 packed]);
             from_cv (bounded_object_q_cv_list
               [EL 2 packed;EL 7 packed;EL 11 packed;
                EL 12 packed;EL 13 packed;EL 14 packed]);
             from_cv (bounded_object_q_cv_list
               [EL 3 packed;EL 8 packed;EL 12 packed;
                EL 15 packed;EL 16 packed;EL 17 packed]);
             from_cv (bounded_object_q_cv_list
               [EL 4 packed;EL 9 packed;EL 13 packed;
                EL 16 packed;EL 18 packed;EL 19 packed]);
             from_cv (bounded_object_q_cv_list
               [EL 5 packed;EL 10 packed;EL 14 packed;
                EL 17 packed;EL 19 packed;EL 20 packed])]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
      >> simp []
      >> simp [bounded_case16594_object_delta_six_lookup_eval]
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [bounded_packed_q_source_hessian6_rows_def]
  >> simp []
  >> irule bounded_case16594_object_delta_six_eval
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_gradient_rows_complete_body_def:
  bounded_case16594_object_gradient_rows_complete_body =
    If (Uop Ispair (Var «center_gradient»))
      (If (Uop Ispair (Var «interval_rows»))
        (Pair
          (App «candle_cv_q_packed_object_gradient_row_complete»
            [Var «radii»;Uop Fst (Var «center_gradient»);
             Uop Fst (Var «interval_rows»)])
          (App «candle_cv_q_packed_object_gradient_rows_complete»
            [Var «radii»;Uop Snd (Var «center_gradient»);
             Uop Snd (Var «interval_rows»)]))
        (Num 0))
      (Num 0)
End

Theorem bounded_case16594_object_gradient_rows_complete_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_gradient_rows_complete» =
    SOME
      ([«radii»;«center_gradient»;«interval_rows»],
       bounded_case16594_object_gradient_rows_complete_body)
Proof
  rw [bounded_case16594_object_gradient_rows_complete_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_gradient_rows_complete_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_rows_complete»
        [from_cv radii;from_cv center_gradient;from_cv interval_rows])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_gradient»,from_cv center_gradient);
         («interval_rows»,from_cv interval_rows)]
        bounded_case16594_object_gradient_rows_complete_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_gradient_rows_complete_lookup
QED

Theorem bounded_case16594_object_gradient_rows_complete_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_rows_complete»
        [from_cv radii;from_cv (Num 0);from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success (from_cv (Num 0)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_gradient_rows_complete_unfold]
  >> simp
       [bounded_case16594_object_gradient_rows_complete_body_def,
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

Theorem bounded_case16594_object_compute_eval_app3_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) ==>
  compute_eval clock ceqs
      (App function_name [argument1;argument2;argument3]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3]) refs
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
  >> Cases_on `LENGTH q = 3`
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

Theorem bounded_case16594_object_compute_eval_if_ispair_pair_components:
  compute_eval clock ceqs
      (If (Uop Ispair (Pair (from_cv left) (from_cv right)))
        yes_branch no_branch) (refs:hol_refs) =
    compute_eval clock ceqs yes_branch refs
Proof
  ACCEPT_TAC
    (REWRITE_RULE [compute_execTheory.from_cv_def]
      compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_if_ispair_from_cv_pair)
QED

Theorem bounded_case16594_object_compute_eval_pair_fst_components:
  compute_eval clock ceqs
      (Uop Fst (Pair (from_cv left) (from_cv right))) (refs:hol_refs) =
    (M_success (from_cv left),refs)
Proof
  ACCEPT_TAC
    (REWRITE_RULE [compute_execTheory.from_cv_def]
      compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_fst)
QED

Theorem bounded_case16594_object_compute_eval_pair_snd_components:
  compute_eval clock ceqs
      (Uop Snd (Pair (from_cv left) (from_cv right))) (refs:hol_refs) =
    (M_success (from_cv right),refs)
Proof
  ACCEPT_TAC
    (REWRITE_RULE [compute_execTheory.from_cv_def]
      compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_snd)
QED

Theorem bounded_case16594_object_gradient_rows_complete_cons_eval:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_row_complete»
        [from_cv radii;from_cv center_entry;from_cv interval_row])
      (refs:hol_refs) =
    (M_success (from_cv completed_entry),refs) /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_rows_complete»
        [from_cv radii;from_cv center_rest;from_cv row_rest]) refs =
    (M_success (from_cv completed_rest),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_rows_complete»
        [from_cv radii;
         from_cv (Pair center_entry center_rest);
         from_cv (Pair interval_row row_rest)]) refs =
    (M_success (from_cv (Pair completed_entry completed_rest)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_gradient_rows_complete_unfold]
  >> simp
       [bounded_case16594_object_gradient_rows_complete_body_def,
        compute_evalTheory.subst_def,
        bounded_case16594_object_compute_eval_if_ispair_pair_components]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_object_gradient_row_complete»
                [from_cv radii;from_cv center_entry;from_cv interval_row]) refs`
      >> conj_tac
      >- (irule bounded_case16594_object_compute_eval_app3_argument_results
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                bounded_case16594_object_compute_eval_pair_fst_components]
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_gradient_rows_complete»
            [from_cv radii;from_cv center_rest;from_cv row_rest]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app3_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            bounded_case16594_object_compute_eval_pair_snd_components]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_gradient_rows_complete_eval:
  !center_gradient interval_rows clock refs.
    EVERY bounded_object_q_encoded radii /\
    LENGTH radii = 6 /\
    EVERY bounded_packed_q_interval_encoded center_gradient /\
    EVERY (EVERY bounded_packed_q_interval_encoded) interval_rows /\
    LENGTH center_gradient = LENGTH interval_rows /\
    512 * (LENGTH center_gradient + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_gradient_rows_complete»
          [from_cv (bounded_object_q_cv_list radii);
           from_cv (bounded_object_q_cv_list center_gradient);
           from_cv
             (bounded_object_q_cv_list
               (MAP bounded_object_q_cv_list interval_rows))])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_object_q_cv_list
            (bounded_packed_q_source_gradient_rows_complete_cv
              radii center_gradient interval_rows))),refs)
Proof
  Induct_on `center_gradient`
  >- (rpt gen_tac
      >> Cases_on `interval_rows`
      >> simp []
      >> strip_tac
      >> PURE_REWRITE_TAC
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            bounded_packed_q_source_gradient_rows_complete_cv_def]
      >> irule bounded_case16594_object_gradient_rows_complete_nil_eval
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> Cases_on `interval_rows`
  >- simp []
  >> strip_tac
  >> gvs []
  >> PURE_REWRITE_TAC
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        listTheory.MAP,
        bounded_packed_q_source_gradient_rows_complete_cv_def]
  >> irule bounded_case16594_object_gradient_rows_complete_cons_eval
  >> conj_tac
  >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_gradient_row_complete_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> first_x_assum irule
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_source_hessian6_rows_encoded:
  LENGTH packed = 21 /\
  EVERY bounded_packed_q_interval_encoded packed ==>
  EVERY (EVERY bounded_packed_q_interval_encoded)
    (bounded_packed_q_source_hessian6_rows packed)
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> gvs
       [bounded_packed_q_source_hessian6_rows_def,
        listTheory.EVERY_DEF]
QED

Definition bounded_case16594_object_gradient_complete6_body_def:
  bounded_case16594_object_gradient_complete6_body =
    App «candle_cv_q_packed_object_gradient_rows_complete»
      [Var «radii»;Var «center_gradient»;
       App «candle_cv_q_packed_hessian6_expand»
         [Var «packed_hessian»]]
End

Theorem bounded_case16594_object_gradient_complete6_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_gradient_complete6» =
    SOME
      ([«radii»;«center_gradient»;«packed_hessian»],
       bounded_case16594_object_gradient_complete6_body)
Proof
  rw [bounded_case16594_object_gradient_complete6_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_gradient_complete6_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_complete6»
        [from_cv radii;from_cv center_gradient;from_cv packed_hessian])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_gradient»,from_cv center_gradient);
         («packed_hessian»,from_cv packed_hessian)]
        bounded_case16594_object_gradient_complete6_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_gradient_complete6_lookup
QED

Theorem bounded_case16594_object_gradient_complete6_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  4096 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_complete6»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv (bounded_object_q_cv_list center_gradient);
         from_cv (bounded_object_q_cv_list packed_hessian)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_packed_q_source_gradient_complete6_cv
            radii center_gradient packed_hessian))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_gradient_complete6_unfold]
  >> simp
       [bounded_case16594_object_gradient_complete6_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_gradient_rows_complete»
            [from_cv (bounded_object_q_cv_list radii);
             from_cv (bounded_object_q_cv_list center_gradient);
             from_cv
               (bounded_object_q_cv_list
                 (MAP bounded_object_q_cv_list
                   (bounded_packed_q_source_hessian6_rows
                     packed_hessian)))]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app3_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule bounded_case16594_object_hessian6_expand_eval
      >> intLib.ARITH_TAC)
  >> simp
       [bounded_packed_q_source_gradient_complete6_cv_def,
        bounded_packed_q_source_hessian6_rows_exact]
  >> irule bounded_case16594_object_gradient_rows_complete_eval
  >> simp
       [bounded_packed_q_source_hessian6_rows_def,
        bounded_packed_q_source_hessian6_rows_encoded]
QED

val _ = export_theory ();
