(*****************************************************************************
 * Exact source-faithful packed-object value-bound evaluation.
 *****************************************************************************)
Theory compute_boundedPackedObjectValueEval
Ancestors
  compute_boundedPackedObjectErrorEval
Libs
  bossLib preamble intLib

Definition bounded_packed_q_half_body_def:
  bounded_packed_q_half_body : compute_exp =
    Pair (Pair (Num 1) (Num 0)) (Num 1)
End

Definition bounded_packed_q_interval_add_body_def:
  bounded_packed_q_interval_add_body =
    Pair
      (App «candle_cv_q_add»
        [Uop Fst (Var «x»);Uop Fst (Var «y»)])
      (App «candle_cv_q_add»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Definition bounded_packed_q_value_bound6_body_def:
  bounded_packed_q_value_bound6_body =
    Let «half_error»
      (App «candle_cv_q_mul»
        [App «candle_cv_q_half» [];
         App «candle_cv_q_packed_object_error6»
           [Var «radii»;Var «center_gradient»;Var «packed»]])
      (App «candle_cv_q_interval_add»
        [Var «center_value»;
         Pair (App «candle_cv_q_neg» [Var «half_error»])
           (Var «half_error»)])
End

Definition bounded_packed_q_source_interval_add_cv_def:
  bounded_packed_q_source_interval_add_cv
      (Pair left_lower left_upper) (Pair right_lower right_upper) =
    Pair
      (bounded_object_q_add_cv left_lower right_lower)
      (bounded_object_q_add_cv left_upper right_upper) /\
  bounded_packed_q_source_interval_add_cv _ _ = Num 0
End

Definition bounded_packed_q_source_half_error_cv_def:
  bounded_packed_q_source_half_error_cv radii center_gradient packed =
    bounded_object_q_mul_cv
      (bounded_analytic_source_q_cv 1 0 1)
      (bounded_packed_q_source_error6_cv radii center_gradient packed)
End

Definition bounded_packed_q_source_value_bound6_cv_def:
  bounded_packed_q_source_value_bound6_cv
      radii center_value center_gradient packed =
    let half_error =
      bounded_packed_q_source_half_error_cv
        radii center_gradient packed in
      bounded_packed_q_source_interval_add_cv center_value
        (Pair (bounded_object_q_neg_cv half_error) half_error)
End

Theorem bounded_packed_q_half_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_q_half» =
    SOME ([],bounded_packed_q_half_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_interval_add_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_q_interval_add» =
    SOME ([«x»;«y»],bounded_packed_q_interval_add_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_value_bound6_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs
      «candle_cv_q_packed_object_value_bound6» =
    SOME
      ([«radii»;«center_value»;«center_gradient»;«packed»],
       bounded_packed_q_value_bound6_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_half_eval:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_half» []) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_analytic_source_q_cv 1 0 1)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_q_half_lookup,
        bounded_packed_q_half_body_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_compute_eval_pair_from_results:
  compute_eval clock ceqs left (refs:hol_refs) =
      (M_success (from_cv left_result),refs) /\
  compute_eval clock ceqs right refs =
      (M_success (from_cv right_result),refs) ==>
  compute_eval clock ceqs (Pair left right) refs =
    (M_success (from_cv (Pair left_result right_result)),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_compute_eval_fst_literal_pair:
  compute_eval clock ceqs
      (Uop Fst (Pair (from_cv left) (from_cv right)))
      (refs:hol_refs) =
    (M_success (from_cv left),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_fst_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_compute_eval_snd_literal_pair:
  compute_eval clock ceqs
      (Uop Snd (Pair (from_cv left) (from_cv right)))
      (refs:hol_refs) =
    (M_success (from_cv right),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_add_argument_results_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  compute_eval clock bounded_packed_object_entry_ceqs left_expression
      (refs:hol_refs) = (M_success (from_cv left),refs) /\
  compute_eval clock bounded_packed_object_entry_ceqs right_expression refs =
      (M_success (from_cv right),refs) /\
  3 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_add» [left_expression;right_expression]) refs =
    (M_success
      (from_cv (bounded_object_q_add_cv left right)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_add» [from_cv left;from_cv right]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [])
  >> irule
       compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_add_eval
  >> simp []
QED

Theorem bounded_packed_q_interval_add_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_interval_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst [(«x»,from_cv left);(«y»,from_cv right)]
        bounded_packed_q_interval_add_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectDotEvalTheory.bounded_packed_compute_eval_literal_app2
  >> simp [bounded_packed_q_interval_add_lookup]
QED

Theorem bounded_packed_q_interval_add_eval:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right /\
  5 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_interval_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_packed_q_source_interval_add_cv left right)),refs)
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> rw [bounded_packed_q_interval_add_unfold]
  >> simp
       [bounded_packed_q_interval_add_body_def,
        bounded_packed_q_source_interval_add_cv_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_compute_eval_pair_from_results)
  >> conj_tac
  >- (irule bounded_packed_q_add_argument_results_eval
      >> simp
           [bounded_packed_compute_eval_fst_literal_pair]
      >> intLib.ARITH_TAC)
  >> irule bounded_packed_q_add_argument_results_eval
  >> simp
       [bounded_packed_compute_eval_snd_literal_pair]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_source_interval_add_encoded:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right ==>
  bounded_packed_q_interval_encoded
    (bounded_packed_q_source_interval_add_cv left right)
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> simp
       [bounded_packed_q_source_interval_add_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded]
QED

Theorem bounded_packed_q_source_half_error_encoded:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 ==>
  bounded_object_q_encoded
    (bounded_packed_q_source_half_error_cv
      radii center_gradient packed)
Proof
  strip_tac
  >> simp
       [bounded_packed_q_source_half_error_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded,
        compute_boundedPackedObjectErrorEvalTheory.bounded_packed_q_source_error6_encoded]
QED

Theorem bounded_packed_q_source_value_bound6_encoded:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 ==>
  bounded_packed_q_interval_encoded
    (bounded_packed_q_source_value_bound6_cv
      radii center_value center_gradient packed)
Proof
  strip_tac
  >> rw [bounded_packed_q_source_value_bound6_cv_def]
  >> irule bounded_packed_q_source_interval_add_encoded
  >> simp []
  >> rw
       [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> simp
       [compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_neg_encoded,
        bounded_packed_q_source_half_error_encoded]
QED

Theorem bounded_packed_q_half_error_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  98 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_mul»
        [App «candle_cv_q_half» [];
         App «candle_cv_q_packed_object_error6»
          [from_cv (bounded_object_q_cv_list radii);
           from_cv (bounded_object_q_cv_list center_gradient);
           from_cv (bounded_object_q_cv_list packed)]]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_half_error_cv
          radii center_gradient packed)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_mul»
            [from_cv (bounded_analytic_source_q_cv 1 0 1);
             from_cv
               (bounded_packed_q_source_error6_cv
                 radii center_gradient packed)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule bounded_packed_q_half_eval
          >> intLib.ARITH_TAC)
      >> irule
           compute_boundedPackedObjectErrorEvalTheory.bounded_packed_q_error6_eval
      >> simp [])
  >> rw [bounded_packed_q_source_half_error_cv_def]
  >> irule
       compute_boundedPackedObjectPrimitiveMulEvalTheory.bounded_packed_q_mul_eval
  >> simp
       [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded,
        compute_boundedPackedObjectErrorEvalTheory.bounded_packed_q_source_error6_encoded]
QED

Theorem bounded_packed_q_symmetric_half_interval_eval:
  bounded_object_q_encoded half_error /\ 2 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (Pair (App «candle_cv_q_neg» [from_cv half_error])
        (from_cv half_error)) (refs:hol_refs) =
    (M_success
      (from_cv (Pair (bounded_object_q_neg_cv half_error) half_error)),refs)
Proof
  strip_tac
  >> irule bounded_packed_compute_eval_pair_from_results
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_neg_eval
      >> simp [])
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_q_value_bound6_body_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  112 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (subst
        [(«radii»,from_cv (bounded_object_q_cv_list radii));
         («center_value»,from_cv center_value);
         («center_gradient»,from_cv
            (bounded_object_q_cv_list center_gradient));
         («packed»,from_cv (bounded_object_q_cv_list packed))]
        bounded_packed_q_value_bound6_body) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_value_bound6_cv
          radii center_value center_gradient packed)),refs)
Proof
  strip_tac
  >> simp
       [bounded_packed_q_value_bound6_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_half_error_cv
          radii center_gradient packed`
  >> conj_tac
  >- (irule bounded_packed_q_half_error_eval
      >> simp [])
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_q_source_value_bound6_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1) bounded_packed_object_entry_ceqs
          (App «candle_cv_q_interval_add»
            [from_cv center_value;
             from_cv
               (Pair
                 (bounded_object_q_neg_cv
                   (bounded_packed_q_source_half_error_cv
                     radii center_gradient packed))
                 (bounded_packed_q_source_half_error_cv
                   radii center_gradient packed))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> conj_tac
      >- simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule bounded_packed_q_symmetric_half_interval_eval
      >> simp [bounded_packed_q_source_half_error_encoded]
      >> intLib.ARITH_TAC)
  >> irule bounded_packed_q_interval_add_eval
  >> simp []
  >> rw
       [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> simp
       [compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_neg_encoded,
        bounded_packed_q_source_half_error_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_value_bound6_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_object_value_bound6»
        [from_cv radii;from_cv center_value;
         from_cv center_gradient;from_cv packed]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst
        [(«radii»,from_cv radii);(«center_value»,from_cv center_value);
         («center_gradient»,from_cv center_gradient);
         («packed»,from_cv packed)]
        bounded_packed_q_value_bound6_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_literal_app4
  >> simp [bounded_packed_q_value_bound6_lookup]
QED

Theorem bounded_packed_q_value_bound6_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_value /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  113 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_object_value_bound6»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv center_value;
         from_cv (bounded_object_q_cv_list center_gradient);
         from_cv (bounded_object_q_cv_list packed)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_value_bound6_cv
          radii center_value center_gradient packed)),refs)
Proof
  strip_tac
  >> rw [bounded_packed_q_value_bound6_unfold]
  >> irule bounded_packed_q_value_bound6_body_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
