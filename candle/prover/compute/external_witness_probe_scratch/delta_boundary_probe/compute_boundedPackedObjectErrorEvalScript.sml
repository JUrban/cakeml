(*****************************************************************************
 * Exact source-faithful packed-object error evaluation.
 *****************************************************************************)
Theory compute_boundedPackedObjectErrorEval
Ancestors
  compute_boundedPackedObjectQuadraticBodyEval
Libs
  bossLib preamble intLib

Definition bounded_packed_q_error6_body_def:
  bounded_packed_q_error6_body =
    Let «linear»
      (App «candle_cv_q_dot_abs_upper»
        [Var «radii»;Var «center_gradient»])
      (Let «quadratic»
        (App «candle_cv_q_packed_quadratic_abs_upper6»
          [Var «radii»;Var «packed»])
        (App «candle_cv_q_add»
          [App «candle_cv_q_add» [Var «linear»;Var «linear»];
           Var «quadratic»]))
End

Definition bounded_packed_q_source_error6_cv_def:
  bounded_packed_q_source_error6_cv radii center_gradient packed =
    let linear =
      bounded_packed_q_source_dot_abs_upper_cv radii center_gradient in
    let quadratic =
      bounded_packed_q_source_quadratic_suffix6_cv
        0 (HD radii) (EL 1 radii) (EL 2 radii)
        (EL 3 radii) (EL 4 radii) (EL 5 radii) packed in
      bounded_object_q_add_cv
        (bounded_object_q_add_cv linear linear) quadratic
End

Theorem bounded_packed_q_error6_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs
      «candle_cv_q_packed_object_error6» =
    SOME
      ([«radii»;«center_gradient»;«packed»],
       bounded_packed_q_error6_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_compute_eval_literal_app3:
  0 < clock /\
  ALOOKUP ceqs function_name =
      SOME ([name1;name2;name3],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv value1;from_cv value2;from_cv value3])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv value1);(name2,from_cv value2);
         (name3,from_cv value3)] body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_error6_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_object_error6»
        [from_cv radii;from_cv center_gradient;from_cv packed])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_gradient»,from_cv center_gradient);
         («packed»,from_cv packed)]
        bounded_packed_q_error6_body) refs
Proof
  strip_tac
  >> irule bounded_packed_compute_eval_literal_app3
  >> simp [bounded_packed_q_error6_lookup]
QED

Theorem bounded_packed_q_source_error6_encoded:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 ==>
  bounded_object_q_encoded
    (bounded_packed_q_source_error6_cv radii center_gradient packed)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedObjectQuadraticBodyEvalTheory.bounded_packed_q_radii6_encoded
  >> simp
       [bounded_packed_q_source_error6_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded,
        compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_encoded,
        compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_suffix6_encoded]
QED

Theorem bounded_packed_q_double_linear_add_quadratic_eval:
  bounded_object_q_encoded linear_value /\
  bounded_object_q_encoded quadratic_value /\
  4 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_add»
        [App «candle_cv_q_add»
          [from_cv linear_value;from_cv linear_value];
         from_cv quadratic_value]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_add_cv
          (bounded_object_q_add_cv linear_value linear_value)
          quadratic_value)),refs)
Proof
  strip_tac
  >> `bounded_object_q_encoded
        (bounded_object_q_add_cv linear_value linear_value)` by
       simp
         [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded]
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_add»
          [from_cv linear_value;from_cv linear_value]) refs =
      (M_success
        (from_cv
          (bounded_object_q_add_cv linear_value linear_value)),refs)` by
       (irule
          compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_add_eval
        >> simp [])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_add»
            [from_cv
              (bounded_object_q_add_cv linear_value linear_value);
             from_cv quadratic_value]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> irule
       compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_add_eval
  >> simp []
QED

Theorem bounded_packed_q_error6_body_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  96 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (subst
        [(«radii»,from_cv (bounded_object_q_cv_list radii));
         («center_gradient»,from_cv
            (bounded_object_q_cv_list center_gradient));
         («packed»,from_cv (bounded_object_q_cv_list packed))]
        bounded_packed_q_error6_body) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_error6_cv
          radii center_gradient packed)),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedObjectQuadraticBodyEvalTheory.bounded_packed_q_radii6_encoded
  >> simp
       [bounded_packed_q_error6_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_dot_abs_upper_cv radii center_gradient`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_q_dot_abs_upper_recursive_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          0 (HD radii) (EL 1 radii) (EL 2 radii)
          (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectQuadraticBodyEvalTheory.bounded_packed_q_quadratic_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_q_source_error6_cv_def]
  >> irule bounded_packed_q_double_linear_add_quadratic_eval
  >> simp
       [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_encoded,
        compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_suffix6_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_error6_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  97 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_object_error6»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv (bounded_object_q_cv_list center_gradient);
         from_cv (bounded_object_q_cv_list packed)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_error6_cv
          radii center_gradient packed)),refs)
Proof
  strip_tac
  >> rw [bounded_packed_q_error6_unfold]
  >> irule bounded_packed_q_error6_body_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
