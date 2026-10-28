(*****************************************************************************
 * One exact source-faithful packed quadratic contribution.
 *****************************************************************************)
Theory compute_boundedPackedObjectQuadraticTermEval
Ancestors
  compute_boundedPackedObjectLookupEval
Libs
  bossLib preamble intLib

Definition bounded_packed_q_quadratic_term_body_def:
  bounded_packed_q_quadratic_term_body =
    Let «raw»
      (App «candle_cv_q_mul»
        [App «candle_cv_q_mul»
          [Var «left_radius»;Var «right_radius»];
         App «candle_cv_q_abs_upper» [Var «entry»]])
      (If (Var «twice»)
        (App «candle_cv_q_add» [Var «raw»;Var «raw»])
        (Var «raw»))
End

Definition bounded_packed_q_source_quadratic_raw_cv_def:
  bounded_packed_q_source_quadratic_raw_cv left right entry =
    bounded_object_q_mul_cv
      (bounded_object_q_mul_cv left right)
      (bounded_packed_q_source_abs_upper_cv entry)
End

Definition bounded_packed_q_source_quadratic_term_cv_def:
  bounded_packed_q_source_quadratic_term_cv left right twice entry =
    let raw =
      bounded_packed_q_source_quadratic_raw_cv left right entry in
      if twice then bounded_object_q_add_cv raw raw else raw
End

Theorem bounded_packed_q_quadratic_term_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs
      «candle_cv_q_packed_quadratic_term» =
    SOME
      ([«left_radius»;«right_radius»;«twice»;«entry»],
       bounded_packed_q_quadratic_term_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_compute_eval_literal_app4:
  0 < clock /\
  ALOOKUP ceqs function_name =
      SOME ([name1;name2;name3;name4],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv value1;from_cv value2;from_cv value3;from_cv value4])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv value1);(name2,from_cv value2);
         (name3,from_cv value3);(name4,from_cv value4)] body) refs
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

Theorem bounded_packed_q_quadratic_term_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_quadratic_term»
        [from_cv left;from_cv right;from_cv twice;from_cv entry])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst
        [(«left_radius»,from_cv left);(«right_radius»,from_cv right);
         («twice»,from_cv twice);(«entry»,from_cv entry)]
        bounded_packed_q_quadratic_term_body) refs
Proof
  strip_tac
  >> irule bounded_packed_compute_eval_literal_app4
  >> simp [bounded_packed_q_quadratic_term_lookup]
QED

Theorem bounded_packed_q_source_quadratic_raw_encoded:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  bounded_packed_q_interval_encoded entry ==>
  bounded_object_q_encoded
    (bounded_packed_q_source_quadratic_raw_cv left right entry)
Proof
  strip_tac
  >> rw [bounded_packed_q_source_quadratic_raw_cv_def]
  >> irule compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded
  >> simp
       [compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
        compute_boundedPackedObjectPrimitiveAbsContractTheory.bounded_packed_q_source_abs_upper_encoded]
QED

Theorem bounded_packed_q_source_quadratic_term_encoded:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  bounded_packed_q_interval_encoded entry ==>
  bounded_object_q_encoded
    (bounded_packed_q_source_quadratic_term_cv left right twice entry)
Proof
  strip_tac
  >> Cases_on `twice`
  >> simp
       [bounded_packed_q_source_quadratic_term_cv_def,
        bounded_packed_q_source_quadratic_raw_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded]
QED

Theorem bounded_packed_q_quadratic_raw_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  bounded_packed_q_interval_encoded entry /\
  6 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_mul»
        [App «candle_cv_q_mul» [from_cv left;from_cv right];
         App «candle_cv_q_abs_upper» [from_cv entry]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_quadratic_raw_cv left right entry)),refs)
Proof
  strip_tac
  >> `bounded_object_q_encoded (bounded_object_q_mul_cv left right)` by
       simp
         [compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded]
  >> `bounded_object_q_encoded
        (bounded_packed_q_source_abs_upper_cv entry)` by
       simp
         [compute_boundedPackedObjectPrimitiveAbsContractTheory.bounded_packed_q_source_abs_upper_encoded]
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_mul» [from_cv left;from_cv right]) refs =
      (M_success (from_cv (bounded_object_q_mul_cv left right)),refs)` by
       (irule
          compute_boundedPackedObjectPrimitiveMulEvalTheory.bounded_packed_q_mul_eval
        >> simp [])
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_abs_upper» [from_cv entry]) refs =
      (M_success
        (from_cv (bounded_packed_q_source_abs_upper_cv entry)),refs)` by
       (irule
          compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_source_abs_upper_eval
        >> simp [])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_mul»
            [from_cv (bounded_object_q_mul_cv left right);
             from_cv (bounded_packed_q_source_abs_upper_cv entry)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [])
  >> rw [bounded_packed_q_source_quadratic_raw_cv_def]
  >> irule
       compute_boundedPackedObjectPrimitiveMulEvalTheory.bounded_packed_q_mul_eval
  >> simp []
QED

Theorem bounded_packed_compute_eval_let_result:
  0 < clock /\
  compute_eval clock ceqs bound (refs:hol_refs) =
      (M_success (from_cv value),refs) /\
  compute_eval (clock - 1) ceqs
      (subst [(name,from_cv value)] body) refs = result ==>
  compute_eval clock ceqs (Let name bound body) refs = result
Proof
  Cases_on `clock`
  >> simp
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_compute_eval_if_num_true:
  0 < clock ==>
  compute_eval clock ceqs
      (If (Num 1) true_branch false_branch) (refs:hol_refs) =
    compute_eval clock ceqs true_branch refs
Proof
  Cases_on `clock`
  >> simp
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_compute_eval_if_num_false:
  0 < clock ==>
  compute_eval clock ceqs
      (If (Num 0) true_branch false_branch) (refs:hol_refs) =
    compute_eval clock ceqs false_branch refs
Proof
  Cases_on `clock`
  >> simp
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_quadratic_after_raw_eval:
  bounded_object_q_encoded raw /\ 3 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (If (Num (if twice then 1 else 0))
        (App «candle_cv_q_add» [from_cv raw;from_cv raw])
        (from_cv raw)) (refs:hol_refs) =
    (M_success
      (from_cv (if twice then bounded_object_q_add_cv raw raw else raw)),
     refs)
Proof
  Cases_on `twice`
  >> strip_tac
  >- (rw [bounded_packed_compute_eval_if_num_true]
      >> irule
           compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_add_eval
      >> simp [])
  >> rw [bounded_packed_compute_eval_if_num_false]
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_q_quadratic_term_body_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  bounded_packed_q_interval_encoded entry /\
  7 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (Let «raw»
        (App «candle_cv_q_mul»
          [App «candle_cv_q_mul» [from_cv left;from_cv right];
           App «candle_cv_q_abs_upper» [from_cv entry]])
        (If (Num (if twice then 1 else 0))
          (App «candle_cv_q_add» [Var «raw»;Var «raw»])
          (Var «raw»))) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_quadratic_term_cv
          left right twice entry)),refs)
Proof
  strip_tac
  >> irule bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_raw_cv left right entry`
  >> conj_tac
  >- (irule bounded_packed_q_quadratic_raw_eval
      >> simp [])
  >> simp
       [bounded_packed_q_source_quadratic_term_cv_def,
        compute_evalTheory.subst_def]
  >> irule bounded_packed_q_quadratic_after_raw_eval
  >> simp [bounded_packed_q_source_quadratic_raw_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_quadratic_term_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  bounded_packed_q_interval_encoded entry /\
  8 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_quadratic_term»
        [from_cv left;from_cv right;
         from_cv (Num (if twice then 1 else 0));from_cv entry])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_quadratic_term_cv
          left right twice entry)),refs)
Proof
  strip_tac
  >> rw [bounded_packed_q_quadratic_term_unfold]
  >> simp
       [bounded_packed_q_quadratic_term_body_def,
        compute_evalTheory.subst_def]
  >> FIRST
       [irule
          (SIMP_RULE std_ss []
            (Q.INST [`twice` |-> `T`]
              bounded_packed_q_quadratic_term_body_eval)),
        irule
          (SIMP_RULE std_ss []
            (Q.INST [`twice` |-> `F`]
              bounded_packed_q_quadratic_term_body_eval))]
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
