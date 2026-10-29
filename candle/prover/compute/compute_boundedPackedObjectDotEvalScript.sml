(*****************************************************************************
 * Source-faithful right-associated dot evaluation for the exported entry.
 *****************************************************************************)
Theory compute_boundedPackedObjectDotEval
Ancestors
  compute_boundedPackedObjectPrimitiveAbsContract
  compute_boundedPackedObjectEntryContract
Libs
  bossLib preamble intLib

Definition bounded_packed_q_zero_body_def:
  bounded_packed_q_zero_body : compute_exp =
    Pair (Pair (Num 0) (Num 0)) (Num 0)
End

Definition bounded_packed_q_dot_abs_upper_body_def:
  bounded_packed_q_dot_abs_upper_body =
    If (Uop Ispair (Var «xs»))
      (If (Uop Ispair (Var «ys»))
        (App «candle_cv_q_add»
          [App «candle_cv_q_mul»
            [Uop Fst (Var «xs»);
             App «candle_cv_q_abs_upper» [Uop Fst (Var «ys»)]];
           App «candle_cv_q_dot_abs_upper»
             [Uop Snd (Var «xs»);Uop Snd (Var «ys»)]])
        (App «candle_cv_q_zero» []))
      (App «candle_cv_q_zero» [])
End

Definition bounded_packed_q_source_dot_abs_upper_cv_def:
  bounded_packed_q_source_dot_abs_upper_cv [] entries =
      bounded_object_q_zero_cv /\
  bounded_packed_q_source_dot_abs_upper_cv (_::_) [] =
      bounded_object_q_zero_cv /\
  bounded_packed_q_source_dot_abs_upper_cv
      (radius::radii) (entry::entries) =
    bounded_object_q_add_cv
      (bounded_object_q_mul_cv radius
        (bounded_packed_q_source_abs_upper_cv entry))
      (bounded_packed_q_source_dot_abs_upper_cv radii entries)
End

Theorem bounded_packed_q_zero_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_q_zero» =
    SOME ([],bounded_packed_q_zero_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_dot_abs_upper_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs
      «candle_cv_q_dot_abs_upper» =
    SOME ([«xs»;«ys»],bounded_packed_q_dot_abs_upper_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_zero_eval:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_zero» []) (refs:hol_refs) =
    (M_success (from_cv bounded_object_q_zero_cv),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_q_zero_lookup,
        bounded_packed_q_zero_body_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_compute_eval_literal_app2:
  0 < clock /\
  ALOOKUP ceqs function_name =
      SOME ([argument1_name;argument2_name],body) ==>
  compute_eval clock ceqs
      (App function_name [from_cv argument1;from_cv argument2])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(argument1_name,from_cv argument1);
         (argument2_name,from_cv argument2)] body) refs
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

Theorem bounded_packed_q_dot_abs_upper_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_dot_abs_upper» [from_cv xs;from_cv ys])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst [(«xs»,from_cv xs);(«ys»,from_cv ys)]
        bounded_packed_q_dot_abs_upper_body) refs
Proof
  strip_tac
  >> irule bounded_packed_compute_eval_literal_app2
  >> simp [bounded_packed_q_dot_abs_upper_lookup]
QED

Theorem bounded_packed_q_source_dot_abs_upper_encoded:
  !radii entries.
    EVERY bounded_object_q_encoded radii /\
    EVERY bounded_packed_q_interval_encoded entries ==>
    bounded_object_q_encoded
      (bounded_packed_q_source_dot_abs_upper_cv radii entries)
Proof
  Induct_on `radii`
  >> Cases_on `entries`
  >> simp
       [bounded_packed_q_source_dot_abs_upper_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded]
  >> metis_tac
       [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
        compute_boundedPackedObjectPrimitiveAbsContractTheory.bounded_packed_q_source_abs_upper_encoded]
QED

val _ = export_theory ();
