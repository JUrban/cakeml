(*****************************************************************************
 * Recursive refinement of the exported dot helper on canonical cv lists.
 *****************************************************************************)
Theory compute_boundedPackedObjectDotRecursiveEval
Ancestors
  compute_boundedPackedObjectDotStructuralEval
Libs
  bossLib preamble intLib

Theorem bounded_packed_compute_eval_if_ispair_num:
  compute_eval clock ceqs
      (If (Uop Ispair (Num n)) pair_branch number_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs number_branch refs
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_compute_eval_if_ispair_pair:
  compute_eval clock ceqs
      (If (Uop Ispair (Pair (from_cv left) (from_cv right)))
        pair_branch number_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs pair_branch refs
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_dot_abs_upper_recursive_eval:
  !radii entries clock refs.
    EVERY bounded_object_q_encoded radii /\
    EVERY bounded_packed_q_interval_encoded entries /\
    12 * (LENGTH radii + 1) < clock ==>
    compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_dot_abs_upper»
          [from_cv (bounded_object_q_cv_list radii);
           from_cv (bounded_object_q_cv_list entries)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_packed_q_source_dot_abs_upper_cv radii entries)),refs)
Proof
  Induct_on `radii`
  >- (rw
        [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_cv_def]
      >> rw
           [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_dot_abs_upper_unfold]
      >> simp
           [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_dot_abs_upper_body_def,
            compute_evalTheory.subst_def,
            compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            bounded_packed_compute_eval_if_ispair_num,
            compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_zero_eval])
  >> Cases_on `entries`
  >- (rw
        [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_cv_def]
      >> rw
           [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_dot_abs_upper_unfold]
      >> simp
           [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_dot_abs_upper_body_def,
            compute_evalTheory.subst_def,
            compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            bounded_packed_compute_eval_if_ispair_num,
            bounded_packed_compute_eval_if_ispair_pair,
            compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_zero_eval])
  >> rw
       [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_cv_def]
  >> rw
       [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_dot_abs_upper_unfold]
  >> simp
       [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_dot_abs_upper_body_def,
        compute_evalTheory.subst_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        bounded_packed_compute_eval_if_ispair_pair]
  >> `compute_eval (clock - 1) bounded_packed_object_entry_ceqs
        (App «candle_cv_q_dot_abs_upper»
          [from_cv (bounded_object_q_cv_list radii);
           from_cv (bounded_object_q_cv_list t)]) refs =
      (M_success
        (from_cv
          (bounded_packed_q_source_dot_abs_upper_cv radii t)),refs)` by
       (qpat_x_assum `!entries clock refs. _`
          (qspecl_then [`t`,`clock - 1`,`refs`] mp_tac)
        >> simp []
        >> intLib.ARITH_TAC)
  >> irule
       compute_boundedPackedObjectDotStructuralEvalTheory.bounded_packed_q_dot_cons_structural_eval
  >> simp
       [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_encoded]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
