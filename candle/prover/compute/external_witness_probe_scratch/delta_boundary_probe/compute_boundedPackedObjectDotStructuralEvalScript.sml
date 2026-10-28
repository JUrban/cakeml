(*****************************************************************************
 * One dot step in the exact syntactic shape produced by list destructuring.
 *****************************************************************************)
Theory compute_boundedPackedObjectDotStructuralEval
Ancestors
  compute_boundedPackedObjectDotConsEval
Libs
  bossLib preamble intLib

Theorem bounded_packed_q_dot_cons_structural_eval:
  bounded_object_q_encoded radius /\
  bounded_packed_q_interval_encoded entry /\
  bounded_object_q_encoded tail_result /\
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_dot_abs_upper»
        [from_cv tail_radii;from_cv tail_entries])
      (refs:hol_refs) =
    (M_success (from_cv tail_result),refs) /\
  6 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_add»
        [App «candle_cv_q_mul»
          [Uop Fst
             (Pair (from_cv radius) (from_cv tail_radii));
           App «candle_cv_q_abs_upper»
             [Uop Fst
               (Pair (from_cv entry) (from_cv tail_entries))]];
         App «candle_cv_q_dot_abs_upper»
           [Uop Snd
              (Pair (from_cv radius) (from_cv tail_radii));
            Uop Snd
              (Pair (from_cv entry) (from_cv tail_entries))]])
      refs =
    (M_success
      (from_cv
        (bounded_object_q_add_cv
          (bounded_object_q_mul_cv radius
            (bounded_packed_q_source_abs_upper_cv entry))
          tail_result)),refs)
Proof
  strip_tac
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (Uop Fst (Pair (from_cv radius) (from_cv tail_radii))) refs =
      (M_success (from_cv radius),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_fst_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (Uop Fst (Pair (from_cv entry) (from_cv tail_entries))) refs =
      (M_success (from_cv entry),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_fst_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (Uop Snd (Pair (from_cv radius) (from_cv tail_radii))) refs =
      (M_success (from_cv tail_radii),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_snd_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (Uop Snd (Pair (from_cv entry) (from_cv tail_entries))) refs =
      (M_success (from_cv tail_entries),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_snd_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_abs_upper»
          [Uop Fst
            (Pair (from_cv entry) (from_cv tail_entries))]) refs =
      (M_success
        (from_cv (bounded_packed_q_source_abs_upper_cv entry)),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval clock bounded_packed_object_entry_ceqs
                (App «candle_cv_q_abs_upper» [from_cv entry]) refs`
        >> conj_tac
        >- (irule
              compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app1_argument_result
            >> simp []
            >> intLib.ARITH_TAC)
        >> irule
             compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_source_abs_upper_eval
        >> simp [])
  >> `bounded_object_q_encoded
        (bounded_packed_q_source_abs_upper_cv entry)` by
       (irule
          compute_boundedPackedObjectPrimitiveAbsContractTheory.bounded_packed_q_source_abs_upper_encoded
        >> simp [])
  >> `bounded_object_q_encoded
        (bounded_object_q_mul_cv radius
          (bounded_packed_q_source_abs_upper_cv entry))` by
       (irule compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded
        >> simp [])
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_mul»
          [Uop Fst (Pair (from_cv radius) (from_cv tail_radii));
           App «candle_cv_q_abs_upper»
             [Uop Fst
               (Pair (from_cv entry) (from_cv tail_entries))]]) refs =
      (M_success
        (from_cv
          (bounded_object_q_mul_cv radius
            (bounded_packed_q_source_abs_upper_cv entry))),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval clock bounded_packed_object_entry_ceqs
                (App «candle_cv_q_mul»
                  [from_cv radius;
                   from_cv (bounded_packed_q_source_abs_upper_cv entry)]) refs`
        >> conj_tac
        >- (irule
              compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
            >> simp []
            >> intLib.ARITH_TAC)
        >> irule
             compute_boundedPackedObjectPrimitiveMulEvalTheory.bounded_packed_q_mul_eval
        >> simp []
        >> intLib.ARITH_TAC)
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_dot_abs_upper»
          [Uop Snd (Pair (from_cv radius) (from_cv tail_radii));
           Uop Snd (Pair (from_cv entry) (from_cv tail_entries))]) refs =
      (M_success (from_cv tail_result),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval clock bounded_packed_object_entry_ceqs
                (App «candle_cv_q_dot_abs_upper»
                  [from_cv tail_radii;from_cv tail_entries]) refs`
        >> conj_tac
        >- (irule
              compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
            >> simp []
            >> intLib.ARITH_TAC)
        >> simp [])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_add»
            [from_cv
              (bounded_object_q_mul_cv radius
                (bounded_packed_q_source_abs_upper_cv entry));
             from_cv tail_result]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_add_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
