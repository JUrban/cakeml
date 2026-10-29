(*****************************************************************************
 * Exact source-faithful evaluation of the exported six-variable quadratic.
 *****************************************************************************)
Theory compute_boundedPackedObjectQuadraticEval
Ancestors
  compute_boundedPackedObjectQuadraticTermAtEval
Libs
  bossLib preamble intLib

Definition bounded_packed_q_quadratic_body_def:
  bounded_packed_q_quadratic_body =
    Let «r0» (App «candle_cv_q_list_lookup» [Num 0;Var «radii»]) (Let «r1» (App «candle_cv_q_list_lookup» [Num 1;Var «radii»]) (Let «r2» (App «candle_cv_q_list_lookup» [Num 2;Var «radii»]) (Let «r3» (App «candle_cv_q_list_lookup» [Num 3;Var «radii»]) (Let «r4» (App «candle_cv_q_list_lookup» [Num 4;Var «radii»]) (Let «r5» (App «candle_cv_q_list_lookup» [Num 5;Var «radii»]) (Let «true_flag» (Num 1) (Let «a20» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 20;Var «r5»;Var «r5»;Num 0];App «candle_cv_q_zero» []]) (Let «a19» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 19;Var «r4»;Var «r5»;Var «true_flag»];Var «a20»]) (Let «a18» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 18;Var «r4»;Var «r4»;Num 0];Var «a19»]) (Let «a17» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 17;Var «r3»;Var «r5»;Var «true_flag»];Var «a18»]) (Let «a16» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 16;Var «r3»;Var «r4»;Var «true_flag»];Var «a17»]) (Let «a15» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 15;Var «r3»;Var «r3»;Num 0];Var «a16»]) (Let «a14» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 14;Var «r2»;Var «r5»;Var «true_flag»];Var «a15»]) (Let «a13» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 13;Var «r2»;Var «r4»;Var «true_flag»];Var «a14»]) (Let «a12» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 12;Var «r2»;Var «r3»;Var «true_flag»];Var «a13»]) (Let «a11» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 11;Var «r2»;Var «r2»;Num 0];Var «a12»]) (Let «a10» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 10;Var «r1»;Var «r5»;Var «true_flag»];Var «a11»]) (Let «a9» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 9;Var «r1»;Var «r4»;Var «true_flag»];Var «a10»]) (Let «a8» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 8;Var «r1»;Var «r3»;Var «true_flag»];Var «a9»]) (Let «a7» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 7;Var «r1»;Var «r2»;Var «true_flag»];Var «a8»]) (Let «a6» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 6;Var «r1»;Var «r1»;Num 0];Var «a7»]) (Let «a5» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 5;Var «r0»;Var «r5»;Var «true_flag»];Var «a6»]) (Let «a4» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 4;Var «r0»;Var «r4»;Var «true_flag»];Var «a5»]) (Let «a3» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 3;Var «r0»;Var «r3»;Var «true_flag»];Var «a4»]) (Let «a2» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 2;Var «r0»;Var «r2»;Var «true_flag»];Var «a3»]) (Let «a1» (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 1;Var «r0»;Var «r1»;Var «true_flag»];Var «a2»]) (App «candle_cv_q_add» [App «candle_cv_q_packed_quadratic_term_at» [Var «packed»;Num 0;Var «r0»;Var «r0»;Num 0];Var «a1»])))))))))))))))))))))))))))
End

Definition bounded_packed_q_source_quadratic_terms6_cv_def:
  bounded_packed_q_source_quadratic_terms6_cv r0 r1 r2 r3 r4 r5 packed =
    [bounded_packed_q_source_quadratic_term_cv r0 r0 F (EL 0 packed);
     bounded_packed_q_source_quadratic_term_cv r0 r1 T (EL 1 packed);
     bounded_packed_q_source_quadratic_term_cv r0 r2 T (EL 2 packed);
     bounded_packed_q_source_quadratic_term_cv r0 r3 T (EL 3 packed);
     bounded_packed_q_source_quadratic_term_cv r0 r4 T (EL 4 packed);
     bounded_packed_q_source_quadratic_term_cv r0 r5 T (EL 5 packed);
     bounded_packed_q_source_quadratic_term_cv r1 r1 F (EL 6 packed);
     bounded_packed_q_source_quadratic_term_cv r1 r2 T (EL 7 packed);
     bounded_packed_q_source_quadratic_term_cv r1 r3 T (EL 8 packed);
     bounded_packed_q_source_quadratic_term_cv r1 r4 T (EL 9 packed);
     bounded_packed_q_source_quadratic_term_cv r1 r5 T (EL 10 packed);
     bounded_packed_q_source_quadratic_term_cv r2 r2 F (EL 11 packed);
     bounded_packed_q_source_quadratic_term_cv r2 r3 T (EL 12 packed);
     bounded_packed_q_source_quadratic_term_cv r2 r4 T (EL 13 packed);
     bounded_packed_q_source_quadratic_term_cv r2 r5 T (EL 14 packed);
     bounded_packed_q_source_quadratic_term_cv r3 r3 F (EL 15 packed);
     bounded_packed_q_source_quadratic_term_cv r3 r4 T (EL 16 packed);
     bounded_packed_q_source_quadratic_term_cv r3 r5 T (EL 17 packed);
     bounded_packed_q_source_quadratic_term_cv r4 r4 F (EL 18 packed);
     bounded_packed_q_source_quadratic_term_cv r4 r5 T (EL 19 packed);
     bounded_packed_q_source_quadratic_term_cv r5 r5 F (EL 20 packed)]
End

Definition bounded_packed_q_source_quadratic_suffix6_cv_def:
  bounded_packed_q_source_quadratic_suffix6_cv
      index r0 r1 r2 r3 r4 r5 packed =
    bounded_object_q_right_sum_cv
      (DROP index
        (bounded_packed_q_source_quadratic_terms6_cv
          r0 r1 r2 r3 r4 r5 packed))
End

Theorem bounded_packed_q_quadratic_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs
      «candle_cv_q_packed_quadratic_abs_upper6» =
    SOME ([«radii»;«packed»],bounded_packed_q_quadratic_body)
Proof
  rw [bounded_packed_q_quadratic_body_def]
  >> EVAL_TAC
QED

Theorem bounded_packed_q_quadratic_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_quadratic_abs_upper6»
        [from_cv radii;from_cv packed]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst [(«radii»,from_cv radii);(«packed»,from_cv packed)]
        bounded_packed_q_quadratic_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectDotEvalTheory.bounded_packed_compute_eval_literal_app2
  >> simp [bounded_packed_q_quadratic_lookup]
QED

Theorem bounded_packed_q_interval_el_encoded:
  EVERY bounded_packed_q_interval_encoded packed /\
  index < LENGTH packed ==>
  bounded_packed_q_interval_encoded (EL index packed)
Proof
  metis_tac [listTheory.EVERY_EL]
QED

Theorem bounded_packed_q_source_quadratic_term_el_encoded:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  EVERY bounded_packed_q_interval_encoded packed /\
  index < LENGTH packed ==>
  bounded_object_q_encoded
    (bounded_packed_q_source_quadratic_term_cv
      left right twice (EL index packed))
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_q_source_quadratic_term_encoded
  >> simp [bounded_packed_q_interval_el_encoded]
QED

Theorem bounded_packed_q_source_quadratic_terms6_encoded:
  bounded_object_q_encoded r0 /\
  bounded_object_q_encoded r1 /\
  bounded_object_q_encoded r2 /\
  bounded_object_q_encoded r3 /\
  bounded_object_q_encoded r4 /\
  bounded_object_q_encoded r5 /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 ==>
  EVERY bounded_object_q_encoded
    (bounded_packed_q_source_quadratic_terms6_cv
      r0 r1 r2 r3 r4 r5 packed)
Proof
  strip_tac
  >> PURE_REWRITE_TAC
       [bounded_packed_q_source_quadratic_terms6_cv_def,
        listTheory.EVERY_DEF]
  >> rpt conj_tac
  >> FIRST
       [irule bounded_packed_q_source_quadratic_term_el_encoded
        >> simp [],
        simp []]
QED

Theorem bounded_packed_q_right_sum_drop_step:
  index < LENGTH values ==>
  bounded_object_q_right_sum_cv (DROP index values) =
    bounded_object_q_add_cv (EL index values)
      (bounded_object_q_right_sum_cv (DROP (index + 1) values))
Proof
  strip_tac
  >> `DROP index values = EL index values :: DROP (index + 1) values` by
       metis_tac [rich_listTheory.DROP_EL_CONS]
  >> simp
       [compute_boundedQFoldRelationTheory.bounded_object_q_right_sum_cv_def]
QED

Theorem bounded_packed_q_source_quadratic_suffix6_step:
  index < 21 ==>
  bounded_packed_q_source_quadratic_suffix6_cv
      index r0 r1 r2 r3 r4 r5 packed =
    bounded_object_q_add_cv
      (EL index
        (bounded_packed_q_source_quadratic_terms6_cv
          r0 r1 r2 r3 r4 r5 packed))
      (bounded_packed_q_source_quadratic_suffix6_cv
        (index + 1) r0 r1 r2 r3 r4 r5 packed)
Proof
  strip_tac
  >> rw [bounded_packed_q_source_quadratic_suffix6_cv_def]
  >> irule bounded_packed_q_right_sum_drop_step
  >> simp [bounded_packed_q_source_quadratic_terms6_cv_def]
QED

Theorem bounded_packed_q_source_quadratic_suffix6_encoded:
  bounded_object_q_encoded r0 /\
  bounded_object_q_encoded r1 /\
  bounded_object_q_encoded r2 /\
  bounded_object_q_encoded r3 /\
  bounded_object_q_encoded r4 /\
  bounded_object_q_encoded r5 /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 ==>
  bounded_object_q_encoded
    (bounded_packed_q_source_quadratic_suffix6_cv
      index r0 r1 r2 r3 r4 r5 packed)
Proof
  strip_tac
  >> rw [bounded_packed_q_source_quadratic_suffix6_cv_def]
  >> irule
       compute_boundedQFoldRelationTheory.bounded_object_q_right_sum_cv_encoded
  >> irule rich_listTheory.EVERY_DROP
  >> irule bounded_packed_q_source_quadratic_terms6_encoded
  >> simp []
QED

Theorem bounded_packed_q_source_quadratic_suffix6_21:
  bounded_packed_q_source_quadratic_suffix6_cv
      21 r0 r1 r2 r3 r4 r5 packed = bounded_object_q_zero_cv
Proof
  simp
    [bounded_packed_q_source_quadratic_suffix6_cv_def,
     bounded_packed_q_source_quadratic_terms6_cv_def,
     compute_boundedQFoldRelationTheory.bounded_object_q_right_sum_cv_def]
QED

Theorem bounded_packed_q_quadratic_term_at_add_arguments:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  EVERY bounded_packed_q_interval_encoded packed /\
  index < LENGTH packed /\
  index + 10 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_add»
        [App «candle_cv_q_packed_quadratic_term_at»
          [from_cv (bounded_object_q_cv_list packed);from_cv (Num index);
           from_cv left;from_cv right;
           from_cv (Num (if twice then 1 else 0))];
         from_cv accumulator]) (refs:hol_refs) =
    compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_add»
        [from_cv
          (bounded_packed_q_source_quadratic_term_cv
            left right twice (EL index packed));
         from_cv accumulator]) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
  >> conj_tac
  >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectQuadraticTermAtEvalTheory.bounded_packed_q_quadratic_term_at_eval
      >> simp [])
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_q_quadratic_term_at_add_result_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  EVERY bounded_packed_q_interval_encoded packed /\
  index < LENGTH packed /\
  bounded_object_q_encoded accumulator /\
  compute_eval clock bounded_packed_object_entry_ceqs accumulator_expression
      (refs:hol_refs) = (M_success (from_cv accumulator),refs) /\
  index + 10 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_add»
        [App «candle_cv_q_packed_quadratic_term_at»
          [from_cv (bounded_object_q_cv_list packed);from_cv (Num index);
           from_cv left;from_cv right;
           from_cv (Num (if twice then 1 else 0))];
         accumulator_expression]) refs =
    (M_success
      (from_cv
        (bounded_object_q_add_cv
          (bounded_packed_q_source_quadratic_term_cv
            left right twice (EL index packed))
          accumulator)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_add»
            [from_cv
              (bounded_packed_q_source_quadratic_term_cv
                left right twice (EL index packed));
             from_cv accumulator]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            compute_boundedPackedObjectQuadraticTermAtEvalTheory.bounded_packed_q_quadratic_term_at_eval
          >> simp [])
      >> simp [])
  >> irule
       compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_add_eval
  >> conj_tac
  >- (irule bounded_packed_q_source_quadratic_term_el_encoded
      >> simp [])
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_quadratic_term_at_suffix_result_eval:
  bounded_object_q_encoded r0 /\
  bounded_object_q_encoded r1 /\
  bounded_object_q_encoded r2 /\
  bounded_object_q_encoded r3 /\
  bounded_object_q_encoded r4 /\
  bounded_object_q_encoded r5 /\
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  index < 21 /\
  EL index
      (bounded_packed_q_source_quadratic_terms6_cv
        r0 r1 r2 r3 r4 r5 packed) =
    bounded_packed_q_source_quadratic_term_cv
      left right twice (EL index packed) /\
  compute_eval clock bounded_packed_object_entry_ceqs accumulator_expression
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_quadratic_suffix6_cv
          (index + 1) r0 r1 r2 r3 r4 r5 packed)),refs) /\
  index + 10 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_add»
        [App «candle_cv_q_packed_quadratic_term_at»
          [from_cv (bounded_object_q_cv_list packed);from_cv (Num index);
           from_cv left;from_cv right;
           from_cv (Num (if twice then 1 else 0))];
         accumulator_expression]) refs =
    (M_success
      (from_cv
        (bounded_packed_q_source_quadratic_suffix6_cv
          index r0 r1 r2 r3 r4 r5 packed)),refs)
Proof
  strip_tac
  >> `bounded_object_q_encoded
        (bounded_packed_q_source_quadratic_suffix6_cv
          (index + 1) r0 r1 r2 r3 r4 r5 packed)` by
       (irule bounded_packed_q_source_quadratic_suffix6_encoded
        >> simp [])
  >> irule EQ_TRANS
  >> qexists_tac
       `(M_success
          (from_cv
            (bounded_object_q_add_cv
              (bounded_packed_q_source_quadratic_term_cv
                left right twice (EL index packed))
              (bounded_packed_q_source_quadratic_suffix6_cv
                (index + 1) r0 r1 r2 r3 r4 r5 packed))),refs)`
  >> conj_tac
  >- (irule bounded_packed_q_quadratic_term_at_add_result_eval
      >> simp [])
  >> `bounded_packed_q_source_quadratic_suffix6_cv
        index r0 r1 r2 r3 r4 r5 packed =
      bounded_object_q_add_cv
        (EL index
          (bounded_packed_q_source_quadratic_terms6_cv
            r0 r1 r2 r3 r4 r5 packed))
        (bounded_packed_q_source_quadratic_suffix6_cv
          (index + 1) r0 r1 r2 r3 r4 r5 packed)` by
       (irule bounded_packed_q_source_quadratic_suffix6_step
        >> simp [])
  >> simp []
QED

Theorem bounded_packed_q_quadratic_term_at_add_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  EVERY bounded_packed_q_interval_encoded packed /\
  index < LENGTH packed /\
  bounded_object_q_encoded accumulator /\
  index + 10 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_add»
        [App «candle_cv_q_packed_quadratic_term_at»
          [from_cv (bounded_object_q_cv_list packed);from_cv (Num index);
           from_cv left;from_cv right;
           from_cv (Num (if twice then 1 else 0))];
         from_cv accumulator]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_add_cv
          (bounded_packed_q_source_quadratic_term_cv
            left right twice (EL index packed))
          accumulator)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_add»
            [from_cv
              (bounded_packed_q_source_quadratic_term_cv
                left right twice (EL index packed));
             from_cv accumulator]) refs`
  >> conj_tac
  >- (irule bounded_packed_q_quadratic_term_at_add_arguments
      >> simp [])
  >> irule
       compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_add_eval
  >> conj_tac
  >- (irule bounded_packed_q_source_quadratic_term_el_encoded
      >> simp [])
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
