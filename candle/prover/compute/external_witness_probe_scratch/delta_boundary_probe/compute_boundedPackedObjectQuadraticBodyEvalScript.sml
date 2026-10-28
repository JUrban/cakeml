(*****************************************************************************
 * The fixed Let schedule exported for the six-variable packed quadratic.
 *****************************************************************************)
Theory compute_boundedPackedObjectQuadraticBodyEval
Ancestors
  compute_boundedPackedObjectQuadraticEval
Libs
  bossLib preamble intLib

val _ = augment_srw_ss
  [rewrites [compute_execProofTheory.subst_from_cv]]

val bounded_packed_q_quadratic_term_at_suffix_result_eval_false_literal =
  SIMP_RULE std_ss [compute_execTheory.from_cv_def]
    (Q.INST [`twice` |-> `F`]
      compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_quadratic_term_at_suffix_result_eval)

val bounded_packed_q_quadratic_term_at_suffix_result_eval_true_literal =
  SIMP_RULE std_ss [compute_execTheory.from_cv_def]
    (Q.INST [`twice` |-> `T`]
      compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_quadratic_term_at_suffix_result_eval)

val bounded_packed_q_irule_quadratic_suffix_result =
  FIRST
    [irule bounded_packed_q_quadratic_term_at_suffix_result_eval_false_literal,
     irule bounded_packed_q_quadratic_term_at_suffix_result_eval_true_literal]

Theorem bounded_packed_q_hd_encoded:
  EVERY bounded_object_q_encoded values /\ 0 < LENGTH values ==>
  bounded_object_q_encoded (HD values)
Proof
  Cases_on `values`
  >> simp []
QED

Theorem bounded_packed_q_el_encoded:
  EVERY bounded_object_q_encoded values /\ index < LENGTH values ==>
  bounded_object_q_encoded (EL index values)
Proof
  metis_tac [listTheory.EVERY_EL]
QED

Theorem bounded_packed_q_radii6_encoded:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 ==>
  bounded_object_q_encoded (HD radii) /\
  bounded_object_q_encoded (EL 1 radii) /\
  bounded_object_q_encoded (EL 2 radii) /\
  bounded_object_q_encoded (EL 3 radii) /\
  bounded_object_q_encoded (EL 4 radii) /\
  bounded_object_q_encoded (EL 5 radii)
Proof
  strip_tac
  >> conj_tac
  >- (irule bounded_packed_q_hd_encoded
      >> simp [])
  >> rpt conj_tac
  >> irule bounded_packed_q_el_encoded
  >> simp []
QED

Theorem bounded_packed_q_quadratic_body_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  64 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (subst
        [(«radii»,from_cv (bounded_object_q_cv_list radii));
         («packed»,from_cv (bounded_object_q_cv_list packed))]
        bounded_packed_q_quadratic_body) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_quadratic_suffix6_cv
          0 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed)),refs)
Proof
  strip_tac
  >> imp_res_tac bounded_packed_q_radii6_encoded
  >> simp
       [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_quadratic_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `EL 0 radii`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_boundedPackedObjectLookupEvalTheory.bounded_packed_q_list_lookup_el_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `EL 1 radii`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_boundedPackedObjectLookupEvalTheory.bounded_packed_q_list_lookup_el_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `EL 2 radii`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_boundedPackedObjectLookupEvalTheory.bounded_packed_q_list_lookup_el_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `EL 3 radii`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_boundedPackedObjectLookupEvalTheory.bounded_packed_q_list_lookup_el_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `EL 4 radii`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_boundedPackedObjectLookupEvalTheory.bounded_packed_q_list_lookup_el_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `EL 5 radii`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_boundedPackedObjectLookupEvalTheory.bounded_packed_q_list_lookup_el_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `Num 1`
  >> conj_tac
  >- (simp [compute_execTheory.from_cv_def]
      >> irule
        compute_boundedPackedObjectQuadraticTermAtEvalTheory.bounded_packed_compute_eval_num
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          20 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_suffix6_21,
            compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_zero_eval,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          19 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          18 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          17 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          16 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          15 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          14 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          13 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          12 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          11 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          10 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          9 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          8 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          7 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          6 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          5 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          4 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          3 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          2 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_compute_eval_let_result
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_packed_q_source_quadratic_suffix6_cv
          1 (HD radii) (EL 1 radii) (EL 2 radii) (EL 3 radii) (EL 4 radii) (EL 5 radii) packed`
  >> conj_tac
  >- (bounded_packed_q_irule_quadratic_suffix_result
      >> simp
           [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            listTheory.EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> bounded_packed_q_irule_quadratic_suffix_result
  >> simp
       [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        listTheory.EVERY_EL]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_quadratic_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_encoded packed /\
  LENGTH packed = 21 /\
  65 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_quadratic_abs_upper6»
        [from_cv (bounded_object_q_cv_list radii);
         from_cv (bounded_object_q_cv_list packed)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_quadratic_suffix6_cv
          0 (HD radii) (EL 1 radii) (EL 2 radii)
          (EL 3 radii) (EL 4 radii) (EL 5 radii) packed)),refs)
Proof
  strip_tac
  >> rw
       [compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_quadratic_unfold]
  >> irule bounded_packed_q_quadratic_body_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
