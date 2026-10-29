(*****************************************************************************
 * Indexed exact source-faithful packed quadratic contribution.
 *****************************************************************************)
Theory compute_boundedPackedObjectQuadraticTermAtEval
Ancestors
  compute_boundedPackedObjectQuadraticTermEval
Libs
  bossLib preamble intLib

Definition bounded_packed_q_quadratic_term_at_body_def:
  bounded_packed_q_quadratic_term_at_body =
    App «candle_cv_q_packed_quadratic_term»
      [Var «left»;Var «right»;Var «twice»;
       App «candle_cv_q_interval_lookup» [Var «i»;Var «packed»]]
End

Theorem bounded_packed_q_quadratic_term_at_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs
      «candle_cv_q_packed_quadratic_term_at» =
    SOME
      ([«packed»;«i»;«left»;«right»;«twice»],
       bounded_packed_q_quadratic_term_at_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_compute_eval_literal_app5:
  0 < clock /\
  ALOOKUP ceqs function_name =
      SOME ([name1;name2;name3;name4;name5],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv value1;from_cv value2;from_cv value3;from_cv value4;
         from_cv value5]) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv value1);(name2,from_cv value2);
         (name3,from_cv value3);(name4,from_cv value4);
         (name5,from_cv value5)] body) refs
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

Theorem bounded_packed_q_quadratic_term_at_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_quadratic_term_at»
        [from_cv packed;from_cv index;from_cv left;from_cv right;
         from_cv twice]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst
        [(«packed»,from_cv packed);(«i»,from_cv index);
         («left»,from_cv left);(«right»,from_cv right);
         («twice»,from_cv twice)]
        bounded_packed_q_quadratic_term_at_body) refs
Proof
  strip_tac
  >> irule bounded_packed_compute_eval_literal_app5
  >> simp [bounded_packed_q_quadratic_term_at_lookup]
QED

Theorem bounded_packed_compute_eval_app4_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) /\
  compute_eval clock ceqs argument4 refs =
      (M_success (from_cv result4),refs) ==>
  compute_eval clock ceqs
      (App function_name [argument1;argument2;argument3;argument4]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3;from_cv result4])
      refs
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
  >> Cases_on `LENGTH q = 4`
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

Theorem bounded_packed_compute_eval_num:
  0 < clock ==>
  compute_eval clock ceqs (Num n) (refs:hol_refs) =
    (M_success (Num n),refs)
Proof
  Cases_on `clock`
  >> simp
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_quadratic_term_at_body_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  EVERY bounded_packed_q_interval_encoded packed /\
  index < LENGTH packed /\
  index + 9 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_quadratic_term»
        [from_cv left;from_cv right;
         from_cv (Num (if twice then 1 else 0));
         App «candle_cv_q_interval_lookup»
           [from_cv (Num index);
            from_cv (bounded_object_q_cv_list packed)]]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_quadratic_term_cv
          left right twice (EL index packed))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_packed_object_entry_ceqs
          (App «candle_cv_q_packed_quadratic_term»
            [from_cv left;from_cv right;
             from_cv (Num (if twice then 1 else 0));
             from_cv (EL index packed)]) refs`
  >> conj_tac
  >- (irule bounded_packed_compute_eval_app4_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_boundedPackedObjectLookupEvalTheory.bounded_packed_q_interval_lookup_el_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_q_quadratic_term_eval
  >> fs [listTheory.EVERY_EL]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_quadratic_term_at_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  EVERY bounded_packed_q_interval_encoded packed /\
  index < LENGTH packed /\
  index + 10 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_quadratic_term_at»
        [from_cv (bounded_object_q_cv_list packed);from_cv (Num index);
         from_cv left;from_cv right;
         from_cv (Num (if twice then 1 else 0))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_packed_q_source_quadratic_term_cv
          left right twice (EL index packed))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1) bounded_packed_object_entry_ceqs
          (subst
            [(«packed»,from_cv (bounded_object_q_cv_list packed));
             («i»,from_cv (Num index));(«left»,from_cv left);
             («right»,from_cv right);
             («twice»,from_cv (Num (if twice then 1 else 0)))]
            bounded_packed_q_quadratic_term_at_body) refs`
  >> conj_tac
  >- (irule bounded_packed_q_quadratic_term_at_unfold
      >> intLib.ARITH_TAC)
  >> simp
       [bounded_packed_q_quadratic_term_at_body_def,
        compute_evalTheory.subst_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_q_quadratic_term_at_body_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
