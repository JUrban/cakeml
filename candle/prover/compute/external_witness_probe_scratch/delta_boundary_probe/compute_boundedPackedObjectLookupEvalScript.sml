(*****************************************************************************
 * Canonical in-range list lookups used by the exported packed quadratic.
 *****************************************************************************)
Theory compute_boundedPackedObjectLookupEval
Ancestors
  compute_boundedPackedObjectDotRecursiveEval
Libs
  bossLib preamble intLib

Definition bounded_packed_q_list_lookup_body_def:
  bounded_packed_q_list_lookup_body =
    If (Uop Ispair (Var «n»))
      (App «candle_cv_q_zero» [])
      (If (Uop Ispair (Var «items»))
        (If (Binop Eq (Var «n») (Num 0))
          (Uop Fst (Var «items»))
          (App «candle_cv_q_list_lookup»
            [Binop Sub (Var «n») (Num 1);Uop Snd (Var «items»)]))
        (App «candle_cv_q_zero» []))
End

Definition bounded_packed_q_interval_lookup_body_def:
  bounded_packed_q_interval_lookup_body =
    If (Uop Ispair (Var «n»))
      (App «candle_cv_q_zero_interval» [])
      (If (Uop Ispair (Var «env»))
        (If (Binop Eq (Var «n») (Num 0))
          (Uop Fst (Var «env»))
          (App «candle_cv_q_interval_lookup»
            [Binop Sub (Var «n») (Num 1);Uop Snd (Var «env»)]))
        (App «candle_cv_q_zero_interval» []))
End

Theorem bounded_packed_q_list_lookup_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_q_list_lookup» =
    SOME ([«n»;«items»],bounded_packed_q_list_lookup_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_interval_lookup_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_q_interval_lookup» =
    SOME ([«n»;«env»],bounded_packed_q_interval_lookup_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_list_lookup_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_list_lookup» [from_cv n;from_cv items])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst [(«n»,from_cv n);(«items»,from_cv items)]
        bounded_packed_q_list_lookup_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectDotEvalTheory.bounded_packed_compute_eval_literal_app2
  >> simp [bounded_packed_q_list_lookup_lookup]
QED

Theorem bounded_packed_q_interval_lookup_unfold:
  0 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_interval_lookup» [from_cv n;from_cv items])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (subst [(«n»,from_cv n);(«env»,from_cv items)]
        bounded_packed_q_interval_lookup_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedPackedObjectDotEvalTheory.bounded_packed_compute_eval_literal_app2
  >> simp [bounded_packed_q_interval_lookup_lookup]
QED

Theorem bounded_packed_q_list_lookup_head_eval:
  1 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_list_lookup»
        [from_cv (Num 0);from_cv (Pair item items)])
      (refs:hol_refs) =
    (M_success (from_cv item),refs)
Proof
  strip_tac
  >> simp [bounded_packed_q_list_lookup_unfold]
  >> simp
       [bounded_packed_q_list_lookup_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_list_lookup_tail_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (App «candle_cv_q_list_lookup»
        [from_cv (Num n);from_cv items]) (refs:hol_refs) = result ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_list_lookup»
        [from_cv (Num (SUC n));from_cv (Pair item items)]) refs =
    result
Proof
  strip_tac
  >> simp [bounded_packed_q_list_lookup_unfold]
  >> fs
       [bounded_packed_q_list_lookup_body_def,
        bounded_packed_q_list_lookup_unfold,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> gvs []
QED

Theorem bounded_packed_q_interval_lookup_head_eval:
  1 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_interval_lookup»
        [from_cv (Num 0);from_cv (Pair item items)])
      (refs:hol_refs) =
    (M_success (from_cv item),refs)
Proof
  strip_tac
  >> simp [bounded_packed_q_interval_lookup_unfold]
  >> simp
       [bounded_packed_q_interval_lookup_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_q_interval_lookup_tail_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_packed_object_entry_ceqs
      (App «candle_cv_q_interval_lookup»
        [from_cv (Num n);from_cv items]) (refs:hol_refs) = result ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_interval_lookup»
        [from_cv (Num (SUC n));from_cv (Pair item items)]) refs =
    result
Proof
  strip_tac
  >> simp [bounded_packed_q_interval_lookup_unfold]
  >> fs
       [bounded_packed_q_interval_lookup_body_def,
        bounded_packed_q_interval_lookup_unfold,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> gvs []
QED

Theorem bounded_packed_q_list_lookup_el_eval:
  !n items clock refs.
    n < LENGTH items /\ n + 2 < clock ==>
    compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_list_lookup»
          [from_cv (Num n);
           from_cv (bounded_object_q_cv_list items)]) (refs:hol_refs) =
      (M_success (from_cv (EL n items)),refs)
Proof
  Induct_on `n`
  >> Cases_on `items`
  >> simp []
  >- (strip_tac
      >> rw
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_packed_q_list_lookup_head_eval)
      >> intLib.ARITH_TAC)
  >> strip_tac
  >> rw
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_q_list_lookup_tail_eval)
  >> conj_tac
  >- intLib.ARITH_TAC
  >> first_x_assum (qspecl_then [`t`,`clock - 1`,`refs`] mp_tac)
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_interval_lookup_el_eval:
  !n items clock refs.
    n < LENGTH items /\ n + 2 < clock ==>
    compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_interval_lookup»
          [from_cv (Num n);
           from_cv (bounded_object_q_cv_list items)]) (refs:hol_refs) =
      (M_success (from_cv (EL n items)),refs)
Proof
  Induct_on `n`
  >> Cases_on `items`
  >> simp []
  >- (strip_tac
      >> rw
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_packed_q_interval_lookup_head_eval)
      >> intLib.ARITH_TAC)
  >> strip_tac
  >> rw
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_q_interval_lookup_tail_eval)
  >> conj_tac
  >- intLib.ARITH_TAC
  >> first_x_assum (qspecl_then [`t`,`clock - 1`,`refs`] mp_tac)
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
