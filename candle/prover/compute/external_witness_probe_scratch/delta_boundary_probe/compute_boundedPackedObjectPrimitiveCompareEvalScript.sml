(*****************************************************************************
 * Exact-rational comparison semantics for the exported packed entry.
 *****************************************************************************)
Theory compute_boundedPackedObjectPrimitiveCompareEval
Ancestors
  compute_boundedPackedObjectPrimitiveMulEval
Libs
  bossLib preamble intLib

Definition bounded_packed_q_den_body_def:
  bounded_packed_q_den_body =
    Binop Add (Uop Snd (Var «q»)) (Num 1)
End

Definition bounded_packed_q_le_body_def:
  bounded_packed_q_le_body =
    Binop Less
      (Binop Add
        (Binop Mul (Uop Fst (Uop Fst (Var «x»)))
          (App «candle_cv_q_den» [Var «y»]))
        (Binop Mul (Uop Snd (Uop Fst (Var «y»)))
          (App «candle_cv_q_den» [Var «x»])))
      (Binop Add
        (Binop Add
          (Binop Mul (Uop Fst (Uop Fst (Var «y»)))
            (App «candle_cv_q_den» [Var «x»]))
          (Binop Mul (Uop Snd (Uop Fst (Var «x»)))
            (App «candle_cv_q_den» [Var «y»])))
        (Num 1))
End

Theorem bounded_packed_q_den_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_q_den» =
    SOME ([«q»],bounded_packed_q_den_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_le_lookup:
  ALOOKUP bounded_packed_object_entry_ceqs «candle_cv_q_le» =
    SOME ([«x»;«y»],bounded_packed_q_le_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_q_le_components_eval:
  1 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_le»
        [Pair (Pair (Num left_positive) (Num left_negative))
           (Num left_denominator_minus_one);
         Pair (Pair (Num right_positive) (Num right_negative))
           (Num right_denominator_minus_one)])
      (refs:hol_refs) =
    (M_success
      (Num
        (if
          left_positive * SUC right_denominator_minus_one +
              right_negative * SUC left_denominator_minus_one <=
            right_positive * SUC left_denominator_minus_one +
              left_negative * SUC right_denominator_minus_one
         then 1 else 0)),refs)
Proof
  Cases_on `clock`
  >> simp
    [Once compute_evalTheory.compute_eval_def,
     bounded_packed_q_le_lookup,
     bounded_packed_q_le_body_def,
     bounded_packed_q_den_lookup,
     bounded_packed_q_den_body_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_evalTheory.option_def,
     compute_evalTheory.check_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_reln_def,
     compute_evalTheory.do_arith_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on
       `left_positive * SUC right_denominator_minus_one +
           right_negative * SUC left_denominator_minus_one <=
         right_positive * SUC left_denominator_minus_one +
           left_negative * SUC right_denominator_minus_one`
  >> fs [arithmeticTheory.ADD1]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_le_components:
  bounded_object_q_le_cv
      (Pair (Pair (Num left_positive) (Num left_negative))
        (Num left_denominator_minus_one))
      (Pair (Pair (Num right_positive) (Num right_negative))
        (Num right_denominator_minus_one)) <=>
    left_positive * SUC right_denominator_minus_one +
        right_negative * SUC left_denominator_minus_one <=
      right_positive * SUC left_denominator_minus_one +
        left_negative * SUC right_denominator_minus_one
Proof
  simp
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_def]
QED

Theorem bounded_packed_q_le_components_source_order:
  bounded_object_q_le_cv
      (Pair (Pair (Num left_positive) (Num left_negative))
        (Num left_denominator_minus_one))
      (Pair (Pair (Num right_positive) (Num right_negative))
        (Num right_denominator_minus_one)) <=>
    right_negative * SUC left_denominator_minus_one +
        left_positive * SUC right_denominator_minus_one <=
      left_negative * SUC right_denominator_minus_one +
        right_positive * SUC left_denominator_minus_one
Proof
  simp
    [bounded_packed_q_le_components,
     AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem bounded_packed_q_encoded_components:
  bounded_object_q_encoded value ==>
  ?positive negative denominator_minus_one.
    value =
      Pair (Pair (Num positive) (Num negative))
        (Num denominator_minus_one)
Proof
  rw
    [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
QED

Theorem bounded_packed_q_le_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  1 < clock ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_le» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (if bounded_object_q_le_cv left right then Num 1 else Num 0)),refs)
Proof
  strip_tac
  >> imp_res_tac bounded_packed_q_encoded_components
  >> gvs []
  >> simp [bounded_packed_q_le_components_eval]
  >> simp
       [bounded_packed_q_le_components_source_order,
        compute_execTheory.from_cv_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
