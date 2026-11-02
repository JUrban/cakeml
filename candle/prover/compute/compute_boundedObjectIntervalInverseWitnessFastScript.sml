(*****************************************************************************
 * Compositional exact-object interval inverse witness.
 *
 * The semantic ladder in this theory is intentionally local: primitive
 * rational operations are proved over one shared equation set before the
 * interval and inverse wrappers are admitted.
 *****************************************************************************)
Theory compute_boundedObjectIntervalInverseWitnessFast
Ancestors
  compute_payloadListFast
  compute_boundedPackedObjectPrimitiveMaxEval
Libs
  bossLib preamble intLib

Definition object_inverse_q_den_body_def:
  object_inverse_q_den_body =
    Binop Add (Uop Snd (Var «q»)) (Num 1)
End

Definition object_inverse_q_le_body_def:
  object_inverse_q_le_body =
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

Definition object_inverse_q_min_body_def:
  object_inverse_q_min_body =
    If (App «candle_cv_q_le» [Var «x»;Var «y»])
      (Var «x») (Var «y»)
End

Definition object_inverse_q_max_body_def:
  object_inverse_q_max_body =
    If (App «candle_cv_q_le» [Var «x»;Var «y»])
      (Var «y») (Var «x»)
End

Definition object_inverse_q_min4_body_def:
  object_inverse_q_min4_body =
    App «candle_cv_q_min»
      [App «candle_cv_q_min» [Var «a»;Var «b»];
       App «candle_cv_q_min» [Var «c»;Var «d»]]
End

Definition object_inverse_q_max4_body_def:
  object_inverse_q_max4_body =
    App «candle_cv_q_max»
      [App «candle_cv_q_max» [Var «a»;Var «b»];
       App «candle_cv_q_max» [Var «c»;Var «d»]]
End

Definition object_inverse_q_interval_mul_body_def:
  object_inverse_q_interval_mul_body =
    Pair
      (App «candle_cv_q_min4»
        [App «candle_cv_q_mul» [Uop Fst (Var «i»);Uop Fst (Var «j»)];
         App «candle_cv_q_mul» [Uop Fst (Var «i»);Uop Snd (Var «j»)];
         App «candle_cv_q_mul» [Uop Snd (Var «i»);Uop Fst (Var «j»)];
         App «candle_cv_q_mul» [Uop Snd (Var «i»);Uop Snd (Var «j»)]])
      (App «candle_cv_q_max4»
        [App «candle_cv_q_mul» [Uop Fst (Var «i»);Uop Fst (Var «j»)];
         App «candle_cv_q_mul» [Uop Fst (Var «i»);Uop Snd (Var «j»)];
         App «candle_cv_q_mul» [Uop Snd (Var «i»);Uop Fst (Var «j»)];
         App «candle_cv_q_mul» [Uop Snd (Var «i»);Uop Snd (Var «j»)]])
End

Definition object_inverse_q_interval_neg_body_def:
  object_inverse_q_interval_neg_body =
    Pair
      (App «candle_cv_q_neg» [Uop Snd (Var «x»)])
      (App «candle_cv_q_neg» [Uop Fst (Var «x»)])
End

Definition object_inverse_derivative_body_def:
  object_inverse_derivative_body =
    App «candle_cv_q_interval_neg»
      [App «candle_cv_q_interval_mul»
        [Var «reciprocal»;Var «reciprocal»]]
End

Definition object_inverse_witness_body_def:
  object_inverse_witness_body =
    Binop Eq
      (App «candle_cv_q_packed_object_inverse_derivative»
        [Var «reciprocal»])
      (Var «candidate»)
End

Definition object_inverse_q_den_product_pred_body_def:
  object_inverse_q_den_product_pred_body =
    Binop Add (Binop Add (Var «d1») (Var «d2»))
      (Binop Mul (Var «d1») (Var «d2»))
End

Definition object_inverse_q_zmul_body_def:
  object_inverse_q_zmul_body =
    Pair
      (Binop Add
        (Binop Mul (Uop Fst (Var «x»)) (Uop Fst (Var «y»)))
        (Binop Mul (Uop Snd (Var «x»)) (Uop Snd (Var «y»))))
      (Binop Add
        (Binop Mul (Uop Fst (Var «x»)) (Uop Snd (Var «y»)))
        (Binop Mul (Uop Snd (Var «x»)) (Uop Fst (Var «y»))))
End

Definition object_inverse_q_mul_body_def:
  object_inverse_q_mul_body =
    Pair
      (App «candle_cv_q_zmul» [Uop Fst (Var «x»);Uop Fst (Var «y»)])
      (App «candle_cv_q_den_product_pred»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Definition object_inverse_q_neg_body_def:
  object_inverse_q_neg_body =
    Pair
      (Pair (Uop Snd (Uop Fst (Var «x»)))
        (Uop Fst (Uop Fst (Var «x»))))
      (Uop Snd (Var «x»))
End

Definition bounded_object_interval_inverse_witness_ceqs_def:
  bounded_object_interval_inverse_witness_ceqs :
      (mlstring # (mlstring list # compute_exp)) list =
    [(«candle_cv_q_packed_object_inverse_derivative_witness»,
       ([«reciprocal»;«candidate»],object_inverse_witness_body));
     («candle_cv_q_packed_object_inverse_derivative»,
       ([«reciprocal»],object_inverse_derivative_body));
     («candle_cv_q_interval_neg»,
       ([«x»],object_inverse_q_interval_neg_body));
     («candle_cv_q_interval_mul»,
       ([«i»;«j»],object_inverse_q_interval_mul_body));
     («candle_cv_q_min4»,
       ([«a»;«b»;«c»;«d»],object_inverse_q_min4_body));
     («candle_cv_q_max4»,
       ([«a»;«b»;«c»;«d»],object_inverse_q_max4_body));
     («candle_cv_q_min»,([«x»;«y»],object_inverse_q_min_body));
     («candle_cv_q_max»,([«x»;«y»],object_inverse_q_max_body));
     («candle_cv_q_le»,([«x»;«y»],object_inverse_q_le_body));
     («candle_cv_q_den»,([«q»],object_inverse_q_den_body));
     («candle_cv_q_den_product_pred»,
       ([«d1»;«d2»],object_inverse_q_den_product_pred_body));
     («candle_cv_q_zmul»,([«x»;«y»],object_inverse_q_zmul_body));
     («candle_cv_q_mul»,([«x»;«y»],object_inverse_q_mul_body));
     («candle_cv_q_neg»,([«x»],object_inverse_q_neg_body))]
End

Theorem object_inverse_q_mul_lookup:
  ALOOKUP bounded_object_interval_inverse_witness_ceqs «candle_cv_q_mul» =
    SOME ([«x»;«y»],object_inverse_q_mul_body)
Proof
  EVAL_TAC
QED

Theorem object_inverse_q_neg_lookup:
  ALOOKUP bounded_object_interval_inverse_witness_ceqs «candle_cv_q_neg» =
    SOME ([«x»],object_inverse_q_neg_body)
Proof
  EVAL_TAC
QED

Theorem object_inverse_q_den_lookup:
  ALOOKUP bounded_object_interval_inverse_witness_ceqs «candle_cv_q_den» =
    SOME ([«q»],object_inverse_q_den_body)
Proof
  EVAL_TAC
QED

Theorem object_inverse_q_le_lookup:
  ALOOKUP bounded_object_interval_inverse_witness_ceqs «candle_cv_q_le» =
    SOME ([«x»;«y»],object_inverse_q_le_body)
Proof
  EVAL_TAC
QED

Theorem object_inverse_q_min_lookup:
  ALOOKUP bounded_object_interval_inverse_witness_ceqs «candle_cv_q_min» =
    SOME ([«x»;«y»],object_inverse_q_min_body)
Proof
  EVAL_TAC
QED

Theorem object_inverse_q_max_lookup:
  ALOOKUP bounded_object_interval_inverse_witness_ceqs «candle_cv_q_max» =
    SOME ([«x»;«y»],object_inverse_q_max_body)
Proof
  EVAL_TAC
QED

Theorem object_inverse_q_min4_lookup:
  ALOOKUP bounded_object_interval_inverse_witness_ceqs «candle_cv_q_min4» =
    SOME ([«a»;«b»;«c»;«d»],object_inverse_q_min4_body)
Proof
  EVAL_TAC
QED

Theorem object_inverse_q_max4_lookup:
  ALOOKUP bounded_object_interval_inverse_witness_ceqs «candle_cv_q_max4» =
    SOME ([«a»;«b»;«c»;«d»],object_inverse_q_max4_body)
Proof
  EVAL_TAC
QED

Theorem object_inverse_q_interval_mul_lookup:
  ALOOKUP bounded_object_interval_inverse_witness_ceqs
      «candle_cv_q_interval_mul» =
    SOME ([«i»;«j»],object_inverse_q_interval_mul_body)
Proof
  EVAL_TAC
QED

Theorem object_inverse_q_mul_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_mul» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_mul_cv left right)),refs)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> PairCases_on `fraction'`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> Cases_on `clock`
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        object_inverse_q_mul_lookup,
        object_inverse_q_mul_body_def,
        bounded_object_interval_inverse_witness_ceqs_def,
        object_inverse_q_zmul_body_def,
        object_inverse_q_den_product_pred_body_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_def,
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
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [arithmeticTheory.ADD1,
        arithmeticTheory.LEFT_ADD_DISTRIB,
        arithmeticTheory.RIGHT_ADD_DISTRIB,
        AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem object_inverse_q_neg_eval:
  bounded_object_q_encoded value /\
  1 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_neg» [from_cv value]) (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_neg_cv value)),refs)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> Cases_on `clock`
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        object_inverse_q_neg_lookup,
        object_inverse_q_neg_body_def,
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem object_inverse_compute_eval_list_from_cv:
  !values refs.
    compute_eval_list clock ceqs (MAP from_cv values) refs =
      (M_success (MAP from_cv values),refs)
Proof
  Induct_on `values`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
       ml_monadBaseTheory.st_ex_return_def]
QED

Theorem object_inverse_compute_eval_list4_from_cv:
  compute_eval_list clock ceqs
      [from_cv q1;from_cv q2;from_cv q3;from_cv q4] refs =
    (M_success [from_cv q1;from_cv q2;from_cv q3;from_cv q4],refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem object_inverse_compute_eval_list2_from_cv:
  compute_eval_list clock ceqs [from_cv q1;from_cv q2] refs =
    (M_success [from_cv q1;from_cv q2],refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem object_inverse_compute_eval_app2_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) ==>
  compute_eval clock ceqs
      (App function_name [argument1;argument2]) refs =
    compute_eval clock ceqs
      (App function_name [from_cv result1;from_cv result2]) refs
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
  >> Cases_on `LENGTH q = 2`
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

Theorem object_inverse_compute_eval_app4_argument_results:
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
        [from_cv result1;from_cv result2;from_cv result3;from_cv result4]) refs
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

Theorem object_inverse_compute_eval_pair_results:
  compute_eval clock ceqs left_expression (refs:hol_refs) =
      (M_success (from_cv left),refs) /\
  compute_eval clock ceqs right_expression refs =
      (M_success (from_cv right),refs) ==>
  compute_eval clock ceqs (Pair left_expression right_expression) refs =
    (M_success (from_cv (Pair left right)),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_execTheory.from_cv_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem object_inverse_compute_eval_fst_from_pair:
  compute_eval clock ceqs (Uop Fst (from_cv (Pair left right)))
      (refs:hol_refs) = (M_success (from_cv left),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_execTheory.from_cv_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_fst_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem object_inverse_compute_eval_snd_from_pair:
  compute_eval clock ceqs (Uop Snd (from_cv (Pair left right)))
      (refs:hol_refs) = (M_success (from_cv right),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_execTheory.from_cv_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem object_inverse_q_le_components_eval:
  1 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
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
     object_inverse_q_le_lookup,
     object_inverse_q_le_body_def,
     object_inverse_q_den_lookup,
     object_inverse_q_den_body_def,
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

Theorem object_inverse_q_le_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  1 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_le» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (if bounded_object_q_le_cv left right then Num 1 else Num 0)),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedObjectPrimitiveCompareEvalTheory.bounded_packed_q_encoded_components
  >> gvs []
  >> simp [object_inverse_q_le_components_eval]
  >> simp
       [compute_boundedPackedObjectPrimitiveCompareEvalTheory.bounded_packed_q_le_components_source_order,
        compute_execTheory.from_cv_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem object_inverse_q_min_cv_encoded:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right ==>
  bounded_object_q_encoded (bounded_object_q_min_cv left right)
Proof
  rw
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_min_cv_def]
QED

Theorem object_inverse_q_max_cv_encoded:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right ==>
  bounded_object_q_encoded (bounded_object_q_max_cv left right)
Proof
  rw
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max_cv_def]
QED

Theorem object_inverse_q_min_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_min» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_min_cv left right)),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedObjectPrimitiveCompareEvalTheory.bounded_packed_q_encoded_components
  >> gvs []
  >> Cases_on `clock`
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        object_inverse_q_min_lookup,
        object_inverse_q_min_body_def,
        object_inverse_q_le_lookup,
        object_inverse_q_le_body_def,
        object_inverse_q_den_lookup,
        object_inverse_q_den_body_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_min_cv_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_def,
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
       `positive' * SUC denominator_minus_one +
           negative * SUC denominator_minus_one' <=
         positive * SUC denominator_minus_one' +
           negative' * SUC denominator_minus_one`
  >> fs [arithmeticTheory.ADD1,compute_execTheory.from_cv_def]
  >> intLib.ARITH_TAC
QED

Theorem object_inverse_q_max_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_max» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_max_cv left right)),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedObjectPrimitiveCompareEvalTheory.bounded_packed_q_encoded_components
  >> gvs []
  >> Cases_on `clock`
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        object_inverse_q_max_lookup,
        object_inverse_q_max_body_def,
        object_inverse_q_le_lookup,
        object_inverse_q_le_body_def,
        object_inverse_q_den_lookup,
        object_inverse_q_den_body_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max_cv_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_def,
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
       `positive' * SUC denominator_minus_one +
           negative * SUC denominator_minus_one' <=
         positive * SUC denominator_minus_one' +
           negative' * SUC denominator_minus_one`
  >> fs [arithmeticTheory.ADD1,compute_execTheory.from_cv_def]
  >> intLib.ARITH_TAC
QED

Theorem object_inverse_q_min_results_eval:
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      left_expression (refs:hol_refs) =
    (M_success (from_cv left),refs) /\
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      right_expression refs =
    (M_success (from_cv right),refs) /\
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_min» [left_expression;right_expression]) refs =
    (M_success (from_cv (bounded_object_q_min_cv left right)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_object_interval_inverse_witness_ceqs
          (App «candle_cv_q_min» [from_cv left;from_cv right]) refs`
  >> conj_tac
  >- (irule object_inverse_compute_eval_app2_argument_results
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> simp [object_inverse_q_min_eval]
QED

Theorem object_inverse_q_max_results_eval:
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      left_expression (refs:hol_refs) =
    (M_success (from_cv left),refs) /\
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      right_expression refs =
    (M_success (from_cv right),refs) /\
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_max» [left_expression;right_expression]) refs =
    (M_success (from_cv (bounded_object_q_max_cv left right)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_object_interval_inverse_witness_ceqs
          (App «candle_cv_q_max» [from_cv left;from_cv right]) refs`
  >> conj_tac
  >- (irule object_inverse_compute_eval_app2_argument_results
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> simp [object_inverse_q_max_eval]
QED

Theorem object_inverse_q_mul_results_eval:
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      left_expression (refs:hol_refs) =
    (M_success (from_cv left),refs) /\
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      right_expression refs =
    (M_success (from_cv right),refs) /\
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_mul» [left_expression;right_expression]) refs =
    (M_success (from_cv (bounded_object_q_mul_cv left right)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_object_interval_inverse_witness_ceqs
          (App «candle_cv_q_mul» [from_cv left;from_cv right]) refs`
  >> conj_tac
  >- (irule object_inverse_compute_eval_app2_argument_results
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> simp [object_inverse_q_mul_eval]
QED

Theorem object_inverse_q_min4_cv_encoded:
  bounded_object_q_encoded q1 /\
  bounded_object_q_encoded q2 /\
  bounded_object_q_encoded q3 /\
  bounded_object_q_encoded q4 ==>
  bounded_object_q_encoded (bounded_object_q_min4_cv q1 q2 q3 q4)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_min4_cv_def]
  >> irule object_inverse_q_min_cv_encoded
  >> simp [object_inverse_q_min_cv_encoded]
QED

Theorem object_inverse_q_max4_cv_encoded:
  bounded_object_q_encoded q1 /\
  bounded_object_q_encoded q2 /\
  bounded_object_q_encoded q3 /\
  bounded_object_q_encoded q4 ==>
  bounded_object_q_encoded (bounded_object_q_max4_cv q1 q2 q3 q4)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max4_cv_def]
  >> irule object_inverse_q_max_cv_encoded
  >> simp [object_inverse_q_max_cv_encoded]
QED

Theorem object_inverse_q_min4_eval:
  bounded_object_q_encoded q1 /\
  bounded_object_q_encoded q2 /\
  bounded_object_q_encoded q3 /\
  bounded_object_q_encoded q4 /\
  6 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_min4»
        [from_cv q1;from_cv q2;from_cv q3;from_cv q4])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_min4_cv q1 q2 q3 q4)),refs)
Proof
  strip_tac
  >> Cases_on `clock`
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        object_inverse_q_min4_lookup,
        object_inverse_q_min4_body_def,
        object_inverse_q_min_eval,
        object_inverse_q_min_results_eval,
        object_inverse_q_min_cv_encoded,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_min4_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_execProofTheory.subst_from_cv,
        object_inverse_compute_eval_list_from_cv,
        object_inverse_compute_eval_list4_from_cv,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem object_inverse_q_max4_eval:
  bounded_object_q_encoded q1 /\
  bounded_object_q_encoded q2 /\
  bounded_object_q_encoded q3 /\
  bounded_object_q_encoded q4 /\
  6 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_max4»
        [from_cv q1;from_cv q2;from_cv q3;from_cv q4])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_max4_cv q1 q2 q3 q4)),refs)
Proof
  strip_tac
  >> Cases_on `clock`
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        object_inverse_q_max4_lookup,
        object_inverse_q_max4_body_def,
        object_inverse_q_max_eval,
        object_inverse_q_max_results_eval,
        object_inverse_q_max_cv_encoded,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max4_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_execProofTheory.subst_from_cv,
        object_inverse_compute_eval_list_from_cv,
        object_inverse_compute_eval_list4_from_cv,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem object_inverse_q_min4_results_eval:
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      expression1 (refs:hol_refs) = (M_success (from_cv q1),refs) /\
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      expression2 refs = (M_success (from_cv q2),refs) /\
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      expression3 refs = (M_success (from_cv q3),refs) /\
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      expression4 refs = (M_success (from_cv q4),refs) /\
  bounded_object_q_encoded q1 /\
  bounded_object_q_encoded q2 /\
  bounded_object_q_encoded q3 /\
  bounded_object_q_encoded q4 /\
  6 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_min4»
        [expression1;expression2;expression3;expression4]) refs =
    (M_success (from_cv (bounded_object_q_min4_cv q1 q2 q3 q4)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_object_interval_inverse_witness_ceqs
          (App «candle_cv_q_min4»
            [from_cv q1;from_cv q2;from_cv q3;from_cv q4]) refs`
  >> conj_tac
  >- (irule object_inverse_compute_eval_app4_argument_results
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> simp [object_inverse_q_min4_eval]
QED

Theorem object_inverse_q_max4_results_eval:
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      expression1 (refs:hol_refs) = (M_success (from_cv q1),refs) /\
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      expression2 refs = (M_success (from_cv q2),refs) /\
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      expression3 refs = (M_success (from_cv q3),refs) /\
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      expression4 refs = (M_success (from_cv q4),refs) /\
  bounded_object_q_encoded q1 /\
  bounded_object_q_encoded q2 /\
  bounded_object_q_encoded q3 /\
  bounded_object_q_encoded q4 /\
  6 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_max4»
        [expression1;expression2;expression3;expression4]) refs =
    (M_success (from_cv (bounded_object_q_max4_cv q1 q2 q3 q4)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_object_interval_inverse_witness_ceqs
          (App «candle_cv_q_max4»
            [from_cv q1;from_cv q2;from_cv q3;from_cv q4]) refs`
  >> conj_tac
  >- (irule object_inverse_compute_eval_app4_argument_results
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> simp [object_inverse_q_max4_eval]
QED

Theorem object_inverse_q_interval_mul_cv_encoded:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_mul_cv left right)
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> gvs
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_cv_def]
  >> simp
       [object_inverse_q_min4_cv_encoded,
        object_inverse_q_max4_cv_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded]
QED

Theorem object_inverse_q_interval_mul_unfold:
  0 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_interval_mul» [from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_object_interval_inverse_witness_ceqs
      (subst [(«i»,from_cv left);(«j»,from_cv right)]
        object_inverse_q_interval_mul_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        object_inverse_q_interval_mul_lookup,
        object_inverse_compute_eval_list_from_cv,
        object_inverse_compute_eval_list2_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem object_inverse_q_interval_mul_eval:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right /\
  8 < clock ==>
  compute_eval clock bounded_object_interval_inverse_witness_ceqs
      (App «candle_cv_q_interval_mul» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_mul_cv left right)),refs)
Proof
  rw
    [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> simp [object_inverse_q_interval_mul_unfold]
  >> simp
       [object_inverse_q_interval_mul_body_def,
        compute_evalTheory.subst_def]
  >> simp_tac std_ss
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_cv_def,
        boolTheory.LET_THM,
        compute_execTheory.from_cv_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         object_inverse_compute_eval_pair_results)
  >> conj_tac
  >- (irule object_inverse_q_min4_results_eval
      >> simp
           [object_inverse_q_mul_results_eval,
            SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              object_inverse_compute_eval_fst_from_pair,
            SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              object_inverse_compute_eval_snd_from_pair,
            compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded])
  >> irule object_inverse_q_max4_results_eval
  >> simp
       [object_inverse_q_mul_results_eval,
        SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          object_inverse_compute_eval_fst_from_pair,
        SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          object_inverse_compute_eval_snd_from_pair,
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded]
QED

val _ = export_theory ();
