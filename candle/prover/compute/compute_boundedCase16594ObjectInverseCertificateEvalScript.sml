(*****************************************************************************
 * Generic production evaluation of positive reciprocal certificates.
 *
 * This layer composes the already-proved positive interval reciprocal with
 * the source-faithful not-zero and enclosure guards.  The following theory
 * connects the exact mathematical certificate contract to these conditions.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseCertificateEval
Ancestors
  compute_boundedCase16594ObjectInversePrimitiveEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_q_zero_body_def:
  bounded_case16594_object_q_zero_body : compute_exp =
    Pair (Pair (Num 0) (Num 0)) (Num 0)
End

Definition bounded_case16594_object_q_interval_not_zero_body_def:
  bounded_case16594_object_q_interval_not_zero_body =
    If
      (App «candle_cv_q_le»
        [Uop Fst (Var «i»);App «candle_cv_q_zero» []])
      (If
        (App «candle_cv_q_le»
          [App «candle_cv_q_zero» [];Uop Snd (Var «i»)])
        (Num 0) (Num 1))
      (Num 1)
End

Definition bounded_case16594_object_q_interval_encloses_body_def:
  bounded_case16594_object_q_interval_encloses_body =
    App «candle_cv_bool_and»
      [App «candle_cv_q_le»
        [Uop Fst (Var «outer»);Uop Fst (Var «inner»)];
       App «candle_cv_q_le»
        [Uop Snd (Var «inner»);Uop Snd (Var «outer»)]]
End

Definition bounded_case16594_object_q_interval_inv_certificate_body_def:
  bounded_case16594_object_q_interval_inv_certificate_body =
    App «candle_cv_bool_and»
      [App «candle_cv_q_interval_not_zero» [Var «input»];
       App «candle_cv_q_interval_encloses»
        [Var «output»;
         App «candle_cv_q_interval_inv» [Var «input»]]]
End

Theorem bounded_case16594_object_q_zero_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_zero» =
    SOME ([],bounded_case16594_object_q_zero_body)
Proof
  rw [bounded_case16594_object_q_zero_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_q_interval_not_zero_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_interval_not_zero» =
    SOME ([«i»],bounded_case16594_object_q_interval_not_zero_body)
Proof
  rw [bounded_case16594_object_q_interval_not_zero_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_q_interval_encloses_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_interval_encloses» =
    SOME
      ([«outer»;«inner»],
       bounded_case16594_object_q_interval_encloses_body)
Proof
  rw [bounded_case16594_object_q_interval_encloses_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_q_interval_inv_certificate_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_interval_inv_certificate» =
    SOME
      ([«input»;«output»],
       bounded_case16594_object_q_interval_inv_certificate_body)
Proof
  rw [bounded_case16594_object_q_interval_inv_certificate_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_q_zero_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_zero» []) (refs:hol_refs) =
    (M_success (from_cv bounded_object_q_zero_cv),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app0
  >> simp
       [bounded_case16594_object_q_zero_lookup,
        bounded_case16594_object_q_zero_body_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
        compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_q_le_false_argument_results:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  ~bounded_object_q_le_cv left right /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      left_expression (refs:hol_refs) = (M_success (from_cv left),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      right_expression refs = (M_success (from_cv right),refs) /\
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_le» [left_expression;right_expression]) refs =
    (M_success (Num 0),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_le» [from_cv left;from_cv right]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [])
  >> simp
       [compute_boundedCase16594ObjectSqrtCertificateEvalTheory.bounded_case16594_object_q_le_eval]
QED

Theorem bounded_case16594_object_bool_and_true_argument_results:
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      left_expression (refs:hol_refs) = (M_success (Num 1),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      right_expression refs = (M_success (Num 1),refs) /\
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_bool_and»
        [left_expression;right_expression]) refs =
    (M_success (Num 1),refs)
Proof
  Cases_on `clock`
  >- simp []
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_boundedCase16594ObjectMulCompleteEvalTheory.bounded_case16594_object_bool_and_lookup,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.subst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_q_positive_not_le_zero:
  bounded_object_q_ints value = SOME (numerator,denominator) /\
  0 < numerator ==>
  ~bounded_object_q_le_cv value bounded_object_q_zero_cv
Proof
  strip_tac
  >> `0 < denominator` by
       metis_tac
         [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >> `bounded_object_q_le_cv value bounded_object_q_zero_cv <=>
      bounded_int_fraction_le (numerator,denominator) (0,1)` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct
        >> simp [])
  >> fs
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_q_interval_not_zero_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_not_zero» [from_cv input])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«i»,from_cv input)]
        bounded_case16594_object_q_interval_not_zero_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_q_interval_not_zero_lookup
QED

Theorem bounded_case16594_object_q_interval_not_zero_positive_eval:
  bounded_object_q_ints input_lower =
      SOME (input_lower_numerator,input_lower_denominator) /\
  0 < input_lower_numerator /\
  bounded_object_q_encoded input_upper /\
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_not_zero»
        [from_cv (Pair input_lower input_upper)]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_q_interval_not_zero_unfold]
  >> simp
       [bounded_case16594_object_q_interval_not_zero_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> irule
       compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_if_false_result
  >> conj_tac
  >- (irule bounded_case16594_object_q_le_false_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> qexists_tac `input_lower`
      >> qexists_tac `bounded_object_q_zero_cv`
      >> simp
           [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def,
            compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded,
            bounded_case16594_object_q_positive_not_le_zero,
            SIMP_RULE std_ss
              [compute_execTheory.from_cv_def]
              compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_compute_eval_fst_from_pair,
            bounded_case16594_object_q_zero_eval]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_q_interval_encloses_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_encloses»
        [from_cv outer;from_cv inner]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«outer»,from_cv outer);(«inner»,from_cv inner)]
        bounded_case16594_object_q_interval_encloses_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_q_interval_encloses_lookup
QED

Theorem bounded_case16594_object_q_interval_encloses_conditions_eval:
  bounded_object_q_encoded outer_lower /\
  bounded_object_q_encoded outer_upper /\
  bounded_object_q_encoded inner_lower /\
  bounded_object_q_encoded inner_upper /\
  bounded_object_q_le_cv outer_lower inner_lower /\
  bounded_object_q_le_cv inner_upper outer_upper /\
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_encloses»
        [from_cv (Pair outer_lower outer_upper);
         from_cv (Pair inner_lower inner_upper)]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_q_interval_encloses_unfold]
  >> simp
       [bounded_case16594_object_q_interval_encloses_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> irule bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac
  >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectSqrtCertificateEvalTheory.bounded_case16594_object_q_le_true_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> qexists_tac `outer_lower`
      >> qexists_tac `inner_lower`
      >> simp
           [SIMP_RULE std_ss
              [compute_execTheory.from_cv_def]
              compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_compute_eval_fst_from_pair])
  >> irule
       compute_boundedCase16594ObjectSqrtCertificateEvalTheory.bounded_case16594_object_q_le_true_argument_results
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `inner_upper`
  >> qexists_tac `outer_upper`
  >> simp
       [SIMP_RULE std_ss
          [compute_execTheory.from_cv_def]
          compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_compute_eval_snd_from_pair]
QED

Theorem bounded_case16594_object_q_interval_encloses_argument_results:
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      outer_expression (refs:hol_refs) =
      (M_success (from_cv (Pair outer_lower outer_upper)),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      inner_expression refs =
      (M_success (from_cv (Pair inner_lower inner_upper)),refs) /\
  bounded_object_q_encoded outer_lower /\
  bounded_object_q_encoded outer_upper /\
  bounded_object_q_encoded inner_lower /\
  bounded_object_q_encoded inner_upper /\
  bounded_object_q_le_cv outer_lower inner_lower /\
  bounded_object_q_le_cv inner_upper outer_upper /\
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_encloses»
        [outer_expression;inner_expression]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_encloses»
            [from_cv (Pair outer_lower outer_upper);
             from_cv (Pair inner_lower inner_upper)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [])
  >> irule bounded_case16594_object_q_interval_encloses_conditions_eval
  >> simp []
QED

Theorem bounded_case16594_object_q_interval_inv_certificate_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [from_cv input;from_cv output]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«input»,from_cv input);(«output»,from_cv output)]
        bounded_case16594_object_q_interval_inv_certificate_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_q_interval_inv_certificate_lookup
QED

Theorem bounded_case16594_object_q_interval_inv_certificate_conditions_eval:
  bounded_object_q_ints input_lower =
      SOME (input_lower_numerator,input_lower_denominator) /\
  bounded_object_q_ints input_upper =
      SOME (input_upper_numerator,input_upper_denominator) /\
  bounded_object_q_encoded output_lower /\
  bounded_object_q_encoded output_upper /\
  0 < input_lower_numerator /\
  0 < input_upper_numerator /\
  bounded_object_q_le_cv output_lower
    (bounded_case16594_object_q_positive_inv_cv input_upper) /\
  bounded_object_q_le_cv
    (bounded_case16594_object_q_positive_inv_cv input_lower) output_upper /\
  4 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [from_cv (Pair input_lower input_upper);
         from_cv (Pair output_lower output_upper)]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_q_interval_inv_certificate_unfold]
  >> simp
       [bounded_case16594_object_q_interval_inv_certificate_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> irule bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac
  >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss
          [compute_execTheory.from_cv_def]
          bounded_case16594_object_q_interval_not_zero_positive_eval)
      >> simp
           [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_q_interval_encloses_argument_results
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_object_q_positive_inv_cv input_upper`
  >> qexists_tac `bounded_case16594_object_q_positive_inv_cv input_lower`
  >> qexists_tac `output_lower`
  >> qexists_tac `output_upper`
  >> simp
       [bounded_case16594_object_q_positive_inv_cv_encoded,
        bounded_case16594_object_q_positive_interval_inv_cv_def,
        compute_execTheory.from_cv_def]
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss
          [bounded_case16594_object_q_positive_interval_inv_cv_def,
           compute_execTheory.from_cv_def]
          bounded_case16594_object_q_interval_inv_positive_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
