(*****************************************************************************
 * Production evaluation of positive exact-rational reciprocals.
 *
 * The reciprocal certificate used by the genuine source-6 square-root step
 * is positive.  Prove the concrete q_inv representation and interval wrapper
 * once before reasoning about the surrounding boolean certificate.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInversePrimitiveEval
Ancestors
  compute_boundedCase16594ObjectSqrtCertificateExactEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_q_den_body_def:
  bounded_case16594_object_q_den_body =
    Binop Add (Uop Snd (Var «q»)) (Num 1)
End

Definition bounded_case16594_object_q_inv_body_def:
  bounded_case16594_object_q_inv_body =
    If
      (Binop Less
        (Uop Fst (Uop Fst (Var «q»)))
        (Uop Snd (Uop Fst (Var «q»))))
      (Pair
        (Pair (Num 0) (App «candle_cv_q_den» [Var «q»]))
        (Binop Sub
          (Binop Sub
            (Uop Snd (Uop Fst (Var «q»)))
            (Uop Fst (Uop Fst (Var «q»))))
          (Num 1)))
      (If
        (Binop Less
          (Uop Snd (Uop Fst (Var «q»)))
          (Uop Fst (Uop Fst (Var «q»))))
        (Pair
          (Pair (App «candle_cv_q_den» [Var «q»]) (Num 0))
          (Binop Sub
            (Binop Sub
              (Uop Fst (Uop Fst (Var «q»)))
              (Uop Snd (Uop Fst (Var «q»))))
            (Num 1)))
        (Pair (Pair (Num 0) (Num 0)) (Num 0)))
End

Definition bounded_case16594_object_q_interval_inv_body_def:
  bounded_case16594_object_q_interval_inv_body =
    Pair
      (App «candle_cv_q_inv» [Uop Snd (Var «i»)])
      (App «candle_cv_q_inv» [Uop Fst (Var «i»)])
End

Definition bounded_case16594_object_q_positive_inv_cv_def:
  bounded_case16594_object_q_positive_inv_cv
      (Pair (Pair (Num positive) (Num negative))
        (Num denominator_minus_one)) =
    Pair (Pair (Num (SUC denominator_minus_one)) (Num 0))
      (Num (positive - negative - 1)) /\
  bounded_case16594_object_q_positive_inv_cv _ = Num 0
End

Definition bounded_case16594_object_q_positive_interval_inv_cv_def:
  bounded_case16594_object_q_positive_interval_inv_cv (Pair lower upper) =
    Pair
      (bounded_case16594_object_q_positive_inv_cv upper)
      (bounded_case16594_object_q_positive_inv_cv lower) /\
  bounded_case16594_object_q_positive_interval_inv_cv _ = Num 0
End

Theorem bounded_case16594_object_q_den_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_den» =
    SOME ([«q»],bounded_case16594_object_q_den_body)
Proof
  rw [bounded_case16594_object_q_den_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_q_inv_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_inv» =
    SOME ([«q»],bounded_case16594_object_q_inv_body)
Proof
  rw [bounded_case16594_object_q_inv_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_q_interval_inv_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_interval_inv» =
    SOME ([«i»],bounded_case16594_object_q_interval_inv_body)
Proof
  rw [bounded_case16594_object_q_interval_inv_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_q_positive_inv_cv_decodes:
  bounded_object_q_ints value = SOME (numerator,denominator) /\
  0 < numerator ==>
  bounded_object_q_ints
      (bounded_case16594_object_q_positive_inv_cv value) =
    SOME (denominator,numerator)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> `negative < positive` by intLib.ARITH_TAC
  >> `SUC (positive - negative - 1) = positive - negative` by
       intLib.ARITH_TAC
  >> simp
       [bounded_case16594_object_q_positive_inv_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        integerTheory.INT_SUB]
QED

Theorem bounded_case16594_object_q_positive_inv_cv_encoded:
  bounded_object_q_ints value = SOME (numerator,denominator) /\
  0 < numerator ==>
  bounded_object_q_encoded
    (bounded_case16594_object_q_positive_inv_cv value)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> qexists_tac `(denominator,numerator)`
  >> irule bounded_case16594_object_q_positive_inv_cv_decodes
  >> simp []
QED

Theorem bounded_case16594_object_q_inv_positive_eval:
  bounded_object_q_ints value = SOME (numerator,denominator) /\
  0 < numerator /\
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_inv» [from_cv value]) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_case16594_object_q_positive_inv_cv value)),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> `negative < positive` by intLib.ARITH_TAC
  >> Cases_on `clock`
  >> gvs []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_case16594_object_q_inv_lookup,
        bounded_case16594_object_q_inv_body_def,
        bounded_case16594_object_q_den_lookup,
        bounded_case16594_object_q_den_body_def,
        bounded_case16594_object_q_positive_inv_cv_def,
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
QED

Theorem bounded_case16594_object_q_interval_inv_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv» [from_cv input]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«i»,from_cv input)]
        bounded_case16594_object_q_interval_inv_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_q_interval_inv_lookup
QED

Theorem bounded_case16594_object_q_inv_positive_argument_result:
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      argument (refs:hol_refs) = (M_success (from_cv value),refs) /\
  bounded_object_q_ints value = SOME (numerator,denominator) /\
  0 < numerator /\
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_inv» [argument]) refs =
    (M_success
      (from_cv (bounded_case16594_object_q_positive_inv_cv value)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_inv» [from_cv value]) refs`
  >> conj_tac
  >- (irule
        compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_compute_eval_app1_argument_result
      >> simp [])
  >> simp [bounded_case16594_object_q_inv_positive_eval]
QED

Theorem bounded_case16594_object_q_interval_inv_positive_eval:
  bounded_object_q_ints input_lower =
      SOME (input_lower_numerator,input_lower_denominator) /\
  bounded_object_q_ints input_upper =
      SOME (input_upper_numerator,input_upper_denominator) /\
  0 < input_lower_numerator /\
  0 < input_upper_numerator /\
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv»
        [from_cv (Pair input_lower input_upper)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_q_positive_interval_inv_cv
          (Pair input_lower input_upper))),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_q_interval_inv_unfold]
  >> simp
       [bounded_case16594_object_q_interval_inv_body_def,
        compute_evalTheory.subst_def,
        bounded_case16594_object_q_positive_interval_inv_cv_def,
        compute_execTheory.from_cv_def]
  >> irule
       (REWRITE_RULE
         [compute_execTheory.from_cv_def]
         compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_compute_eval_pair_results)
  >> conj_tac
  >- (irule bounded_case16594_object_q_inv_positive_argument_result
      >> simp
           [SIMP_RULE std_ss
              [compute_execTheory.from_cv_def]
              compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_compute_eval_snd_from_pair]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_q_inv_positive_argument_result
  >> simp
       [SIMP_RULE std_ss
          [compute_execTheory.from_cv_def]
          compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_compute_eval_fst_from_pair]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
