(*****************************************************************************
 * Generic production evaluation of the exact-rational square-root
 * certificate.  This layer proves the six executable comparisons once;
 * the genuine source-6 packet instantiates it through the exact certificate
 * contract in the following bridge layer.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSqrtCertificateEval
Ancestors
  compute_boundedCase16594ObjectSqrtStateEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_q_interval_sqrt_certificate_body_def:
  bounded_case16594_object_q_interval_sqrt_certificate_body =
    If
      (App «candle_cv_q_le»
        [Pair (Pair (Num 0) (Num 0)) (Num 0);
         Uop Fst (Var «input»)])
      (If
        (App «candle_cv_q_le»
          [Uop Fst (Var «input»);Uop Snd (Var «input»)])
        (If
          (App «candle_cv_q_le»
            [Pair (Pair (Num 0) (Num 0)) (Num 0);
             Uop Fst (Var «output»)])
          (If
            (App «candle_cv_q_le»
              [Uop Fst (Var «output»);Uop Snd (Var «output»)])
            (If
              (App «candle_cv_q_le»
                [App «candle_cv_q_mul»
                   [Uop Fst (Var «output»);Uop Fst (Var «output»)];
                 Uop Fst (Var «input»)])
              (If
                (App «candle_cv_q_le»
                  [Uop Snd (Var «input»);
                   App «candle_cv_q_mul»
                     [Uop Snd (Var «output»);
                      Uop Snd (Var «output»)]])
                (Num 1) (Num 0))
              (Num 0))
            (Num 0))
          (Num 0))
        (Num 0))
      (Num 0)
End

Theorem bounded_case16594_object_q_interval_sqrt_certificate_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_interval_sqrt_certificate» =
    SOME
      ([«input»;«output»],
       bounded_case16594_object_q_interval_sqrt_certificate_body)
Proof
  rw [bounded_case16594_object_q_interval_sqrt_certificate_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_q_interval_sqrt_certificate_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [from_cv input;from_cv output]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«input»,from_cv input);(«output»,from_cv output)]
        bounded_case16594_object_q_interval_sqrt_certificate_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_q_interval_sqrt_certificate_lookup
QED

Theorem bounded_case16594_object_q_le_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_le» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (if bounded_object_q_le_cv left right then Num 1 else Num 0)),refs)
Proof
  strip_tac
  >> `compute_exp_uses_only
        bounded_case16594_object_inverse_core
        (App «candle_cv_q_le» [from_cv left;from_cv right])` by
       (simp
          [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
           compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_inverse_core_def,
           compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_uses_only_from_cv]
        >> EVAL_TAC)
  >> `compute_eval clock bounded_object_interval_inverse_witness_ceqs
        (App «candle_cv_q_le» [from_cv left;from_cv right])
        (refs:hol_refs) =
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_le» [from_cv left;from_cv right]) refs` by
       metis_tac
         [compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_inverse_core_eval_cong]
  >> metis_tac
       [compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_q_le_eval]
QED

Theorem bounded_case16594_object_q_mul_eval:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  3 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_mul» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_mul_cv left right)),refs)
Proof
  strip_tac
  >> `compute_exp_uses_only
        bounded_case16594_object_inverse_core
        (App «candle_cv_q_mul» [from_cv left;from_cv right])` by
       (simp
          [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
           compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_inverse_core_def,
           compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_uses_only_from_cv]
        >> EVAL_TAC)
  >> `compute_eval clock bounded_object_interval_inverse_witness_ceqs
        (App «candle_cv_q_mul» [from_cv left;from_cv right])
        (refs:hol_refs) =
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_mul» [from_cv left;from_cv right]) refs` by
       metis_tac
         [compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_inverse_core_eval_cong]
  >> metis_tac
       [compute_boundedObjectIntervalInverseWitnessFastTheory.object_inverse_q_mul_eval]
QED

Theorem bounded_case16594_object_q_le_true_argument_results:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  bounded_object_q_le_cv left right /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      left_expression (refs:hol_refs) = (M_success (from_cv left),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      right_expression refs = (M_success (from_cv right),refs) /\
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_le» [left_expression;right_expression]) refs =
    (M_success (Num 1),refs)
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
  >> simp [bounded_case16594_object_q_le_eval]
QED

Theorem bounded_case16594_object_q_mul_argument_results:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      left_expression (refs:hol_refs) = (M_success (from_cv left),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      right_expression refs = (M_success (from_cv right),refs) /\
  3 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_mul» [left_expression;right_expression]) refs =
    (M_success (from_cv (bounded_object_q_mul_cv left right)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_mul» [from_cv left;from_cv right]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [])
  >> irule bounded_case16594_object_q_mul_eval
  >> simp []
QED

Theorem bounded_case16594_compute_eval_six_if_success:
  compute_eval clock ceqs condition1 (refs:hol_refs) =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs condition2 refs =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs condition3 refs =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs condition4 refs =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs condition5 refs =
      (M_success (Num 1),refs) /\
  compute_eval clock ceqs condition6 refs =
      (M_success (Num 1),refs) ==>
  compute_eval clock ceqs
      (If condition1
        (If condition2
          (If condition3
            (If condition4
              (If condition5
                (If condition6 (Num 1) (Num 0))
                (Num 0))
              (Num 0))
            (Num 0))
          (Num 0))
        (Num 0)) refs =
    (M_success (Num 1),refs)
Proof
  rpt strip_tac
  >> fs
       [compute_boundedPackedObjectFinishEvalTheory.bounded_packed_compute_eval_if_true_result,
        compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_q_interval_sqrt_certificate_conditions_eval:
  bounded_object_q_encoded input_lower /\
  bounded_object_q_encoded input_upper /\
  bounded_object_q_encoded output_lower /\
  bounded_object_q_encoded output_upper /\
  bounded_object_q_le_cv bounded_object_q_zero_cv input_lower /\
  bounded_object_q_le_cv input_lower input_upper /\
  bounded_object_q_le_cv bounded_object_q_zero_cv output_lower /\
  bounded_object_q_le_cv output_lower output_upper /\
  bounded_object_q_le_cv
    (bounded_object_q_mul_cv output_lower output_lower) input_lower /\
  bounded_object_q_le_cv input_upper
    (bounded_object_q_mul_cv output_upper output_upper) /\
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [from_cv (Pair input_lower input_upper);
         from_cv (Pair output_lower output_upper)]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  rpt strip_tac
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_le»
          [from_cv bounded_object_q_zero_cv;
           Uop Fst (from_cv (Pair input_lower input_upper))]) refs =
      (M_success (Num 1),refs)` by
     (irule bounded_case16594_object_q_le_true_argument_results
      >> simp
           [compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_fst]
      >> qexists_tac `bounded_object_q_zero_cv`
      >> qexists_tac `input_lower`
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_le»
          [Uop Fst (from_cv (Pair input_lower input_upper));
           Uop Snd (from_cv (Pair input_lower input_upper))]) refs =
      (M_success (Num 1),refs)` by
     (irule bounded_case16594_object_q_le_true_argument_results
      >> simp
           [compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_fst,
            compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_snd]
      >> qexists_tac `input_lower`
      >> qexists_tac `input_upper`
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_le»
          [from_cv bounded_object_q_zero_cv;
           Uop Fst (from_cv (Pair output_lower output_upper))]) refs =
      (M_success (Num 1),refs)` by
     (irule bounded_case16594_object_q_le_true_argument_results
      >> simp
           [compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_fst]
      >> qexists_tac `bounded_object_q_zero_cv`
      >> qexists_tac `output_lower`
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_le»
          [Uop Fst (from_cv (Pair output_lower output_upper));
           Uop Snd (from_cv (Pair output_lower output_upper))]) refs =
      (M_success (Num 1),refs)` by
     (irule bounded_case16594_object_q_le_true_argument_results
      >> simp
           [compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_fst,
            compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_snd]
      >> qexists_tac `output_lower`
      >> qexists_tac `output_upper`
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_mul»
          [Uop Fst (from_cv (Pair output_lower output_upper));
           Uop Fst (from_cv (Pair output_lower output_upper))]) refs =
      (M_success
        (from_cv (bounded_object_q_mul_cv output_lower output_lower)),refs)` by
     (irule bounded_case16594_object_q_mul_argument_results
      >> simp
           [compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_fst]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_mul»
          [Uop Snd (from_cv (Pair output_lower output_upper));
           Uop Snd (from_cv (Pair output_lower output_upper))]) refs =
      (M_success
        (from_cv (bounded_object_q_mul_cv output_upper output_upper)),refs)` by
     (irule bounded_case16594_object_q_mul_argument_results
      >> simp
           [compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_snd]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_le»
          [App «candle_cv_q_mul»
             [Uop Fst (from_cv (Pair output_lower output_upper));
              Uop Fst (from_cv (Pair output_lower output_upper))];
           Uop Fst (from_cv (Pair input_lower input_upper))]) refs =
      (M_success (Num 1),refs)` by
     (irule bounded_case16594_object_q_le_true_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> qexists_tac
           `bounded_object_q_mul_cv output_lower output_lower`
      >> qexists_tac `input_lower`
      >> simp
           [compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
            compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_fst]
      >> asm_rewrite_tac [])
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_le»
          [Uop Snd (from_cv (Pair input_lower input_upper));
           App «candle_cv_q_mul»
             [Uop Snd (from_cv (Pair output_lower output_upper));
              Uop Snd (from_cv (Pair output_lower output_upper))]]) refs =
      (M_success (Num 1),refs)` by
     (irule bounded_case16594_object_q_le_true_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> qexists_tac `input_upper`
      >> qexists_tac
           `bounded_object_q_mul_cv output_upper output_upper`
      >> simp
           [compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
            compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_pair_snd]
      >> asm_rewrite_tac [])
  >> rw [bounded_case16594_object_q_interval_sqrt_certificate_unfold]
  >> simp
       [bounded_case16594_object_q_interval_sqrt_certificate_body_def,
        compute_evalTheory.subst_def]
  >> irule bounded_case16594_compute_eval_six_if_success
  >> fs
       [compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
        compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
