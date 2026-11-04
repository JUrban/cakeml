(*****************************************************************************
 * Proof-producing evaluation of the five algebraic checks in the genuine
 * case-16594 atan packet.
 *
 * The fixed numerical tails are evaluated once.  The two source-dependent
 * square guards then compose those results with representation-independent
 * enclosure proofs for the actual runtime Taylor fields.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanAlgebraicCertificateEval
Ancestors
  compute_boundedCase16594ObjectAtanOuterCertificateEval
  compute_evalPure
Libs
  bossLib preamble cv_transLib intLib

val _ = cv_trans
  compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_square_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_derivative_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_input_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_square_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_derivative_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_derivative_square_cv_def;

val center_square_tail_pure_eval = time cv_eval
  ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_encloses»
        [from_cv bounded_case16594_object_cell0_atan_center_square_cv;
         App «candle_cv_q_interval_normalize»
           [App «candle_cv_q_interval_square»
             [from_cv bounded_case16594_object_cell0_atan_center_input_cv]]])``;
val _ = save_thm
  ("bounded_case16594_object_atan_center_square_tail_pure_eval",
   center_square_tail_pure_eval);

val box_square_tail_pure_eval = time cv_eval
  ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_encloses»
        [from_cv bounded_case16594_object_cell0_atan_box_square_cv;
         App «candle_cv_q_interval_normalize»
           [App «candle_cv_q_interval_square»
             [from_cv bounded_case16594_object_cell0_atan_box_input_cv]]])``;
val _ = save_thm
  ("bounded_case16594_object_atan_box_square_tail_pure_eval",
   box_square_tail_pure_eval);

val center_inverse_pure_eval = time cv_eval
  ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [App «candle_cv_q_packed_object_atn_denominator»
          [from_cv bounded_case16594_object_cell0_atan_center_square_cv];
         from_cv bounded_case16594_object_cell0_atan_center_derivative_cv])``;
val _ = save_thm
  ("bounded_case16594_object_atan_center_inverse_pure_eval",
   center_inverse_pure_eval);

val box_inverse_pure_eval = time cv_eval
  ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [App «candle_cv_q_packed_object_atn_denominator»
          [from_cv bounded_case16594_object_cell0_atan_box_square_cv];
         from_cv bounded_case16594_object_cell0_atan_box_derivative_cv])``;
val _ = save_thm
  ("bounded_case16594_object_atan_box_inverse_pure_eval",
   box_inverse_pure_eval);

val derivative_square_pure_eval = time cv_eval
  ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [from_cv bounded_case16594_object_cell0_atan_box_derivative_cv;
         from_cv bounded_case16594_object_cell0_atan_box_derivative_cv;
         from_cv
           bounded_case16594_object_cell0_atan_box_derivative_square_cv])``;
val _ = save_thm
  ("bounded_case16594_object_atan_derivative_square_pure_eval",
   derivative_square_pure_eval);

Theorem bounded_case16594_object_atan_center_square_tail_eval:
  4096 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_encloses»
        [from_cv bounded_case16594_object_cell0_atan_center_square_cv;
         App «candle_cv_q_interval_normalize»
           [App «candle_cv_q_interval_square»
             [from_cv bounded_case16594_object_cell0_atan_center_input_cv]]])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac
       [center_square_tail_pure_eval]
QED

Theorem bounded_case16594_object_atan_box_square_tail_eval:
  4096 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_encloses»
        [from_cv bounded_case16594_object_cell0_atan_box_square_cv;
         App «candle_cv_q_interval_normalize»
           [App «candle_cv_q_interval_square»
             [from_cv bounded_case16594_object_cell0_atan_box_input_cv]]])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac
       [box_square_tail_pure_eval]
QED

Theorem bounded_case16594_object_atan_center_inverse_eval:
  4096 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [App «candle_cv_q_packed_object_atn_denominator»
          [from_cv bounded_case16594_object_cell0_atan_center_square_cv];
         from_cv bounded_case16594_object_cell0_atan_center_derivative_cv])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac
       [center_inverse_pure_eval]
QED

Theorem bounded_case16594_object_atan_box_inverse_eval:
  4096 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [App «candle_cv_q_packed_object_atn_denominator»
          [from_cv bounded_case16594_object_cell0_atan_box_square_cv];
         from_cv bounded_case16594_object_cell0_atan_box_derivative_cv])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac
       [box_inverse_pure_eval]
QED

Theorem bounded_case16594_object_atan_derivative_square_eval:
  4096 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [from_cv bounded_case16594_object_cell0_atan_box_derivative_cv;
         from_cv bounded_case16594_object_cell0_atan_box_derivative_cv;
         from_cv
           bounded_case16594_object_cell0_atan_box_derivative_square_cv])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac
       [derivative_square_pure_eval]
QED

Definition bounded_case16594_object_q_interval_square_outer_certificate_body_def:
  bounded_case16594_object_q_interval_square_outer_certificate_body =
    App «candle_cv_bool_and»
      [App «candle_cv_q_interval_encloses»
        [Var «word_input»;Var «source_input»];
       App «candle_cv_q_interval_encloses»
        [Var «output»;
         App «candle_cv_q_interval_normalize»
           [App «candle_cv_q_interval_square» [Var «word_input»]]]]
End

Theorem bounded_case16594_object_q_interval_square_outer_certificate_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_interval_square_outer_certificate» =
    SOME
      ([«source_input»;«word_input»;«output»],
       bounded_case16594_object_q_interval_square_outer_certificate_body)
Proof
  rw [bounded_case16594_object_q_interval_square_outer_certificate_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_q_interval_square_outer_certificate_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [from_cv source_input;from_cv word_input;from_cv output])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«source_input»,from_cv source_input);
         («word_input»,from_cv word_input);
         («output»,from_cv output)]
        bounded_case16594_object_q_interval_square_outer_certificate_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> simp
       [bounded_case16594_object_q_interval_square_outer_certificate_lookup]
QED

Theorem bounded_case16594_object_runtime_atan_center_square_eval:
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_cv_equiv runtime_center
    (bounded_object_q_taylor_center
      bounded_case16594_object_source8_result) /\
  4097 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [from_cv runtime_center;
         from_cv bounded_case16594_object_cell0_atan_center_input_cv;
         from_cv bounded_case16594_object_cell0_atan_center_square_cv])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> `bounded_object_q_interval_encloses
        bounded_case16594_object_cell0_atan_center_input_cv
        runtime_center` by
       (irule
          compute_boundedObjectIntervalEnclosesEquivalenceTheory.bounded_object_q_interval_encloses_equiv_inner
        >> simp
             [compute_boundedCase16594ObjectAtanInputContractTheory.bounded_case16594_object_atan_center_input_encoded]
        >> qexists_tac
             `bounded_object_q_taylor_center
                bounded_case16594_object_source8_result`
        >> simp
             [compute_boundedCase16594ObjectAtanInputContractTheory.bounded_case16594_object_source8_center_encoded,
              compute_boundedCase16594ObjectSource8SemanticShapeTheory.bounded_case16594_object_source8_center_certificate_encloses])
  >> simp
       [bounded_case16594_object_q_interval_square_outer_certificate_unfold,
        bounded_case16594_object_q_interval_square_outer_certificate_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectAtanOuterCertificateEvalTheory.bounded_case16594_object_q_interval_encloses_contract_eval
      >> simp
           [compute_boundedCase16594ObjectAtanInputContractTheory.bounded_case16594_object_atan_center_input_encoded]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_atan_center_square_tail_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_runtime_atan_box_square_eval:
  bounded_object_q_interval_encoded runtime_value_bound /\
  bounded_object_q_interval_cv_equiv runtime_value_bound
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result) /\
  4097 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_square_outer_certificate»
        [from_cv runtime_value_bound;
         from_cv bounded_case16594_object_cell0_atan_box_input_cv;
         from_cv bounded_case16594_object_cell0_atan_box_square_cv])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> `bounded_object_q_interval_encoded
        bounded_case16594_object_cell0_atan_box_input_cv` by
       simp
         [compute_boundedCase16594ObjectAtanCertificateRelationsTheory.bounded_case16594_object_atan_inputs_identical,
          compute_boundedCase16594ObjectAtanInputContractTheory.bounded_case16594_object_atan_center_input_encoded]
  >> `bounded_object_q_interval_encloses
        bounded_case16594_object_cell0_atan_box_input_cv
        runtime_value_bound` by
       (irule
          compute_boundedObjectIntervalEnclosesEquivalenceTheory.bounded_object_q_interval_encloses_equiv_inner
        >> simp []
        >> qexists_tac
             `bounded_object_q_taylor_value_bound
                bounded_case16594_object_source8_result`
        >> simp
             [compute_boundedCase16594ObjectAtanInputContractTheory.bounded_case16594_object_source8_value_bound_encoded,
              compute_boundedCase16594ObjectAtanInputContractTheory.bounded_case16594_object_source8_value_bound_certificate_encloses])
  >> simp
       [bounded_case16594_object_q_interval_square_outer_certificate_unfold,
        bounded_case16594_object_q_interval_square_outer_certificate_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectAtanOuterCertificateEvalTheory.bounded_case16594_object_q_interval_encloses_contract_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_atan_box_square_tail_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
