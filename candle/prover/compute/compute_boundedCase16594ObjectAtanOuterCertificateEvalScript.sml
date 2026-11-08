(*****************************************************************************
 * Evaluator bridge for the genuine case-16594 outer q-atan certificate.
 *
 * The source Taylor state may use a different exact rational encoding from
 * the authenticated word certificate.  The generic enclosure lemma below
 * turns the mathematical enclosure relation into a production evaluator
 * result, after which the already-computed inner atan certificate can be
 * composed without re-running or reproving its numerical work.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanOuterCertificateEval
Ancestors
  compute_boundedCase16594ObjectAtanCertificateEval
  compute_boundedCase16594ObjectInverseCertificateEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_q_interval_atn_outer_certificate_body_def:
  bounded_case16594_object_q_interval_atn_outer_certificate_body =
    App «candle_cv_bool_and»
      [App «candle_cv_q_interval_encloses»
        [Var «word_input»;Var «source_input»];
       App «candle_cv_q_interval_atn_certificate»
        [Var «word_input»;Var «output»]]
End

Theorem bounded_case16594_object_q_interval_encloses_contract_eval:
  bounded_object_q_interval_encoded outer /\
  bounded_object_q_interval_encoded inner /\
  bounded_object_q_interval_encloses outer inner /\
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_encloses»
        [from_cv outer;from_cv inner]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> gvs []
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_encloses»
            [from_cv (Pair lower' upper');
             from_cv (Pair lower upper)]) refs`
  >> conj_tac
  >- simp [compute_execTheory.from_cv_def]
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_q_interval_encloses_conditions_eval
  >> simp []
  >> metis_tac
       [compute_boundedObjectIntervalEnclosesEquivalenceTheory.bounded_object_q_interval_encloses_pair_iff]
QED

Theorem bounded_case16594_object_q_interval_atn_outer_certificate_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_interval_atn_outer_certificate» =
    SOME
      ([«source_input»;«word_input»;«output»],
       bounded_case16594_object_q_interval_atn_outer_certificate_body)
Proof
  rw [bounded_case16594_object_q_interval_atn_outer_certificate_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_q_interval_atn_outer_certificate_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_atn_outer_certificate»
        [from_cv source_input;from_cv word_input;from_cv output])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«source_input»,from_cv source_input);
         («word_input»,from_cv word_input);
         («output»,from_cv output)]
        bounded_case16594_object_q_interval_atn_outer_certificate_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> simp
       [bounded_case16594_object_q_interval_atn_outer_certificate_lookup]
QED

Theorem bounded_case16594_object_runtime_atan_center_outer_certificate_eval:
  bounded_object_q_interval_encoded runtime_center /\
  bounded_object_q_interval_cv_equiv runtime_center
    (bounded_object_q_taylor_center
      bounded_case16594_object_source8_result) /\
  4097 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_atn_outer_certificate»
        [from_cv runtime_center;
         from_cv bounded_case16594_object_cell0_atan_center_input_cv;
         from_cv bounded_case16594_object_cell0_atan_center_result_cv])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> `bounded_object_q_interval_encloses
        bounded_case16594_object_cell0_atan_center_input_cv
        runtime_center` by
       (irule
          compute_boundedObjectIntervalEnclosesEquivalenceTheory.bounded_object_q_interval_encloses_equiv_inner
        >> conj_tac >- simp []
        >> conj_tac
        >- simp
             [compute_boundedCase16594ObjectAtanInputContractTheory.bounded_case16594_object_atan_center_input_encoded]
        >> qexists_tac
             `bounded_object_q_taylor_center
                bounded_case16594_object_source8_result`
        >> simp
             [compute_boundedCase16594ObjectAtanInputContractTheory.bounded_case16594_object_source8_center_encoded,
              compute_boundedCase16594ObjectSource8SemanticShapeTheory.bounded_case16594_object_source8_center_certificate_encloses])
  >> simp
       [bounded_case16594_object_q_interval_atn_outer_certificate_unfold,
        bounded_case16594_object_q_interval_atn_outer_certificate_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedCase16594ObjectInverseCertificateEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_q_interval_encloses_contract_eval
      >> simp
           [compute_boundedCase16594ObjectAtanInputContractTheory.bounded_case16594_object_atan_center_input_encoded]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectAtanCertificateEvalTheory.bounded_case16594_object_atan_center_inner_certificate_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
