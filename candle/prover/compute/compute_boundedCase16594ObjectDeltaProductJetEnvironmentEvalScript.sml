(*****************************************************************************
 * Exact environment wrapper for the production 4*x_i*delta center jet.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductJetEnvironmentEval
Ancestors
  compute_boundedCase16594ObjectDeltaProductJetCompleteEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_delta_product_jet_environment_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [from_cv (Num coordinate);from_cv environment]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«coordinate»,from_cv (Num coordinate));
         («environment»,from_cv environment)]
        bounded_case16594_object_delta_product_jet_environment_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> simp
       [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_product_jet_environment_lookup]
QED

Theorem bounded_case16594_object_delta_product_jet_environment_eval:
  coordinate < 6 /\ LENGTH environment = 6 /\
  EVERY bounded_packed_q_interval_encoded environment /\
  262160 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [from_cv (Num coordinate);
         from_cv (bounded_object_q_cv_list environment)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_product_jet_six_cv coordinate
          (EL 0 environment) (EL 1 environment) (EL 2 environment)
          (EL 3 environment) (EL 4 environment) (EL 5 environment))),refs)
Proof
  strip_tac
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 environment;EL 1 environment;EL 2 environment;
         EL 3 environment;EL 4 environment;EL 5 environment]` by
       fs [listTheory.EVERY_EL]
  >> rw [bounded_case16594_object_delta_product_jet_environment_unfold]
  >> simp
       [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_product_jet_environment_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_product_jet_six»
            [from_cv (Num coordinate);from_cv (HD environment);
             from_cv (EL 1 environment);from_cv (EL 2 environment);
             from_cv (EL 3 environment);from_cv (EL 4 environment);
             from_cv (EL 5 environment)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_app7_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp
           [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
      >> conj_tac
      >- (irule EQ_TRANS
          >> qexists_tac
               `(M_success (from_cv (EL 0 environment)),refs)`
          >> conj_tac
          >- (irule
                compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
              >> simp [] >> intLib.ARITH_TAC)
          >> simp [listTheory.EL])
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
          >> simp [] >> intLib.ARITH_TAC)
      >> irule
           compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectDeltaProductJetCompleteEvalTheory.bounded_case16594_object_delta_product_jet_six_eval
  >> fs [listTheory.EL]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
