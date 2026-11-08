(*****************************************************************************
 * Fast semantic/evaluator regression for the first genuine case-16594
 * negation.  This instantiates the generic production bridge on the
 * authenticated cell-0 radii and the source constant 13/500; no concrete
 * recompletion result is expanded.
 *****************************************************************************)
open compute_boundedCase16594ObjectNegEvalTheory
open compute_boundedCase16594ObjectFirstPolySemanticTheory
open compute_boundedCase16594ObjectRuntimePreservationTheory
open compute_boundedCase16594ObjectPolyStepControlEvalTheory
open compute_boundedAnalyticObjectPolyProgramRefinementTheory
open compute_boundedPackedObjectEntryRefinementTheory
open preamble

Theory compute_boundedCase16594ObjectFirstNegSemanticEval
Ancestors
  compute_boundedCase16594ObjectNegEval
  compute_boundedCase16594ObjectFirstPolySemantic
  compute_boundedCase16594ObjectDispatchPrefix8Eval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_cell0_runtime_radii_def:
  bounded_case16594_object_cell0_runtime_radii =
    THE
      (bounded_object_q_cv_list_decode
        bounded_case16594_object_cell0_radii_cv)
End

Theorem bounded_case16594_object_cell0_radii_equivalent_fast:
  bounded_object_q_cv_list_decode
      bounded_case16594_object_cell0_radii_cv <> NONE /\
  LIST_REL bounded_case10173_q_cv_equiv
    (THE
      (bounded_object_q_cv_list_decode
        bounded_case16594_object_cell0_radii_cv))
    (MAP bounded_word64_object_q_cv
      bounded_case16594_object_cell0_word_radii)
Proof
  simp
    [compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_radii_cv_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_decode_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_def,
     compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_cell0_runtime_radii_decode:
  bounded_object_q_cv_list_decode
      bounded_case16594_object_cell0_radii_cv =
    SOME bounded_case16594_object_cell0_runtime_radii
Proof
  rw [bounded_case16594_object_cell0_runtime_radii_def]
  >> Cases_on
    `bounded_object_q_cv_list_decode
       bounded_case16594_object_cell0_radii_cv`
  >> fs
       [bounded_case16594_object_cell0_radii_equivalent_fast]
QED

Theorem bounded_case16594_object_cell0_runtime_radii_encode:
  bounded_object_q_cv_list bounded_case16594_object_cell0_runtime_radii =
    bounded_case16594_object_cell0_radii_cv
Proof
  irule bounded_object_q_cv_list_encode_decode
  >> ACCEPT_TAC bounded_case16594_object_cell0_runtime_radii_decode
QED

Theorem bounded_case16594_object_cell0_runtime_radii_equivalent:
  LIST_REL bounded_case10173_q_cv_equiv
    bounded_case16594_object_cell0_runtime_radii
    (MAP bounded_word64_object_q_cv
      bounded_case16594_object_cell0_word_radii)
Proof
  fs
    [bounded_case16594_object_cell0_runtime_radii_def,
     bounded_case16594_object_cell0_radii_equivalent_fast]
QED

Theorem bounded_object_q_equiv_list_left_encoded:
  !left right.
    LIST_REL bounded_case10173_q_cv_equiv left right ==>
    EVERY bounded_object_q_encoded left
Proof
  Induct
  >> Cases_on `right`
  >> simp [LIST_REL_def]
  >> rw
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_case16594_object_cell0_runtime_radii_encoded:
  EVERY bounded_object_q_encoded
    bounded_case16594_object_cell0_runtime_radii
Proof
  metis_tac
    [bounded_case16594_object_cell0_runtime_radii_equivalent,
     bounded_object_q_equiv_list_left_encoded]
QED

Theorem bounded_analytic_source_q_interval_valid:
  bounded_packed_q_interval_valid_cv
    (bounded_analytic_source_q_interval_cv positive negative
      denominator_predecessor)
Proof
  simp
    [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

val bounded_analytic_source_q_interval_valid_expanded =
  REWRITE_RULE
    [compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def]
    bounded_analytic_source_q_interval_valid;

Theorem bounded_case16594_object_first_neg_eval_semantic:
  4101 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_state_neg»
          [from_cv bounded_case16594_object_cell0_radii_cv;
           from_cv
             (bounded_case16594_object_constant_state_cv
               (bounded_analytic_source_q_cv 13 0 499))])
        (refs:hol_refs) =
      (M_success (from_cv result_state),refs) /\
    bounded_object_q_taylor_runtime_equiv result_state
      (bounded_object_q_taylor_neg
        bounded_case16594_object_cell0_word_radii
        bounded_case16594_object_cell0_weights
        (bounded_object_q_taylor_constant 13 0 499))
Proof
  strip_tac
  >> PURE_REWRITE_TAC
    [GSYM bounded_case16594_object_cell0_runtime_radii_encode,
     bounded_case16594_object_constant_state_cv_def,
     bounded_case16594_object_zero_gradient6_cv_def,
     bounded_case16594_object_zero_hessian21_cv_def,
     bounded_case16594_object_cv_list_identity,
     bounded_case16594_object_zero_interval_identity,
     bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def]
  >> irule
       (SIMP_RULE std_ss []
         (Q.SPEC `T`
           compute_boundedCase16594ObjectNegEvalTheory.bounded_case16594_object_state_neg_eval_semantic))
  >> simp
       [bounded_case16594_object_cell0_runtime_radii_encoded,
        bounded_case16594_object_cell0_runtime_radii_equivalent,
        bounded_case16594_object_cell0_radius_pairs,
        bounded_analytic_source_q_interval_valid_expanded,
        compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded,
        bounded_object_q_interval_cv_equiv_refl]
  >> conj_tac
  >- (metis_tac
       [bounded_case16594_object_cell0_runtime_radii_equivalent,
        LIST_REL_LENGTH,rich_listTheory.LENGTH_MAP,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths,
        bounded_case16594_object_cell0_radius_pairs])
  >> simp
       [bounded_object_q_interval_list_rel_refl,
        bounded_analytic_source_q_interval_valid_expanded,
        compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

val _ = export_theory ();
