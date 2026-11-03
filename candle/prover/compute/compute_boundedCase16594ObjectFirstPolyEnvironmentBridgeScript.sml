(*****************************************************************************
 * Authenticated environment instance of the first genuine polynomial run.
 *
 * Extract the exact six-element center and outer interval lists from the
 * production entry payload.  Keeping the extraction at theory-construction
 * time avoids a second handwritten copy of the genuine data.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectFirstPolyEnvironmentBridge
Ancestors
  compute_boundedCase16594ObjectFirstPolyRunBridge
  compute_boundedCase16594ObjectRuntimePreservation
Libs
  bossLib preamble intLib

fun cv_list_elements tm =
  let
    val (head,arguments) = strip_comb tm;
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Num",[number]) =>
        if aconv number numSyntax.zero_tm then []
        else raise Fail "nonzero terminator in authenticated object list"
    | ("Pair",[item,items]) => item :: cv_list_elements items
    | _ => raise Fail "non-list authenticated object payload"
  end;

fun cv_list_from_definition definition =
  listSyntax.mk_list (cv_list_elements (rhs (concl definition)),``:cv``);

val center_boxes_tm =
  cv_list_from_definition
    compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_center_boxes_cv_def;
val outer_boxes_tm =
  cv_list_from_definition
    compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_outer_boxes_cv_def;

val bounded_case16594_object_cell0_center_boxes_def =
  new_definition
    ("bounded_case16594_object_cell0_center_boxes_def",
     mk_eq
       (mk_var ("bounded_case16594_object_cell0_center_boxes",``:cv list``),
        center_boxes_tm));
val bounded_case16594_object_cell0_outer_boxes_def =
  new_definition
    ("bounded_case16594_object_cell0_outer_boxes_def",
     mk_eq
       (mk_var ("bounded_case16594_object_cell0_outer_boxes",``:cv list``),
        outer_boxes_tm));

Theorem bounded_case16594_object_cell0_center_boxes_encode:
  bounded_object_q_cv_list bounded_case16594_object_cell0_center_boxes =
    bounded_case16594_object_cell0_center_boxes_cv
Proof
  simp
    [bounded_case16594_object_cell0_center_boxes_def,
     compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_center_boxes_cv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Theorem bounded_case16594_object_cell0_outer_boxes_encode:
  bounded_object_q_cv_list bounded_case16594_object_cell0_outer_boxes =
    bounded_case16594_object_cell0_outer_boxes_cv
Proof
  simp
    [bounded_case16594_object_cell0_outer_boxes_def,
     compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_outer_boxes_cv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Theorem bounded_case16594_object_cell0_center_boxes_length:
  LENGTH bounded_case16594_object_cell0_center_boxes = 6
Proof
  simp [bounded_case16594_object_cell0_center_boxes_def]
QED

Theorem bounded_case16594_object_cell0_outer_boxes_length:
  LENGTH bounded_case16594_object_cell0_outer_boxes = 6
Proof
  simp [bounded_case16594_object_cell0_outer_boxes_def]
QED

Theorem bounded_case16594_object_cell0_center_boxes_valid:
  EVERY bounded_packed_q_interval_valid_cv
    bounded_case16594_object_cell0_center_boxes
Proof
  simp
    [bounded_case16594_object_cell0_center_boxes_def,
     compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_case16594_object_cell0_outer_boxes_valid:
  EVERY bounded_packed_q_interval_valid_cv
    bounded_case16594_object_cell0_outer_boxes
Proof
  simp
    [bounded_case16594_object_cell0_outer_boxes_def,
     compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_packed_q_interval_valid_cv_object_encoded:
  bounded_packed_q_interval_valid_cv value ==>
  bounded_object_q_interval_encoded value
Proof
  rw
    [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> metis_tac []
QED

Theorem bounded_packed_q_interval_valid_cv_list_object_encoded:
  !values.
    EVERY bounded_packed_q_interval_valid_cv values ==>
    EVERY bounded_object_q_interval_encoded values
Proof
  Induct
  >> simp [bounded_packed_q_interval_valid_cv_object_encoded]
QED

Theorem bounded_case16594_object_cell0_center_boxes_equivalent:
  LIST_REL bounded_object_q_interval_cv_equiv
    bounded_case16594_object_cell0_center_boxes
    bounded_case16594_object_cell0_center_boxes
Proof
  irule bounded_object_q_interval_list_rel_refl
  >> irule
       bounded_packed_q_interval_valid_cv_list_object_encoded
  >> ACCEPT_TAC bounded_case16594_object_cell0_center_boxes_valid
QED

Theorem bounded_case16594_object_cell0_outer_boxes_equivalent:
  LIST_REL bounded_object_q_interval_cv_equiv
    bounded_case16594_object_cell0_outer_boxes
    bounded_case16594_object_cell0_outer_boxes
Proof
  irule bounded_object_q_interval_list_rel_refl
  >> irule
       bounded_packed_q_interval_valid_cv_list_object_encoded
  >> ACCEPT_TAC bounded_case16594_object_cell0_outer_boxes_valid
QED

Theorem bounded_case16594_object_source0_exact_environment_runtime_refines:
  4107 < clock ==>
  ?runtime_result_stack.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_source0_program_cv;
         from_cv (Pair (compute_exec$Num 1) (compute_exec$Num 0))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (compute_exec$Num 1)
          (bounded_object_q_cv_list runtime_result_stack))),refs) /\
    bounded_object_q_taylor_stack_runtime_refines
      runtime_result_stack [bounded_case16594_object_source0_result]
Proof
  strip_tac
  >> PURE_REWRITE_TAC
       [GSYM bounded_case16594_object_cell0_center_boxes_encode,
        GSYM bounded_case16594_object_cell0_outer_boxes_encode]
  >> irule bounded_case16594_object_source0_poly_run_runtime_refines
  >> simp
       [bounded_case16594_object_cell0_center_boxes_length,
        bounded_case16594_object_cell0_outer_boxes_length]
  >> conj_tac
  >- (qexists_tac `bounded_case16594_object_cell0_center_boxes`
      >> simp
           [bounded_case16594_object_cell0_center_boxes_valid,
            bounded_case16594_object_cell0_center_boxes_equivalent])
  >> qexists_tac `bounded_case16594_object_cell0_outer_boxes`
  >> simp
       [bounded_case16594_object_cell0_outer_boxes_valid,
        bounded_case16594_object_cell0_outer_boxes_equivalent]
QED

val _ = export_theory ();
