(*****************************************************************************
 * Authenticated-input relation for the genuine case-16594 cell-0 fast trace.
 *
 * The production entry retains exact rational inputs, while the fixed-word
 * checker uses directed scale-2^40 enclosures.  The exact object inputs below
 * are projected mechanically from the authenticated six-field entry.  The
 * fast certificates are independent checked witnesses; they are deliberately
 * not identified with the legacy production certificate stream.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0RuntimePayloadIdentity
Ancestors
  compute_boundedCase16594Cell0AuthenticatedWordRuntimeTrace
  compute_boundedAnalyticObjectCompleteRefinement
Libs
  bossLib preamble wordsLib intLib

fun cv_list_elements tm =
  let
    val (head,arguments) = strip_comb tm;
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Num",[number]) =>
        if aconv number numSyntax.zero_tm then []
        else raise Fail "nonzero authenticated payload-list terminator"
    | ("Pair",[item,items]) => item :: cv_list_elements items
    | _ => raise Fail "malformed authenticated payload list"
  end;

fun cv_list_from_definition definition =
  listSyntax.mk_list (cv_list_elements (rhs (concl definition)),``:cv``);

fun define_literal name ty tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,ty),tm));

val object_radii_tm =
  cv_list_from_definition
    compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_radii_cv_def;

val bounded_case16594_cell0_authenticated_object_radii_def =
  define_literal "bounded_case16594_cell0_authenticated_object_radii"
    ``:cv list`` object_radii_tm;

Theorem bounded_case16594_cell0_authenticated_center_payload_identity:
  bounded_object_q_cv_list
      bounded_case16594_cell0_authenticated_object_center_environment =
    bounded_case16594_runtime_cell0_center_boxes_cv
Proof
  simp
    [compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_object_center_environment_def,
     compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_center_boxes_cv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Theorem bounded_case16594_cell0_authenticated_box_payload_identity:
  bounded_object_q_cv_list
      bounded_case16594_cell0_authenticated_object_box_environment =
    bounded_case16594_runtime_cell0_outer_boxes_cv
Proof
  simp
    [compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_object_box_environment_def,
     compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_outer_boxes_cv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Theorem bounded_case16594_cell0_authenticated_radii_payload_identity:
  bounded_object_q_cv_list bounded_case16594_cell0_authenticated_object_radii =
    bounded_case16594_runtime_cell0_radii_cv
Proof
  simp
    [bounded_case16594_cell0_authenticated_object_radii_def,
     compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_radii_cv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Theorem bounded_case16594_cell0_authenticated_payload_lengths:
  LENGTH bounded_case16594_cell0_authenticated_object_center_environment = 6 /\
  LENGTH bounded_case16594_cell0_authenticated_object_box_environment = 6 /\
  LENGTH bounded_case16594_cell0_authenticated_object_radii = 6
Proof
  simp
    [compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_object_center_environment_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_object_box_environment_def,
     bounded_case16594_cell0_authenticated_object_radii_def]
QED

Theorem bounded_case16594_cell0_authenticated_radii_equivalent:
  LIST_REL bounded_case10173_q_cv_equiv
    bounded_case16594_cell0_authenticated_object_radii
    (MAP bounded_word64_object_q_cv
      bounded_case16594_cell0_source_word_radii)
Proof
  simp
    [bounded_case16594_cell0_authenticated_object_radii_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_radii_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_def,
     compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> EVAL_TAC
QED

val _ = export_theory ();
