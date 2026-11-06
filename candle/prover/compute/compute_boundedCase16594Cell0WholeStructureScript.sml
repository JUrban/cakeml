(*****************************************************************************
 * Exact singleton structure of the genuine case-16594 cell-0 whole call.    *
 *                                                                            *
 * The HOL Light exporter supplied literal cv payloads.  Decompose those      *
 * literals once at theory construction time, name their logical components,  *
 * and prove the exact production-dispatch expression they induce.            *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholeStructure
Ancestors
  compute_boundedCase16594Cell0WholePayloads
  compute_boundedCase16594Cell0FastHolLightEntryData
Libs
  bossLib preamble

fun dest_binary label term =
  case strip_comb term of
  | (_, [left,right]) => (left,right)
  | _ => raise Fail (label ^ ": expected a binary constructor");

val source_descriptor_literal =
  rhs (concl bounded_case16594_cell0_whole_source_descriptor_def);
val (plan_codes_literal,source_and_cells_literal) =
  dest_binary "source descriptor" source_descriptor_literal;
val (source_instructions_literal,packed_cells_literal) =
  dest_binary "source and cells" source_and_cells_literal;
val (packed_cell_literal,packed_cells_tail_literal) =
  dest_binary "packed cells" packed_cells_literal;
val (radii_literal,certificates_literal) =
  dest_binary "packed cell" packed_cell_literal;

val encoded_jobs_literal =
  rhs (concl bounded_case16594_cell0_whole_encoded_jobs_def);
val (job_literal,jobs_tail_literal) =
  dest_binary "encoded jobs" encoded_jobs_literal;
val (outer_boxes_literal,job_tail_literal) =
  dest_binary "job" job_literal;
val (center_boxes_literal,job_metadata_literal) =
  dest_binary "job tail" job_tail_literal;

fun define_literal name term =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,type_of term),term));

val plan_codes_def =
  define_literal "bounded_case16594_cell0_whole_plan_codes"
    plan_codes_literal;
val source_instructions_def =
  define_literal "bounded_case16594_cell0_whole_source_instructions"
    source_instructions_literal;
val packed_cell_def =
  define_literal "bounded_case16594_cell0_whole_packed_cell"
    packed_cell_literal;
val packed_cells_tail_def =
  define_literal "bounded_case16594_cell0_whole_packed_cells_tail"
    packed_cells_tail_literal;
val radii_def =
  define_literal "bounded_case16594_cell0_whole_radii" radii_literal;
val certificates_def =
  define_literal "bounded_case16594_cell0_whole_certificates"
    certificates_literal;
val job_def =
  define_literal "bounded_case16594_cell0_whole_job" job_literal;
val jobs_tail_def =
  define_literal "bounded_case16594_cell0_whole_jobs_tail"
    jobs_tail_literal;
val outer_boxes_def =
  define_literal "bounded_case16594_cell0_whole_outer_boxes"
    outer_boxes_literal;
val center_boxes_def =
  define_literal "bounded_case16594_cell0_whole_center_boxes"
    center_boxes_literal;
val job_metadata_def =
  define_literal "bounded_case16594_cell0_whole_job_metadata"
    job_metadata_literal;

Theorem bounded_case16594_cell0_whole_source_descriptor_shape:
  bounded_case16594_cell0_whole_source_descriptor =
    Pair bounded_case16594_cell0_whole_plan_codes
      (Pair bounded_case16594_cell0_whole_source_instructions
        (Pair bounded_case16594_cell0_whole_packed_cell
          bounded_case16594_cell0_whole_packed_cells_tail))
Proof
  rw
    [bounded_case16594_cell0_whole_source_descriptor_def,plan_codes_def,
     source_instructions_def,packed_cell_def,packed_cells_tail_def]
QED

Theorem bounded_case16594_cell0_whole_packed_cell_shape:
  bounded_case16594_cell0_whole_packed_cell =
    Pair bounded_case16594_cell0_whole_radii
      bounded_case16594_cell0_whole_certificates
Proof
  rw [packed_cell_def,radii_def,certificates_def]
QED

Theorem bounded_case16594_cell0_whole_encoded_jobs_shape:
  bounded_case16594_cell0_whole_encoded_jobs =
    Pair bounded_case16594_cell0_whole_job
      bounded_case16594_cell0_whole_jobs_tail
Proof
  rw
    [bounded_case16594_cell0_whole_encoded_jobs_def,job_def,jobs_tail_def]
QED

Theorem bounded_case16594_cell0_whole_job_shape:
  bounded_case16594_cell0_whole_job =
    Pair bounded_case16594_cell0_whole_outer_boxes
      (Pair bounded_case16594_cell0_whole_center_boxes
        bounded_case16594_cell0_whole_job_metadata)
Proof
  rw [job_def,outer_boxes_def,center_boxes_def,job_metadata_def]
QED

Definition bounded_case16594_cell0_whole_dispatch_cexp_def:
  bounded_case16594_cell0_whole_dispatch_cexp =
    App «candle_cv_q_packed_object_dispatch_entry»
      [from_cv bounded_case16594_cell0_whole_center_boxes;
       from_cv bounded_case16594_cell0_whole_outer_boxes;
       from_cv bounded_case16594_cell0_whole_radii;
       from_cv bounded_case16594_cell0_whole_plan_codes;
       from_cv bounded_case16594_cell0_whole_source_instructions;
       from_cv bounded_case16594_cell0_whole_certificates]
End

Theorem bounded_case16594_cell0_whole_dispatch_identity:
  bounded_case16594_cell0_whole_dispatch_cexp =
    bounded_case16594_cell0_fast_hol_light_entry
Proof
  rw
    [bounded_case16594_cell0_whole_dispatch_cexp_def,center_boxes_def,
     outer_boxes_def,radii_def,plan_codes_def,source_instructions_def,
     certificates_def,
     compute_boundedCase16594Cell0FastHolLightEntryDataTheory.bounded_case16594_cell0_fast_hol_light_entry_def]
QED

val _ = export_theory ();
