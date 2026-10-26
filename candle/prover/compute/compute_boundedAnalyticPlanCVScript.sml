(*****************************************************************************
 * Versioned data boundary for the generic packed analytic checker.
 *
 * The source program remains its independently decoded cv payload.  This
 * metadata payload fixes the wire-format version, dimension, and cell count.
 * Certificate count is derived from the checked prepared program, so callers
 * cannot select a shorter record shape.
 *****************************************************************************)
Theory compute_boundedAnalyticPlanCV
Ancestors
  compute_boundedAnalyticProgramCV
  compute_boundedAnalyticPreparedPlan
  compute_boundedPackedAnalyticCheck
  compute_boundedCase16594SourceCVData
Libs
  bossLib preamble

Datatype:
  bounded_analytic_plan_metadata = BoundedAnalyticPlanMetadata num num
End

Definition bounded_analytic_plan_metadata_of_cv_def:
  bounded_analytic_plan_metadata_of_cv value =
    case value of
    | Pair (Num version) (Pair (Num dimension) (Num cell_count)) =>
        if version = 1 then
          SOME (BoundedAnalyticPlanMetadata dimension cell_count)
        else NONE
    | _ => NONE
End

Definition bounded_analytic64_certificate_count_def:
  bounded_analytic64_certificate_count [] = (0:num) /\
  bounded_analytic64_certificate_count (instruction::instructions) =
    (case instruction of
     | BoundedAnalytic64Sqrt => 1
     | BoundedAnalytic64Inverse => 1
     | BoundedAnalytic64Atan => 1
     | _ => 0) + bounded_analytic64_certificate_count instructions
End

Definition bounded_analytic_program_plan_check_def:
  bounded_analytic_program_plan_check program metadata bytes <=>
    case bounded_analytic_plan_metadata_of_cv metadata of
    | NONE => F
    | SOME (BoundedAnalyticPlanMetadata dimension cell_count) =>
        0 < dimension /\ dimension < 4294967296 /\
        0 < cell_count /\ cell_count < 4294967296 /\
        case bounded_analytic_compile_program dimension program of
        | NONE => F
        | SOME prepared_program =>
            bounded_packed_chars_analytic_complete_check
              prepared_program dimension cell_count
              (bounded_analytic64_certificate_count prepared_program) bytes
End

Definition bounded_analytic_source_plan_check_def:
  bounded_analytic_source_plan_check source_program metadata bytes <=>
    case bounded_analytic_program_of_cv source_program of
    | NONE => F
    | SOME program =>
        bounded_analytic_program_plan_check program metadata bytes
End

Definition bounded_case16594_plan_metadata_cv_def:
  bounded_case16594_plan_metadata_cv =
    Pair (Num 1) (Pair (Num 6) (Num 875))
End

Theorem bounded_analytic_plan_metadata_of_cv_examples:
  bounded_analytic_plan_metadata_of_cv
      bounded_case16594_plan_metadata_cv =
    SOME (BoundedAnalyticPlanMetadata 6 875) /\
  bounded_analytic_plan_metadata_of_cv
      (Pair (Num 2) (Pair (Num 6) (Num 875))) = NONE /\
  bounded_analytic_plan_metadata_of_cv
      (Pair (Num 1) (Pair (Num 6) (Pair (Num 875) (Num 0)))) = NONE /\
  bounded_analytic_plan_metadata_of_cv (Num 1) = NONE
Proof
  EVAL_TAC
QED

Theorem bounded_analytic_program_plan_rejects_invalid_metadata:
  ~bounded_analytic_program_plan_check bounded_case16594_program
      (Pair (Num 1) (Pair (Num 0) (Num 875))) bytes /\
  ~bounded_analytic_program_plan_check bounded_case16594_program
      (Pair (Num 1) (Pair (Num 6) (Num 0))) bytes /\
  ~bounded_analytic_program_plan_check bounded_case16594_program
      (Pair (Num 1)
        (Pair (Num 4294967296) (Num 875))) bytes
Proof
  simp [bounded_analytic_program_plan_check_def,
        bounded_analytic_plan_metadata_of_cv_def]
QED

Theorem bounded_analytic64_certificate_count_case16594:
  bounded_analytic64_certificate_count
      bounded_case16594_prepared_program = 31
Proof
  EVAL_TAC
QED

Theorem bounded_analytic_program_plan_check_case16594:
  bounded_analytic_program_plan_check bounded_case16594_program
      bounded_case16594_plan_metadata_cv bytes <=>
    bounded_packed_chars_case16594_complete_check bytes
Proof
  simp [bounded_analytic_program_plan_check_def,
        bounded_case16594_plan_metadata_cv_def,
        bounded_analytic_plan_metadata_of_cv_def,
        bounded_analytic_compile_program_case16594,
        bounded_analytic64_certificate_count_case16594,
        bounded_packed_chars_analytic_complete_check_case16594]
QED

Theorem bounded_analytic_source_plan_check_case16594:
  bounded_analytic_source_plan_check bounded_case16594_source_program_cv
      bounded_case16594_plan_metadata_cv bytes <=>
    bounded_packed_chars_case16594_complete_check bytes
Proof
  simp [bounded_analytic_source_plan_check_def,
        compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes,
        bounded_analytic_program_plan_check_case16594]
QED

val _ = export_theory ();
