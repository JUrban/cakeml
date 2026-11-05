(*****************************************************************************
 * Canonical cv encoding of bounded analytic source programs.
 *
 * The fail-closed decoder authenticates meanings, while the production
 * evaluator branches on the exact cv constructor representation.  These
 * round-trip theorems connect the two views and identify the authenticated
 * case-16594 payload with the canonical encoding of its 167 instructions.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchCanonicalSourceIdentity
Ancestors
  compute_boundedCase16594ObjectDispatchCell0PayloadIdentity
Libs
  bossLib preamble

Definition bounded_case16594_poly_instruction_cv_def:
  bounded_case16594_poly_instruction_cv instruction =
    case instruction of
    | BoundedPolyConstant positive negative denominator_predecessor =>
        Pair (Num 0)
          (Pair (Pair (Num positive) (Num negative))
            (Num denominator_predecessor))
    | BoundedPolyVariable index => Pair (Num 1) (Num index)
    | BoundedPolyNeg => Num 2
    | BoundedPolyAdd => Num 3
    | BoundedPolyMul => Num 4
    | BoundedPolySquare => Num 5
End

Definition bounded_case16594_poly_program_cv_def:
  bounded_case16594_poly_program_cv program =
    FOLDR (\instruction rest.
      Pair (bounded_case16594_poly_instruction_cv instruction) rest)
      (Num 0:cv) program
End

Definition bounded_case16594_analytic_instruction_cv_def:
  bounded_case16594_analytic_instruction_cv instruction =
    case instruction of
    | BoundedAnalyticPolynomial program =>
        Pair (Num 0) (bounded_case16594_poly_program_cv program)
    | BoundedAnalyticSqrt => Pair (Num 1) bounded_sqrt_placeholder_cv
    | BoundedAnalyticNeg => Num 2
    | BoundedAnalyticAdd => Num 3
    | BoundedAnalyticMul => Num 4
    | BoundedAnalyticSquare => Num 5
    | BoundedAnalyticInverse => Num 6
    | BoundedAnalyticAtan => Num 7
    | BoundedAnalyticPiHalf => Num 8
End

Definition bounded_case16594_analytic_program_cv_def:
  bounded_case16594_analytic_program_cv program =
    FOLDR (\instruction rest.
      Pair (bounded_case16594_analytic_instruction_cv instruction) rest)
      (Num 0:cv) program
End

Theorem bounded_case16594_poly_instruction_cv_round_trip:
  bounded_poly_instruction_of_cv
    (bounded_case16594_poly_instruction_cv instruction) = SOME instruction
Proof
  Cases_on `instruction`
  >> simp
    [bounded_case16594_poly_instruction_cv_def,
     compute_boundedAnalyticProgramCVTheory.bounded_poly_instruction_of_cv_def,
     compute_boundedAnalyticProgramCVTheory.bounded_rational_of_cv_def]
QED

Theorem bounded_case16594_poly_program_cv_round_trip:
  !program.
    bounded_poly_program_of_cv
      (bounded_case16594_poly_program_cv program) = SOME program
Proof
  Induct
  >> fs
    [bounded_case16594_poly_program_cv_def,
     compute_boundedAnalyticProgramCVTheory.bounded_poly_program_of_cv_def,
     bounded_case16594_poly_instruction_cv_round_trip]
QED

Theorem bounded_case16594_analytic_instruction_cv_round_trip:
  bounded_analytic_instruction_of_cv
    (bounded_case16594_analytic_instruction_cv instruction) = SOME instruction
Proof
  Cases_on `instruction`
  >> simp
    [bounded_case16594_analytic_instruction_cv_def,
     compute_boundedAnalyticProgramCVTheory.bounded_analytic_instruction_of_cv_def,
     compute_boundedAnalyticProgramCVTheory.bounded_sqrt_placeholder_cv_def,
     bounded_case16594_poly_program_cv_round_trip]
QED

Theorem bounded_case16594_analytic_program_cv_round_trip:
  !program.
    bounded_analytic_program_of_cv
      (bounded_case16594_analytic_program_cv program) = SOME program
Proof
  Induct
  >> fs
    [bounded_case16594_analytic_program_cv_def,
     compute_boundedAnalyticProgramCVTheory.bounded_analytic_program_of_cv_def,
     bounded_case16594_analytic_instruction_cv_round_trip]
QED

Theorem bounded_case16594_runtime_cell0_sources_canonical:
  bounded_case16594_runtime_cell0_sources_cv =
    bounded_case16594_analytic_program_cv bounded_case16594_program
Proof
  rw
    [compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_sources_identity,
     compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_def,
     compute_boundedCase16594ProgramDataTheory.bounded_case16594_program_def,
     bounded_case16594_analytic_program_cv_def,
     bounded_case16594_analytic_instruction_cv_def,
     bounded_case16594_poly_program_cv_def,
     bounded_case16594_poly_instruction_cv_def,
     compute_boundedAnalyticProgramCVTheory.bounded_sqrt_placeholder_cv_def]
QED

val _ = export_theory ();
