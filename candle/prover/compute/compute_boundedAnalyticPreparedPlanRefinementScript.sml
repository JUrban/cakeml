(*****************************************************************************
 * Structural source-to-prepared refinement for generic analytic plans.
 *
 * This proof-only relation records exactly what compilation preserves.  A
 * rational constant is related only through its proved outward enclosure;
 * variables retain their index under the declared dimension; ordinary
 * operators retain their constructor; and optimized delta instructions are
 * admitted only through the existing exact source-program identity check.
 *****************************************************************************)
Theory compute_boundedAnalyticPreparedPlanRefinement
Ancestors
  compute_boundedAnalyticPreparedPlanSound compute_boundedAnalyticPreparedPlan
Libs
  bossLib preamble

Definition bounded_analytic_poly_instruction_refines_def:
  bounded_analytic_poly_instruction_refines dimension source prepared <=>
    (?positive negative denominator_predecessor interval.
       source = BoundedPolyConstant positive negative denominator_predecessor /\
       prepared = BoundedTaylor64Constant interval /\
       bounded_analytic_rational_interval_covers positive negative
         denominator_predecessor interval) \/
    (?index.
       source = BoundedPolyVariable index /\
       index < dimension /\
       prepared = BoundedTaylor64Variable index) \/
    (source = BoundedPolyNeg /\ prepared = BoundedTaylor64Neg) \/
    (source = BoundedPolyAdd /\ prepared = BoundedTaylor64Add) \/
    (source = BoundedPolyMul /\ prepared = BoundedTaylor64Mul) \/
    (source = BoundedPolySquare /\ prepared = BoundedTaylor64Square)
End

Definition bounded_analytic_instruction_refines_def:
  bounded_analytic_instruction_refines dimension source prepared <=>
    (?source_program prepared_program.
       source = BoundedAnalyticPolynomial source_program /\
       prepared = BoundedAnalytic64Polynomial prepared_program /\
       LIST_REL (bounded_analytic_poly_instruction_refines dimension)
         source_program prepared_program) \/
    (?coordinate.
       prepared = BoundedAnalytic64NegDeltaDerivative coordinate /\
       bounded_analytic_specialization_ok source
         (BoundedNegDeltaDerivative coordinate)) \/
    (?coordinate.
       prepared = BoundedAnalytic64FourCoordinateDelta coordinate /\
       bounded_analytic_specialization_ok source
         (BoundedFourCoordinateDelta coordinate)) \/
    (source = BoundedAnalyticSqrt /\ prepared = BoundedAnalytic64Sqrt) \/
    (source = BoundedAnalyticNeg /\ prepared = BoundedAnalytic64Neg) \/
    (source = BoundedAnalyticAdd /\ prepared = BoundedAnalytic64Add) \/
    (source = BoundedAnalyticMul /\ prepared = BoundedAnalytic64Mul) \/
    (source = BoundedAnalyticSquare /\ prepared = BoundedAnalytic64Square) \/
    (source = BoundedAnalyticInverse /\ prepared = BoundedAnalytic64Inverse) \/
    (source = BoundedAnalyticAtan /\ prepared = BoundedAnalytic64Atan) \/
    (source = BoundedAnalyticPiHalf /\ prepared = BoundedAnalytic64PiHalf)
End

Theorem bounded_analytic_compile_poly_instruction_refines:
  bounded_analytic_compile_poly_instruction dimension source = SOME prepared
  ==>
  bounded_analytic_poly_instruction_refines dimension source prepared
Proof
  Cases_on `source`
  >> rw [compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_poly_instruction_def]
  >> every_case_tac
  >> gvs [bounded_analytic_poly_instruction_refines_def]
  >> metis_tac [bounded_analytic_rational_constant64_covers]
QED

Theorem bounded_analytic_compile_poly_refines:
  !source prepared.
    bounded_analytic_compile_poly dimension source = SOME prepared ==>
    LIST_REL (bounded_analytic_poly_instruction_refines dimension)
      source prepared
Proof
  Induct
  >> rw [compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_poly_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_analytic_compile_poly_instruction_refines]
QED

Theorem bounded_analytic_compile_instruction_refines:
  bounded_analytic_compile_instruction dimension source = SOME prepared
  ==>
  bounded_analytic_instruction_refines dimension source prepared
Proof
  Cases_on `source`
  >> rw [compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_instruction_def]
  >> every_case_tac
  >> gvs [bounded_analytic_instruction_refines_def]
  >> metis_tac [bounded_analytic_compile_poly_refines]
QED

Theorem bounded_analytic_recognized_specialization_sound:
  bounded_analytic_recognized_specialization source <> BoundedAnalyticGeneral
  ==>
  bounded_analytic_specialization_ok source
    (bounded_analytic_recognized_specialization source)
Proof
  rw [compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_recognized_specialization_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_analytic_compile_specialized_instruction_refines:
  bounded_analytic_compile_specialized_instruction dimension source =
    SOME prepared
  ==>
  bounded_analytic_instruction_refines dimension source prepared
Proof
  rw [compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_specialized_instruction_def]
  >> every_case_tac
  >> gvs [bounded_analytic_instruction_refines_def]
  >> TRY (drule bounded_analytic_compile_instruction_refines
          >> simp [bounded_analytic_instruction_refines_def])
  >> (qsuff_tac
        `bounded_analytic_recognized_specialization source <>
         BoundedAnalyticGeneral`
      >- metis_tac [bounded_analytic_recognized_specialization_sound]
      >> gvs [])
QED

Theorem bounded_analytic_compile_program_refines:
  !source prepared.
    bounded_analytic_compile_program dimension source = SOME prepared ==>
    LIST_REL (bounded_analytic_instruction_refines dimension) source prepared
Proof
  Induct
  >> rw [compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_program_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_analytic_compile_specialized_instruction_refines]
QED

val _ = export_theory ();
