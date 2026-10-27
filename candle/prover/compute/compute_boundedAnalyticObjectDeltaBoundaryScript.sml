(*****************************************************************************
 * Exact boundary for the two recognized delta instruction families.
 *
 * This child does not claim the still-open Taylor-state refinement.  It
 * proves the fail-closed coordinate ranges and packages the authenticated
 * source programs with their exact integer meanings.  The subsequent object
 * refinement therefore has exactly six concrete cases, not an open-ended
 * coordinate family or a basename/program alias.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectDeltaBoundary
Ancestors
  compute_boundedAnalyticObjectOrdinaryDispatcherRefinement
  compute_boundedDeltaSpecialization
Libs
  bossLib preamble intLib

Theorem bounded_delta64_neg_derivative_coordinate_range:
  bounded_delta64_neg_derivative radii center_environment coordinate =
      SOME result ==>
  3 <= coordinate /\ coordinate <= 5
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_neg_derivative_def]
  >> every_case_tac
  >> gvs []
  >> intLib.ARITH_TAC
QED

Theorem bounded_delta64_four_coordinate_coordinate_range:
  bounded_delta64_four_coordinate radii center_environment box_environment
      coordinate = SOME result ==>
  coordinate <= 2
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_four_coordinate_def]
  >> every_case_tac
  >> gvs []
  >> intLib.ARITH_TAC
QED

Theorem bounded_neg_delta_specialization_coordinate_range:
  bounded_analytic_specialization_ok source
      (BoundedNegDeltaDerivative coordinate) ==>
  coordinate = 3 \/ coordinate = 4 \/ coordinate = 5
Proof
  rw [compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_ok_def,
      compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_program_def]
  >> every_case_tac
  >> gvs []
  >> intLib.ARITH_TAC
QED

Theorem bounded_four_coordinate_specialization_coordinate_range:
  bounded_analytic_specialization_ok source
      (BoundedFourCoordinateDelta coordinate) ==>
  coordinate = 0 \/ coordinate = 1 \/ coordinate = 2
Proof
  rw [compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_ok_def,
      compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_program_def]
  >> every_case_tac
  >> gvs []
  >> intLib.ARITH_TAC
QED

Theorem bounded_neg_delta_specialization_exact_integer_semantics:
  bounded_analytic_specialization_ok source
      (BoundedNegDeltaDerivative coordinate) ==>
  (coordinate = 3 /\
   source = BoundedAnalyticPolynomial
     (THE (bounded_analytic_specialization_program
       (BoundedNegDeltaDerivative 3))) /\
   bounded_poly_int_eval
     (THE (bounded_analytic_specialization_program
       (BoundedNegDeltaDerivative 3))) [x0;x1;x2;x3;x4;x5] =
     SOME (bounded_neg_delta_derivative3 x0 x1 x2 x3 x4 x5)) \/
  (coordinate = 4 /\
   source = BoundedAnalyticPolynomial
     (THE (bounded_analytic_specialization_program
       (BoundedNegDeltaDerivative 4))) /\
   bounded_poly_int_eval
     (THE (bounded_analytic_specialization_program
       (BoundedNegDeltaDerivative 4))) [x0;x1;x2;x3;x4;x5] =
     SOME (bounded_neg_delta_derivative4 x0 x1 x2 x3 x4 x5)) \/
  (coordinate = 5 /\
   source = BoundedAnalyticPolynomial
     (THE (bounded_analytic_specialization_program
       (BoundedNegDeltaDerivative 5))) /\
   bounded_poly_int_eval
     (THE (bounded_analytic_specialization_program
       (BoundedNegDeltaDerivative 5))) [x0;x1;x2;x3;x4;x5] =
     SOME (bounded_neg_delta_derivative5 x0 x1 x2 x3 x4 x5))
Proof
  strip_tac
  >> drule bounded_neg_delta_specialization_coordinate_range
  >> strip_tac
  >> gvs [compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_ok_def,
          compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_program_def,
          compute_boundedDeltaSpecializationTheory.bounded_neg_delta_derivative3_program_semantics,
          compute_boundedDeltaSpecializationTheory.bounded_neg_delta_derivative4_program_semantics,
          compute_boundedDeltaSpecializationTheory.bounded_neg_delta_derivative5_program_semantics]
QED

Theorem bounded_four_coordinate_specialization_exact_integer_semantics:
  bounded_analytic_specialization_ok source
      (BoundedFourCoordinateDelta coordinate) ==>
  (coordinate = 0 /\
   source = BoundedAnalyticPolynomial
     (THE (bounded_analytic_specialization_program
       (BoundedFourCoordinateDelta 0))) /\
   bounded_poly_int_eval
     (THE (bounded_analytic_specialization_program
       (BoundedFourCoordinateDelta 0))) [x0;x1;x2;x3;x4;x5] =
     SOME (4 * x0 * bounded_delta_value x0 x1 x2 x3 x4 x5)) \/
  (coordinate = 1 /\
   source = BoundedAnalyticPolynomial
     (THE (bounded_analytic_specialization_program
       (BoundedFourCoordinateDelta 1))) /\
   bounded_poly_int_eval
     (THE (bounded_analytic_specialization_program
       (BoundedFourCoordinateDelta 1))) [x0;x1;x2;x3;x4;x5] =
     SOME (4 * x1 * bounded_delta_value x0 x1 x2 x3 x4 x5)) \/
  (coordinate = 2 /\
   source = BoundedAnalyticPolynomial
     (THE (bounded_analytic_specialization_program
       (BoundedFourCoordinateDelta 2))) /\
   bounded_poly_int_eval
     (THE (bounded_analytic_specialization_program
       (BoundedFourCoordinateDelta 2))) [x0;x1;x2;x3;x4;x5] =
     SOME (4 * x2 * bounded_delta_value x0 x1 x2 x3 x4 x5))
Proof
  strip_tac
  >> drule bounded_four_coordinate_specialization_coordinate_range
  >> strip_tac
  >> gvs [compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_ok_def,
          compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_program_def,
          compute_boundedDeltaSpecializationTheory.bounded_four_coordinate_delta0_program_semantics,
          compute_boundedDeltaSpecializationTheory.bounded_four_coordinate_delta1_program_semantics,
          compute_boundedDeltaSpecializationTheory.bounded_four_coordinate_delta2_program_semantics]
QED

val _ = export_theory ();
