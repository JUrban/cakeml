(*****************************************************************************
 * One authenticated identity for the case-16594 source, specialization-code,
 * and prepared programs used by the explicit-radius object dispatcher.
 *****************************************************************************)
Theory compute_boundedCase16594DispatchPlanIdentity
Ancestors
  compute_boundedCase16594PreparedPlan
  compute_boundedAnalyticPreparedPlanRefinement
Libs
  bossLib preamble wordsLib cv_transLib

val _ = cv_trans
  compute_boundedAnalyticRationalConstantTheory.bounded_analytic_scale40_def;
val _ = cv_trans
  compute_boundedAnalyticRationalConstantTheory.bounded_analytic_nat_ceil_div_def;
val _ = cv_trans
  compute_boundedSignedEndpointTheory.bounded_signed64_make_def;
val _ = cv_trans
  compute_boundedAtanTheory.bounded_atan_word64_def;
val _ = cv_trans
  compute_boundedAtanTheory.bounded_atan_one_def;
val _ = cv_trans
  compute_boundedAnalyticRationalConstantTheory.bounded_analytic_rational_constant64_def;
val _ = cv_trans
  compute_boundedCase16594PreparedPlanTheory.bounded_case16594_constant64_def;

Theorem bounded_case16594_constant64_domain:
  IS_SOME
    (bounded_case16594_constant64 positive negative denominator_predecessor) <=>
  (positive = 0 /\ negative = 1 /\ denominator_predecessor = 0) \/
  (positive = 1 /\ negative = 0 /\ denominator_predecessor = 0) \/
  (positive = 1 /\ negative = 0 /\ denominator_predecessor = 2) \/
  (positive = 2 /\ negative = 0 /\ denominator_predecessor = 0) \/
  (positive = 3 /\ negative = 0 /\ denominator_predecessor = 0) \/
  (positive = 4 /\ negative = 0 /\ denominator_predecessor = 0) \/
  (positive = 13 /\ negative = 0 /\ denominator_predecessor = 24) \/
  (positive = 13 /\ negative = 0 /\ denominator_predecessor = 499)
Proof
  PURE_REWRITE_TAC
    [compute_boundedCase16594PreparedPlanTheory.bounded_case16594_constant64_def]
  >> rpt (COND_CASES_TAC >> ASM_REWRITE_TAC [optionTheory.IS_SOME_DEF])
QED

Theorem bounded_case16594_constant64_generic_table:
  bounded_analytic_rational_constant64 0 1 0 =
      bounded_case16594_constant64 0 1 0 /\
  bounded_analytic_rational_constant64 1 0 0 =
      bounded_case16594_constant64 1 0 0 /\
  bounded_analytic_rational_constant64 1 0 2 =
      bounded_case16594_constant64 1 0 2 /\
  bounded_analytic_rational_constant64 2 0 0 =
      bounded_case16594_constant64 2 0 0 /\
  bounded_analytic_rational_constant64 3 0 0 =
      bounded_case16594_constant64 3 0 0 /\
  bounded_analytic_rational_constant64 4 0 0 =
      bounded_case16594_constant64 4 0 0 /\
  bounded_analytic_rational_constant64 13 0 24 =
      bounded_case16594_constant64 13 0 24 /\
  bounded_analytic_rational_constant64 13 0 499 =
      bounded_case16594_constant64 13 0 499
Proof
  CONV_TAC cv_eval
QED

Theorem bounded_case16594_constant64_is_generic:
  bounded_case16594_constant64 positive negative denominator_predecessor =
    SOME interval ==>
  bounded_analytic_rational_constant64 positive negative
    denominator_predecessor = SOME interval
Proof
  strip_tac
  >> `IS_SOME
      (bounded_case16594_constant64 positive negative
          denominator_predecessor)` by fs []
  >> fs
    [bounded_case16594_constant64_domain,
     bounded_case16594_constant64_generic_table]
  >> metis_tac []
QED

Theorem bounded_case16594_compile_poly_instruction_refines:
  bounded_case16594_compile_poly_instruction source = SOME prepared ==>
  bounded_analytic_poly_instruction_refines 6 source prepared
Proof
  Cases_on `source`
  >> rw
    [compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_poly_instruction_def]
  >> every_case_tac
  >> gvs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_poly_instruction_refines_def]
  >> drule bounded_case16594_constant64_is_generic
  >> metis_tac
    [compute_boundedAnalyticPreparedPlanSoundTheory.bounded_analytic_rational_constant64_covers]
QED

Theorem bounded_case16594_compile_poly_refines:
  !source prepared.
    bounded_case16594_compile_poly source = SOME prepared ==>
    LIST_REL (bounded_analytic_poly_instruction_refines 6) source prepared
Proof
  Induct
  >> rw [compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_poly_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_case16594_compile_poly_instruction_refines]
QED

Theorem bounded_case16594_compile_analytic_instruction_refines:
  bounded_case16594_compile_analytic_instruction source = SOME prepared ==>
  bounded_analytic_instruction_refines 6 source prepared
Proof
  Cases_on `source`
  >> rw
    [compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_analytic_instruction_def]
  >> every_case_tac
  >> gvs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
  >> metis_tac [bounded_case16594_compile_poly_refines]
QED

Theorem bounded_case16594_compile_specialized_instruction_refines:
  bounded_case16594_compile_specialized_instruction source role =
    SOME prepared ==>
  bounded_analytic_instruction_refines 6 source prepared
Proof
  Cases_on `role`
  >> rw
    [compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_instruction_def]
  >> every_case_tac
  >> gvs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
  >> TRY
    (drule bounded_case16594_compile_analytic_instruction_refines
     >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def])
  >> metis_tac []
QED

Theorem bounded_case16594_compile_specialized_refines:
  !source roles prepared.
    bounded_case16594_compile_specialized source roles = SOME prepared ==>
    LIST_REL (bounded_analytic_instruction_refines 6) source prepared
Proof
  Induct
  >- (Cases_on `roles`
      >> simp
        [compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_def])
  >> Cases_on `roles`
  >- simp
    [compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_def]
  >> rw
    [compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_case16594_compile_specialized_instruction_refines]
QED

Definition bounded_case16594_source_prepared_plan_authenticated_def:
  bounded_case16594_source_prepared_plan_authenticated source_program
      prepared_program specialization_roles <=>
    bounded_case16594_compile_specialized source_program
      specialization_roles = SOME prepared_program
End

Theorem bounded_case16594_source_prepared_plan_authenticated_value:
  bounded_case16594_source_prepared_plan_authenticated
    bounded_case16594_program bounded_case16594_prepared_program
    bounded_case16594_specializations
Proof
  rw [bounded_case16594_source_prepared_plan_authenticated_def]
  >> metis_tac
    [compute_boundedCase16594PreparedPlanTheory.bounded_case16594_prepared_program_ok_value,
     compute_boundedCase16594PreparedPlanTheory.bounded_case16594_prepared_program_ok_def]
QED

Theorem bounded_case16594_dispatch_plan_refines:
  LIST_REL (bounded_analytic_instruction_refines 6)
    bounded_case16594_program bounded_case16594_prepared_program
Proof
  mp_tac bounded_case16594_source_prepared_plan_authenticated_value
  >> rw [bounded_case16594_source_prepared_plan_authenticated_def]
  >> metis_tac [bounded_case16594_compile_specialized_refines]
QED

val _ = export_theory ();
