(*****************************************************************************
 * Minimal authenticated runtime view of the case-16594 dispatch plan.
 *
 * This theory deliberately depends only on the checked source decoder and
 * prepared-plan compiler.  It does not import the historical packed-entry
 * proof cone.  The runtime code list is derived from the same specialization
 * roles consumed by the compiler, while the runtime source cv is accepted
 * only through the fail-closed source decoder.
 *****************************************************************************)
Theory compute_boundedCase16594DispatchRuntimePlanIdentity
Ancestors
  compute_boundedCase16594DispatchPlanIdentity
  compute_boundedCase16594SourceCVData
Libs
  bossLib preamble

Definition bounded_case16594_dispatch_code_cv_def:
  bounded_case16594_dispatch_code_cv role =
    case role of
    | BoundedAnalyticGeneral => Num 0
    | BoundedNegDeltaDerivative coordinate => Num (SUC coordinate)
    | BoundedFourCoordinateDelta coordinate => Num (SUC coordinate)
End

Definition bounded_case16594_dispatch_codes_cv_def:
  bounded_case16594_dispatch_codes_cv =
    FOLDR (\code rest. Pair code rest) (Num 0:cv)
      (MAP bounded_case16594_dispatch_code_cv
        bounded_case16594_specializations)
End

Definition bounded_case16594_dispatch_runtime_plan_def:
  bounded_case16594_dispatch_runtime_plan source_program roles
      prepared_program runtime_codes runtime_sources <=>
    runtime_codes =
      FOLDR (\code rest. Pair code rest) (Num 0:cv)
        (MAP bounded_case16594_dispatch_code_cv roles) /\
    bounded_analytic_program_of_cv runtime_sources = SOME source_program /\
    bounded_case16594_compile_specialized source_program roles =
      SOME prepared_program
End

Theorem bounded_case16594_dispatch_runtime_plan_empty:
  bounded_case16594_dispatch_runtime_plan [] [] [] (Num 0) (Num 0)
Proof
  simp
    [bounded_case16594_dispatch_runtime_plan_def,
     compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_def,
     compute_boundedAnalyticProgramCVTheory.bounded_analytic_program_of_cv_def]
QED

Theorem bounded_case16594_dispatch_runtime_plan_cons:
  bounded_case16594_dispatch_runtime_plan
      (source::source_rest) (role::role_rest) (prepared::prepared_rest)
      (Pair runtime_code runtime_code_rest)
      (Pair runtime_source runtime_source_rest) ==>
  runtime_code = bounded_case16594_dispatch_code_cv role /\
  bounded_analytic_instruction_of_cv runtime_source = SOME source /\
  bounded_case16594_compile_specialized_instruction source role =
    SOME prepared /\
  bounded_case16594_dispatch_runtime_plan source_rest role_rest
    prepared_rest runtime_code_rest runtime_source_rest
Proof
  rw [bounded_case16594_dispatch_runtime_plan_def]
  >> fs
    [compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_def,
     compute_boundedAnalyticProgramCVTheory.bounded_analytic_program_of_cv_def]
  >> every_case_tac
  >> gvs [bounded_case16594_dispatch_runtime_plan_def]
QED

Theorem bounded_case16594_dispatch_runtime_plan_value:
  bounded_case16594_dispatch_runtime_plan bounded_case16594_program
    bounded_case16594_specializations bounded_case16594_prepared_program
    bounded_case16594_dispatch_codes_cv bounded_case16594_source_program_cv
Proof
  rw
    [bounded_case16594_dispatch_runtime_plan_def,
     bounded_case16594_dispatch_codes_cv_def]
  >- ACCEPT_TAC
       compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes
  >> mp_tac
       compute_boundedCase16594DispatchPlanIdentityTheory.bounded_case16594_source_prepared_plan_authenticated_value
  >> simp
    [compute_boundedCase16594DispatchPlanIdentityTheory.bounded_case16594_source_prepared_plan_authenticated_def]
QED

Theorem bounded_case16594_dispatch_codes_cv_length:
  bounded_case16594_dispatch_codes_cv =
    FOLDR (\code rest. Pair code rest) (Num 0:cv)
      (MAP bounded_case16594_dispatch_code_cv
        bounded_case16594_specializations) /\
  LENGTH bounded_case16594_specializations = 167
Proof
  simp [bounded_case16594_dispatch_codes_cv_def]
  >> EVAL_TAC
QED

val _ = export_theory ();
