(*****************************************************************************
 * Total outer analytic executor for prepared compact Taylor programs.
 *
 * Polynomial blocks use the prepared postfix executor.  Scalar operations
 * consume one typed certificate record from a separate stream.  Thus source
 * plan authentication, untrusted certificate preparation, and recurring
 * numerical execution remain distinct boundaries.
 *****************************************************************************)
Theory compute_boundedAnalyticProgram
Ancestors
  compute_boundedTaylorProgram
Libs
  bossLib preamble

Datatype:
  bounded_analytic64_instruction =
    BoundedAnalytic64Polynomial (bounded_taylor64_instruction list)
  | BoundedAnalytic64Sqrt
  | BoundedAnalytic64Neg
  | BoundedAnalytic64Add
  | BoundedAnalytic64Mul
  | BoundedAnalytic64Square
  | BoundedAnalytic64Inverse
  | BoundedAnalytic64Atan
  | BoundedAnalytic64PiHalf
End

Datatype:
  bounded_analytic64_certificate =
    BoundedAnalytic64SqrtCertificate
      bounded_interval64 bounded_interval64 bounded_interval64
      bounded_interval64 bounded_interval64
  | BoundedAnalytic64InverseCertificate
      bounded_interval64 bounded_interval64
  | BoundedAnalytic64AtanCertificate
      (bounded_interval64 option) (bounded_interval64 option)
      bounded_interval64 bounded_interval64
End

Definition bounded_analytic64_program_step_def:
  bounded_analytic64_program_step radii center_environment box_environment
      instruction state =
    case state of
    | (stack,certificates) =>
      case instruction of
      | BoundedAnalytic64Polynomial program =>
          (case bounded_taylor64_program_eval radii center_environment
            box_environment program of
           | NONE => NONE
           | SOME result => SOME (result::stack,certificates))
      | BoundedAnalytic64Sqrt =>
          (case (stack,certificates) of
           | (value::rest,
              BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
                center_derivative box_derivative box_second_reciprocal::
                certificate_rest) =>
               (case bounded_taylor64_sqrt radii center_sqrt box_sqrt
                  center_derivative box_derivative box_second_reciprocal
                  value of
                | NONE => NONE
                | SOME result => SOME (result::rest,certificate_rest))
           | _ => NONE)
      | BoundedAnalytic64Neg =>
          (case stack of
           | value::rest =>
               (case bounded_taylor64_neg_complete radii value of
                | NONE => NONE
                | SOME result => SOME (result::rest,certificates))
           | _ => NONE)
      | BoundedAnalytic64Add =>
          (case stack of
           | right::left::rest =>
               (case bounded_taylor64_add_complete radii left right of
                | NONE => NONE
                | SOME result => SOME (result::rest,certificates))
           | _ => NONE)
      | BoundedAnalytic64Mul =>
          (case stack of
           | right::left::rest =>
               (case bounded_taylor64_mul radii left right of
                | NONE => NONE
                | SOME result => SOME (result::rest,certificates))
           | _ => NONE)
      | BoundedAnalytic64Square =>
          (case stack of
           | value::rest =>
               (case bounded_taylor64_mul radii value value of
                | NONE => NONE
                | SOME result => SOME (result::rest,certificates))
           | _ => NONE)
      | BoundedAnalytic64Inverse =>
          (case (stack,certificates) of
           | (value::rest,
              BoundedAnalytic64InverseCertificate
                center_reciprocal box_reciprocal::certificate_rest) =>
               (case bounded_taylor64_inverse radii center_reciprocal
                  box_reciprocal value of
                | NONE => NONE
                | SOME result => SOME (result::rest,certificate_rest))
           | _ => NONE)
      | BoundedAnalytic64Atan =>
          (case (stack,certificates) of
           | (value::rest,
              BoundedAnalytic64AtanCertificate lower_reciprocal
                upper_reciprocal center_derivative box_derivative::
                certificate_rest) =>
               (case bounded_taylor64_atan radii lower_reciprocal
                  upper_reciprocal center_derivative box_derivative value of
                | NONE => NONE
                | SOME result => SOME (result::rest,certificate_rest))
           | _ => NONE)
      | BoundedAnalytic64PiHalf =>
          (case bounded_taylor64_constant bounded_atan_pi_half of
           | NONE => NONE
           | SOME result => SOME (result::stack,certificates))
End

Definition bounded_analytic64_program_run_def:
  bounded_analytic64_program_run radii center_environment box_environment
      [] state = SOME state ∧
  bounded_analytic64_program_run radii center_environment box_environment
      (instruction::instructions) state =
    case bounded_analytic64_program_step radii center_environment
      box_environment instruction state of
    | NONE => NONE
    | SOME next =>
        bounded_analytic64_program_run radii center_environment
          box_environment instructions next
End

Definition bounded_analytic64_program_eval_def:
  bounded_analytic64_program_eval radii center_environment box_environment
      program certificates =
    case bounded_analytic64_program_run radii center_environment
      box_environment program ([],certificates) of
    | SOME ([result],[]) => SOME result
    | _ => NONE
End

Theorem bounded_analytic64_program_step_well_formed:
  bounded_taylor64_stack_well_formed (FST state) ∧
  bounded_analytic64_program_step radii center_environment box_environment
      instruction state = SOME result ⇒
  bounded_taylor64_stack_well_formed (FST result)
Proof
  Cases_on `instruction`
  >> Cases_on `state`
  >> Cases_on `q`
  >> rw [bounded_analytic64_program_step_def,
         bounded_taylor64_stack_well_formed_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_taylor64_program_eval_some
  >> imp_res_tac
       compute_boundedTaylorSqrtTheory.bounded_taylor64_sqrt_some
  >> imp_res_tac
       compute_boundedTaylorInverseTheory.bounded_taylor64_inverse_some
  >> imp_res_tac
       compute_boundedTaylorAtanTheory.bounded_taylor64_atan_some
  >> imp_res_tac bounded_taylor64_neg_complete_some
  >> imp_res_tac bounded_taylor64_add_complete_some
  >> imp_res_tac
       compute_boundedTaylorMulTheory.bounded_taylor64_mul_some
  >> imp_res_tac
       compute_boundedTaylorBaseTheory.bounded_taylor64_constant_some
  >> fs [bounded_taylor64_stack_well_formed_def]
  >> metis_tac
       [bounded_taylor64_program_eval_some,
        compute_boundedTaylorSqrtTheory.bounded_taylor64_sqrt_some,
        compute_boundedTaylorInverseTheory.bounded_taylor64_inverse_some,
        compute_boundedTaylorAtanTheory.bounded_taylor64_atan_some,
        bounded_taylor64_neg_complete_some,
        bounded_taylor64_add_complete_some,
        compute_boundedTaylorMulTheory.bounded_taylor64_mul_some,
        compute_boundedTaylorBaseTheory.bounded_taylor64_constant_some]
QED

Theorem bounded_analytic64_program_run_well_formed:
  ∀program state result.
    bounded_taylor64_stack_well_formed (FST state) ∧
    bounded_analytic64_program_run radii center_environment box_environment
      program state = SOME result ⇒
    bounded_taylor64_stack_well_formed (FST result)
Proof
  Induct
  >> rw [bounded_analytic64_program_run_def]
  >> every_case_tac
  >> gvs []
  >> first_x_assum match_mp_tac
  >> metis_tac [bounded_analytic64_program_step_well_formed]
QED

Theorem bounded_analytic64_program_eval_some:
  bounded_analytic64_program_eval radii center_environment box_environment
      program certificates = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_analytic64_program_eval_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_analytic64_program_run_well_formed
  >> fs [bounded_taylor64_stack_well_formed_def]
QED

Theorem bounded_analytic64_program_closed_tests:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let state = BoundedTaylor64 T one zeros6 one zeros6 zeros21 in
  let constant = BoundedAnalytic64Polynomial
    [BoundedTaylor64Constant one] in
  bounded_analytic64_program_eval radii (REPLICATE 6 one)
      (REPLICATE 6 one) [constant;BoundedAnalytic64Square] [] =
    SOME state ∧
  bounded_analytic64_program_eval radii (REPLICATE 6 one)
      (REPLICATE 6 one) [constant;BoundedAnalytic64Inverse]
      [BoundedAnalytic64InverseCertificate one one] = SOME state ∧
  bounded_analytic64_program_eval radii (REPLICATE 6 one)
      (REPLICATE 6 one) [constant;BoundedAnalytic64Inverse] [] = NONE ∧
  bounded_analytic64_program_eval radii (REPLICATE 6 one)
      (REPLICATE 6 one) [constant]
      [BoundedAnalytic64InverseCertificate one one] = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
