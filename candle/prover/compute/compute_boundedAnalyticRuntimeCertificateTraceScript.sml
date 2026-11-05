(*****************************************************************************
 * Executable runtime-certificate trace for the fixed-word analytic checker.
 *
 * The typed checker consumes one certificate value for each sqrt, inverse,
 * or atan instruction.  The exact-object production dispatcher consumes a
 * flat interval stream instead.  This theory records that flat stream while
 * running the same fixed-word steps.  Its first projection is exactly the
 * existing fixed-word program run; no second numerical checker is introduced.
 *****************************************************************************)
Theory compute_boundedAnalyticRuntimeCertificateTrace
Ancestors
  compute_boundedAnalyticProgram
Libs
  bossLib preamble

Definition bounded_analytic64_runtime_certificate_packet_def:
  bounded_analytic64_runtime_certificate_packet instruction state =
    case (instruction,state) of
    | (BoundedAnalytic64Sqrt,
       (value::rest,
        BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
          center_derivative box_derivative box_second_reciprocal::
          certificate_rest)) =>
        SOME
          [center_sqrt;box_sqrt;center_derivative;box_derivative;
           box_second_reciprocal]
    | (BoundedAnalytic64Inverse,
       (value::rest,
        BoundedAnalytic64InverseCertificate center_reciprocal
          box_reciprocal::certificate_rest)) =>
        SOME [center_reciprocal;box_reciprocal]
    | (BoundedAnalytic64Atan,
       (BoundedTaylor64 source_domain center_value center_gradient
          value_bound gradient_bounds hessian::rest,
        BoundedAnalytic64AtanCertificate center_lower_reciprocal
          center_upper_reciprocal center_derivative box_derivative::
          certificate_rest)) =>
        (case bounded_interval64_atan_range center_value
             center_lower_reciprocal center_upper_reciprocal of
         | NONE => NONE
         | SOME center_result =>
           case bounded_interval64_square center_value of
           | NONE => NONE
           | SOME center_square =>
             case bounded_interval64_square value_bound of
             | NONE => NONE
             | SOME box_square =>
               case bounded_interval64_square box_derivative of
               | NONE => NONE
               | SOME box_derivative_square =>
                 SOME
                   [center_value;value_bound;center_result;center_square;
                    center_derivative;box_square;box_derivative;
                    box_derivative_square])
    | _ => SOME []
End

Definition bounded_analytic64_program_runtime_certificate_trace_def:
  bounded_analytic64_program_runtime_certificate_trace radii
      center_environment box_environment [] state = SOME (state,[]) /\
  bounded_analytic64_program_runtime_certificate_trace radii
      center_environment box_environment (instruction::instructions) state =
    case bounded_analytic64_runtime_certificate_packet instruction state of
    | NONE => NONE
    | SOME packet =>
      case bounded_analytic64_program_step radii center_environment
          box_environment instruction state of
      | NONE => NONE
      | SOME next =>
        case bounded_analytic64_program_runtime_certificate_trace radii
            center_environment box_environment instructions next of
        | NONE => NONE
        | SOME (final_state,packets) =>
            SOME (final_state,packet ++ packets)
End

Theorem bounded_analytic64_program_runtime_certificate_trace_projects_run:
  !program state final_state packets.
    bounded_analytic64_program_runtime_certificate_trace radii
      center_environment box_environment program state =
        SOME (final_state,packets) ==>
    bounded_analytic64_program_run radii center_environment box_environment
      program state = SOME final_state
Proof
  Induct
  >- simp
       [bounded_analytic64_program_runtime_certificate_trace_def,
        compute_boundedAnalyticProgramTheory.bounded_analytic64_program_run_def]
  >> rpt gen_tac
  >> rw
       [bounded_analytic64_program_runtime_certificate_trace_def,
        compute_boundedAnalyticProgramTheory.bounded_analytic64_program_run_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_analytic64_program_runtime_certificate_trace_cons:
  bounded_analytic64_program_runtime_certificate_trace radii
      center_environment box_environment (instruction::instructions) state =
        SOME (final_state,packets) ==>
  ?packet next rest_packets.
    bounded_analytic64_runtime_certificate_packet instruction state =
      SOME packet /\
    bounded_analytic64_program_step radii center_environment box_environment
      instruction state = SOME next /\
    bounded_analytic64_program_runtime_certificate_trace radii
      center_environment box_environment instructions next =
        SOME (final_state,rest_packets) /\
    packets = packet ++ rest_packets
Proof
  rw [bounded_analytic64_program_runtime_certificate_trace_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

val _ = export_theory ();
