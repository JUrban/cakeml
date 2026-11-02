(*****************************************************************************
 * Authenticated identity of the packed source program used by the genuine
 * case-16594 entry.
 *
 * Codes are derived from the independently checked specialization roles;
 * they are not a second handwritten instruction table.  The entry expression
 * must carry exactly that code list and the independently decoded source cv.
 *****************************************************************************)
Theory compute_boundedCase16594PackedSourceProgramIdentity
Ancestors
  compute_boundedPackedSourceSpecializedStepControlEval
  compute_boundedCase16594ProgramData
Libs
  bossLib preamble

Definition bounded_case16594_specialization_code_cv_def:
  bounded_case16594_specialization_code_cv role =
    case role of
    | BoundedAnalyticGeneral => Num 0
    | BoundedNegDeltaDerivative coordinate => Num (SUC coordinate)
    | BoundedFourCoordinateDelta coordinate => Num (SUC coordinate)
End

Definition bounded_case16594_specialization_codes_cv_def:
  bounded_case16594_specialization_codes_cv =
    FOLDR (\code rest. Pair code rest) (Num 0:cv)
      (MAP bounded_case16594_specialization_code_cv
        bounded_case16594_specializations)
End

Definition bounded_case16594_nonzero_code_positions_def:
  bounded_case16594_nonzero_code_positions index (Num 0) = SOME [] /\
  bounded_case16594_nonzero_code_positions index (Num (SUC malformed)) =
    NONE /\
  bounded_case16594_nonzero_code_positions index (Pair code rest) =
    case code of
    | Pair left right => NONE
    | Num numeral =>
        case bounded_case16594_nonzero_code_positions (SUC index) rest of
        | NONE => NONE
        | SOME positions =>
            SOME
              (if numeral = 0 then positions
               else (index,numeral)::positions)
End

Definition bounded_case16594_packed_source_entry_argument_def:
  bounded_case16594_packed_source_entry_argument index =
    case bounded_case16594_packed_source_cell0_entry_v2173_cexp of
    | App function_name arguments => LLOOKUP arguments index
    | _ => NONE
End

Theorem bounded_case16594_specialization_codes_length:
  bounded_packed_source_cv_list_length
    bounded_case16594_specialization_codes_cv = 167
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_specialization_codes_nonzero_positions:
  bounded_case16594_nonzero_code_positions 0
      bounded_case16594_specialization_codes_cv =
    SOME
      [(34,4);(35,1);(77,5);(78,2);(120,6);(121,3)]
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_packed_source_entry_shape:
  case bounded_case16594_packed_source_cell0_entry_v2173_cexp of
  | App function_name arguments =>
      function_name =
        «candle_cv_q_packed_source_certificate_dispatch_entry» /\
      LENGTH arguments = 8
  | _ => F
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_packed_source_entry_codes_authenticated:
  bounded_case16594_packed_source_entry_argument 2 =
    SOME (from_cv bounded_case16594_specialization_codes_cv)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_packed_source_entry_sources_authenticated:
  bounded_case16594_packed_source_entry_argument 3 =
    SOME (from_cv bounded_case16594_source_program_cv)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_specialized_source_roles_authenticated:
  bounded_analytic_instruction_of_cv bounded_case16594_source34_cv =
      SOME
        (BoundedAnalyticPolynomial
          (THE (bounded_analytic_specialization_program
            (BoundedNegDeltaDerivative 3)))) /\
  bounded_analytic_instruction_of_cv bounded_case16594_source35_cv =
      SOME
        (BoundedAnalyticPolynomial
          (THE (bounded_analytic_specialization_program
            (BoundedFourCoordinateDelta 0)))) /\
  bounded_analytic_instruction_of_cv bounded_case16594_source77_cv =
      SOME
        (BoundedAnalyticPolynomial
          (THE (bounded_analytic_specialization_program
            (BoundedNegDeltaDerivative 4)))) /\
  bounded_analytic_instruction_of_cv bounded_case16594_source78_cv =
      SOME
        (BoundedAnalyticPolynomial
          (THE (bounded_analytic_specialization_program
            (BoundedFourCoordinateDelta 1)))) /\
  bounded_analytic_instruction_of_cv bounded_case16594_source120_cv =
      SOME
        (BoundedAnalyticPolynomial
          (THE (bounded_analytic_specialization_program
            (BoundedNegDeltaDerivative 5)))) /\
  bounded_analytic_instruction_of_cv bounded_case16594_source121_cv =
      SOME
        (BoundedAnalyticPolynomial
          (THE (bounded_analytic_specialization_program
            (BoundedFourCoordinateDelta 2))))
Proof
  simp
    [bounded_case16594_source34_cv_def,
     bounded_case16594_source35_cv_def,
     bounded_case16594_source77_cv_def,
     bounded_case16594_source78_cv_def,
     bounded_case16594_source120_cv_def,
     bounded_case16594_source121_cv_def,
     bounded_packed_source_cv_nth_def,
     compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_def]
  >> EVAL_TAC
QED

val _ = export_theory ();
