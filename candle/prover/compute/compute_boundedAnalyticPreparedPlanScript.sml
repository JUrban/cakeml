(*****************************************************************************
 * Generic checked preparation of bounded analytic source programs.
 *
 * Rational constants are rounded outward at scale 2^40 using exact natural
 * arithmetic and rejected if either magnitude cannot fit word64.  The six
 * existing delta optimizations are selected only by exact source-program
 * equality through bounded_analytic_specialization_ok; every other source
 * instruction follows the general compiler.
 *****************************************************************************)
Theory compute_boundedAnalyticPreparedPlan
Ancestors
  compute_boundedCase16594PreparedPlan compute_boundedAnalyticRationalConstant
Libs
  bossLib preamble wordsLib

Definition bounded_analytic_compile_poly_instruction_def:
  bounded_analytic_compile_poly_instruction dimension instruction =
    case instruction of
    | BoundedPolyConstant positive negative denominator_predecessor =>
        (case bounded_analytic_rational_constant64 positive negative
          denominator_predecessor of
         | NONE => NONE
         | SOME value => SOME (BoundedTaylor64Constant value))
    | BoundedPolyVariable index =>
        if index < dimension then SOME (BoundedTaylor64Variable index)
        else NONE
    | BoundedPolyNeg => SOME BoundedTaylor64Neg
    | BoundedPolyAdd => SOME BoundedTaylor64Add
    | BoundedPolyMul => SOME BoundedTaylor64Mul
    | BoundedPolySquare => SOME BoundedTaylor64Square
End

Definition bounded_analytic_compile_poly_def:
  bounded_analytic_compile_poly dimension [] = SOME [] /\
  bounded_analytic_compile_poly dimension (instruction::instructions) =
    case bounded_analytic_compile_poly_instruction dimension instruction of
    | NONE => NONE
    | SOME prepared =>
      case bounded_analytic_compile_poly dimension instructions of
      | NONE => NONE
      | SOME rest => SOME (prepared::rest)
End

Definition bounded_analytic_compile_instruction_def:
  bounded_analytic_compile_instruction dimension instruction =
    case instruction of
    | BoundedAnalyticPolynomial program =>
        (case bounded_analytic_compile_poly dimension program of
         | NONE => NONE
         | SOME prepared => SOME (BoundedAnalytic64Polynomial prepared))
    | BoundedAnalyticSqrt => SOME BoundedAnalytic64Sqrt
    | BoundedAnalyticNeg => SOME BoundedAnalytic64Neg
    | BoundedAnalyticAdd => SOME BoundedAnalytic64Add
    | BoundedAnalyticMul => SOME BoundedAnalytic64Mul
    | BoundedAnalyticSquare => SOME BoundedAnalytic64Square
    | BoundedAnalyticInverse => SOME BoundedAnalytic64Inverse
    | BoundedAnalyticAtan => SOME BoundedAnalytic64Atan
    | BoundedAnalyticPiHalf => SOME BoundedAnalytic64PiHalf
End

Definition bounded_analytic_recognized_specialization_def:
  bounded_analytic_recognized_specialization instruction =
    if bounded_analytic_specialization_ok instruction
        (BoundedNegDeltaDerivative 3) then BoundedNegDeltaDerivative 3
    else if bounded_analytic_specialization_ok instruction
        (BoundedNegDeltaDerivative 4) then BoundedNegDeltaDerivative 4
    else if bounded_analytic_specialization_ok instruction
        (BoundedNegDeltaDerivative 5) then BoundedNegDeltaDerivative 5
    else if bounded_analytic_specialization_ok instruction
        (BoundedFourCoordinateDelta 0) then BoundedFourCoordinateDelta 0
    else if bounded_analytic_specialization_ok instruction
        (BoundedFourCoordinateDelta 1) then BoundedFourCoordinateDelta 1
    else if bounded_analytic_specialization_ok instruction
        (BoundedFourCoordinateDelta 2) then BoundedFourCoordinateDelta 2
    else BoundedAnalyticGeneral
End

Definition bounded_analytic_compile_specialized_instruction_def:
  bounded_analytic_compile_specialized_instruction dimension instruction =
    case bounded_analytic_recognized_specialization instruction of
    | BoundedAnalyticGeneral =>
        bounded_analytic_compile_instruction dimension instruction
    | BoundedNegDeltaDerivative coordinate =>
        SOME (BoundedAnalytic64NegDeltaDerivative coordinate)
    | BoundedFourCoordinateDelta coordinate =>
        SOME (BoundedAnalytic64FourCoordinateDelta coordinate)
End

Definition bounded_analytic_compile_program_def:
  bounded_analytic_compile_program dimension [] = SOME [] /\
  bounded_analytic_compile_program dimension
      (instruction::instructions) =
    case bounded_analytic_compile_specialized_instruction
      dimension instruction of
    | NONE => NONE
    | SOME prepared =>
      case bounded_analytic_compile_program dimension instructions of
      | NONE => NONE
      | SOME rest => SOME (prepared::rest)
End

Theorem bounded_analytic_rational_constant64_examples:
  bounded_analytic_rational_constant64 1 0 2 =
    SOME (BoundedInterval64
      (BoundedSigned64 F 366503875925w)
      (BoundedSigned64 F 366503875926w)) /\
  bounded_analytic_rational_constant64 0 1 0 =
    SOME (BoundedInterval64
      (BoundedSigned64 T 1099511627776w)
      (BoundedSigned64 T 1099511627776w)) /\
  bounded_analytic_rational_constant64 3 2 0 =
    SOME bounded_atan_one /\
  bounded_analytic_rational_constant64
      18446744073709551616 0 0 = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_analytic_compile_rejects_out_of_range:
  bounded_analytic_compile_poly_instruction 6
      (BoundedPolyVariable 6) = NONE /\
  bounded_analytic_compile_poly_instruction 6
      (BoundedPolyConstant 18446744073709551616 0 0) = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_analytic_recognized_specialization_rejects_aliases:
  bounded_analytic_recognized_specialization
      (BoundedAnalyticPolynomial []) = BoundedAnalyticGeneral /\
  bounded_analytic_recognized_specialization BoundedAnalyticSqrt =
    BoundedAnalyticGeneral
Proof
  EVAL_TAC
QED

Theorem bounded_analytic_recognized_specializations_case16594:
  MAP bounded_analytic_recognized_specialization
      bounded_case16594_program = bounded_case16594_specializations
Proof
  EVAL_TAC
QED

Theorem bounded_analytic_compile_program_case16594:
  bounded_analytic_compile_program 6 bounded_case16594_program =
    SOME bounded_case16594_prepared_program
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
