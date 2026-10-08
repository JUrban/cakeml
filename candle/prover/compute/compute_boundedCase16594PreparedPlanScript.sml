(*****************************************************************************
 * Checked preparation of the pinned case16594 source plan.
 *
 * The compiler maps every authenticated source constructor to the general
 * prepared analytic language.  Rational constants are accepted only from
 * the exact finite constant vocabulary in the pinned source and are replaced
 * by their outward 2^40 interval encodings.  Unknown constants and variables
 * fail closed.
 *****************************************************************************)
Theory compute_boundedCase16594PreparedPlan
Ancestors
  compute_boundedCase16594ProgramData compute_boundedAnalyticProgram
Libs
  bossLib preamble

Definition bounded_case16594_constant64_def:
  bounded_case16594_constant64 (positive:num) (negative:num)
      (denominator_predecessor:num) =
    if positive = 0 ∧ negative = 1 ∧ denominator_predecessor = 0 then
      SOME (BoundedInterval64
        (BoundedSigned64 T 1099511627776w)
        (BoundedSigned64 T 1099511627776w))
    else if positive = 1 ∧ negative = 0 ∧ denominator_predecessor = 0 then
      SOME bounded_atan_one
    else if positive = 1 ∧ negative = 0 ∧ denominator_predecessor = 2 then
      SOME (BoundedInterval64
        (BoundedSigned64 F 366503875925w)
        (BoundedSigned64 F 366503875926w))
    else if positive = 2 ∧ negative = 0 ∧ denominator_predecessor = 0 then
      SOME (BoundedInterval64
        (BoundedSigned64 F 2199023255552w)
        (BoundedSigned64 F 2199023255552w))
    else if positive = 3 ∧ negative = 0 ∧ denominator_predecessor = 0 then
      SOME (BoundedInterval64
        (BoundedSigned64 F 3298534883328w)
        (BoundedSigned64 F 3298534883328w))
    else if positive = 4 ∧ negative = 0 ∧ denominator_predecessor = 0 then
      SOME (BoundedInterval64
        (BoundedSigned64 F 4398046511104w)
        (BoundedSigned64 F 4398046511104w))
    else if positive = 13 ∧ negative = 0 ∧ denominator_predecessor = 24 then
      SOME (BoundedInterval64
        (BoundedSigned64 F 571746046443w)
        (BoundedSigned64 F 571746046444w))
    else if positive = 13 ∧ negative = 0 ∧ denominator_predecessor = 499 then
      SOME (BoundedInterval64
        (BoundedSigned64 F 28587302322w)
        (BoundedSigned64 F 28587302323w))
    else NONE
End

Definition bounded_case16594_compile_poly_instruction_def:
  bounded_case16594_compile_poly_instruction instruction =
    case instruction of
    | BoundedPolyConstant positive negative denominator_predecessor =>
        (case bounded_case16594_constant64 positive negative
          denominator_predecessor of
         | NONE => NONE
         | SOME value => SOME (BoundedTaylor64Constant value))
    | BoundedPolyVariable index =>
        if index < 6 then SOME (BoundedTaylor64Variable index) else NONE
    | BoundedPolyNeg => SOME BoundedTaylor64Neg
    | BoundedPolyAdd => SOME BoundedTaylor64Add
    | BoundedPolyMul => SOME BoundedTaylor64Mul
    | BoundedPolySquare => SOME BoundedTaylor64Square
End

Definition bounded_case16594_compile_poly_def:
  bounded_case16594_compile_poly [] = SOME [] ∧
  bounded_case16594_compile_poly (instruction::instructions) =
    case bounded_case16594_compile_poly_instruction instruction of
    | NONE => NONE
    | SOME prepared =>
      case bounded_case16594_compile_poly instructions of
      | NONE => NONE
      | SOME rest => SOME (prepared::rest)
End

Definition bounded_case16594_compile_analytic_instruction_def:
  bounded_case16594_compile_analytic_instruction instruction =
    case instruction of
    | BoundedAnalyticPolynomial program =>
        (case bounded_case16594_compile_poly program of
         | NONE => NONE
         | SOME prepared =>
             SOME (BoundedAnalytic64Polynomial prepared))
    | BoundedAnalyticSqrt => SOME BoundedAnalytic64Sqrt
    | BoundedAnalyticNeg => SOME BoundedAnalytic64Neg
    | BoundedAnalyticAdd => SOME BoundedAnalytic64Add
    | BoundedAnalyticMul => SOME BoundedAnalytic64Mul
    | BoundedAnalyticSquare => SOME BoundedAnalytic64Square
    | BoundedAnalyticInverse => SOME BoundedAnalytic64Inverse
    | BoundedAnalyticAtan => SOME BoundedAnalytic64Atan
    | BoundedAnalyticPiHalf => SOME BoundedAnalytic64PiHalf
End

Definition bounded_case16594_compile_analytic_def:
  bounded_case16594_compile_analytic [] = SOME [] ∧
  bounded_case16594_compile_analytic (instruction::instructions) =
    case bounded_case16594_compile_analytic_instruction instruction of
    | NONE => NONE
    | SOME prepared =>
      case bounded_case16594_compile_analytic instructions of
      | NONE => NONE
      | SOME rest => SOME (prepared::rest)
End

Definition bounded_case16594_compile_specialized_instruction_def:
  bounded_case16594_compile_specialized_instruction instruction role =
    if ¬bounded_analytic_specialization_ok instruction role then NONE
    else
      case role of
      | BoundedAnalyticGeneral =>
          bounded_case16594_compile_analytic_instruction instruction
      | BoundedNegDeltaDerivative coordinate =>
          SOME (BoundedAnalytic64NegDeltaDerivative coordinate)
      | BoundedFourCoordinateDelta coordinate =>
          SOME (BoundedAnalytic64FourCoordinateDelta coordinate)
End

Definition bounded_case16594_compile_specialized_def:
  bounded_case16594_compile_specialized [] [] = SOME [] ∧
  bounded_case16594_compile_specialized
      (instruction::instructions) (role::roles) =
    (case bounded_case16594_compile_specialized_instruction instruction role of
     | NONE => NONE
     | SOME prepared =>
       case bounded_case16594_compile_specialized instructions roles of
       | NONE => NONE
       | SOME rest => SOME (prepared::rest)) ∧
  bounded_case16594_compile_specialized _ _ = NONE
End

Definition bounded_case16594_prepared_program_def:
  bounded_case16594_prepared_program =
    case bounded_case16594_compile_specialized bounded_case16594_program
      bounded_case16594_specializations of
    | NONE => []
    | SOME program => program
End

Definition bounded_case16594_prepared_program_ok_def:
  bounded_case16594_prepared_program_ok ⇔
    bounded_case16594_compile_specialized bounded_case16594_program
      bounded_case16594_specializations =
      SOME bounded_case16594_prepared_program ∧
    LENGTH bounded_case16594_prepared_program = 167
End

Theorem bounded_case16594_prepared_program_ok_value:
  bounded_case16594_prepared_program_ok
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_prepared_plan_rejects_aliases:
  bounded_case16594_constant64 13 0 500 = NONE ∧
  bounded_case16594_compile_poly_instruction
    (BoundedPolyVariable 6) = NONE ∧
  bounded_case16594_compile_analytic
    [BoundedAnalyticPolynomial
      [BoundedPolyConstant 1 0 1]] = NONE ∧
  bounded_case16594_compile_specialized_instruction
    (BoundedAnalyticPolynomial (REPLICATE 39 BoundedPolyNeg))
    (BoundedNegDeltaDerivative 3) = NONE ∧
  bounded_case16594_compile_specialized
    [BoundedAnalyticPolynomial
      (THE (bounded_analytic_specialization_program
        (BoundedNegDeltaDerivative 3)))] [] = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
