(*****************************************************************************
 * Fail-closed decoding of bounded analytic source programs from cv data.
 *
 * This is the common source-descriptor boundary for data-driven nonlinear
 * checkers.  It follows the ordinary CakeML constructor representation used
 * by the Flyspeck source reifier, including the historical placeholder carried
 * by square-root instructions.  No case number, basename, or instruction
 * position is used as source authority.
 *****************************************************************************)
Theory compute_boundedAnalyticProgramCV
Ancestors
  compute compute_boundedCase16594ProgramData
Libs
  bossLib preamble

Definition bounded_rational_of_cv_def:
  bounded_rational_of_cv value =
    case value of
    | Pair (Pair (Num positive) (Num negative))
        (Num denominator_predecessor) =>
        SOME (positive,negative,denominator_predecessor)
    | _ => NONE
End

Definition bounded_poly_instruction_of_cv_def:
  bounded_poly_instruction_of_cv value =
    case value of
    | Num opcode =>
        if opcode = 2 then SOME BoundedPolyNeg
        else if opcode = 3 then SOME BoundedPolyAdd
        else if opcode = 4 then SOME BoundedPolyMul
        else if opcode = 5 then SOME BoundedPolySquare
        else NONE
    | Pair (Num tag) payload =>
        if tag = 0 then
          (case bounded_rational_of_cv payload of
           | NONE => NONE
           | SOME (positive,negative,denominator_predecessor) =>
               SOME (BoundedPolyConstant positive negative
                 denominator_predecessor))
        else if tag = 1 then
          (case payload of
           | Num index => SOME (BoundedPolyVariable index)
           | _ => NONE)
        else NONE
    | _ => NONE
End

Definition bounded_poly_program_of_cv_def:
  bounded_poly_program_of_cv (Num 0) = SOME [] /\
  bounded_poly_program_of_cv (Num (SUC tail)) = NONE /\
  bounded_poly_program_of_cv (Pair instruction rest) =
    case bounded_poly_instruction_of_cv instruction of
    | NONE => NONE
    | SOME decoded =>
        case bounded_poly_program_of_cv rest of
        | NONE => NONE
        | SOME suffix => SOME (decoded::suffix)
End

Definition bounded_sqrt_placeholder_cv_def:
  bounded_sqrt_placeholder_cv =
    Pair (Pair (Pair (Num 0) (Num 0)) (Num 0))
      (Pair (Pair (Num 100) (Num 0)) (Num 0))
End

Definition bounded_analytic_instruction_of_cv_def:
  bounded_analytic_instruction_of_cv value =
    case value of
    | Num opcode =>
        if opcode = 2 then SOME BoundedAnalyticNeg
        else if opcode = 3 then SOME BoundedAnalyticAdd
        else if opcode = 4 then SOME BoundedAnalyticMul
        else if opcode = 5 then SOME BoundedAnalyticSquare
        else if opcode = 6 then SOME BoundedAnalyticInverse
        else if opcode = 7 then SOME BoundedAnalyticAtan
        else if opcode = 8 then SOME BoundedAnalyticPiHalf
        else NONE
    | Pair (Num tag) payload =>
        if tag = 0 then
          (case bounded_poly_program_of_cv payload of
           | NONE => NONE
           | SOME program => SOME (BoundedAnalyticPolynomial program))
        else if tag = 1 /\ payload = bounded_sqrt_placeholder_cv then
          SOME BoundedAnalyticSqrt
        else NONE
    | _ => NONE
End

Definition bounded_analytic_program_of_cv_def:
  bounded_analytic_program_of_cv (Num 0) = SOME [] /\
  bounded_analytic_program_of_cv (Num (SUC tail)) = NONE /\
  bounded_analytic_program_of_cv (Pair instruction rest) =
    case bounded_analytic_instruction_of_cv instruction of
    | NONE => NONE
    | SOME decoded =>
        case bounded_analytic_program_of_cv rest of
        | NONE => NONE
        | SOME suffix => SOME (decoded::suffix)
End

Theorem bounded_analytic_program_of_cv_examples:
  bounded_analytic_program_of_cv
    (Pair
      (Pair (Num 0)
        (Pair (Pair (Num 1) (Num 4))
          (Pair (Num 5) (Num 0))))
      (Pair (Pair (Num 1) bounded_sqrt_placeholder_cv)
        (Pair (Num 7) (Num 0)))) =
    SOME
      [BoundedAnalyticPolynomial
        [BoundedPolyVariable 4;BoundedPolySquare];
       BoundedAnalyticSqrt;
       BoundedAnalyticAtan]
Proof
  EVAL_TAC
QED

Theorem bounded_analytic_program_of_cv_rejects_aliases:
  bounded_analytic_program_of_cv (Num 1) = NONE /\
  bounded_analytic_program_of_cv
    (Pair (Pair (Num 9) (Num 0)) (Num 0)) = NONE /\
  bounded_analytic_program_of_cv
    (Pair (Pair (Num 1) (Num 0)) (Num 0)) = NONE /\
  bounded_analytic_program_of_cv
    (Pair (Pair (Num 0)
      (Pair (Pair (Num 1) (Pair (Num 4) (Num 0))) (Num 0)))
      (Num 0)) = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
