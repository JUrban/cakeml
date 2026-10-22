(*****************************************************************************
 * Semantic authentication for the bounded case-16594 delta specializations.
 *
 * The imported postfix programs are evaluated over the integers.  This is a
 * proof boundary, not a runtime recognizer: dispatch still requires exact
 * program identity, and these theorems establish what each accepted identity
 * denotes for every six-coordinate input.
 *****************************************************************************)
Theory compute_boundedDeltaSpecialization
Ancestors
  compute_boundedCase16594ProgramData integer
Libs
  bossLib intLib

Definition bounded_poly_int_stack_step_def:
  bounded_poly_int_stack_step environment instruction stack =
    case instruction of
    | BoundedPolyConstant positive negative denominator_predecessor =>
        if denominator_predecessor = 0 then
          SOME ((&positive - &negative)::stack)
        else NONE
    | BoundedPolyVariable variable =>
        (case oEL variable environment of
         | NONE => NONE
         | SOME value => SOME (value::stack))
    | BoundedPolyNeg =>
        (case stack of
         | value::rest => SOME ((-value)::rest)
         | _ => NONE)
    | BoundedPolyAdd =>
        (case stack of
         | right::left::rest => SOME ((left + right)::rest)
         | _ => NONE)
    | BoundedPolyMul =>
        (case stack of
         | right::left::rest => SOME ((left * right)::rest)
         | _ => NONE)
    | BoundedPolySquare =>
        (case stack of
         | value::rest => SOME ((value * value)::rest)
         | _ => NONE)
End

Definition bounded_poly_int_stack_def:
  bounded_poly_int_stack environment [] stack = SOME stack /\
  bounded_poly_int_stack environment (instruction::instructions) stack =
    case bounded_poly_int_stack_step environment instruction stack of
    | NONE => NONE
    | SOME next => bounded_poly_int_stack environment instructions next
End

Definition bounded_poly_int_eval_def:
  bounded_poly_int_eval program environment =
    case bounded_poly_int_stack environment program [] of
    | SOME [value] => SOME value
    | _ => NONE
End

Definition bounded_delta_value_def:
  bounded_delta_value x0 x1 x2 x3 x4 x5 =
    x0 * x3 * (-x0 + x1 + x2 - x3 + x4 + x5) +
    x1 * x4 * (x0 - x1 + x2 + x3 - x4 + x5) +
    x2 * x5 * (x0 + x1 - x2 + x3 + x4 - x5) -
    (x1 * x2 * x3 + x0 * x2 * x4 + x0 * x1 * x5 + x3 * x4 * x5)
End

Definition bounded_neg_delta_derivative3_def:
  bounded_neg_delta_derivative3 x0 x1 x2 x3 x4 x5 =
    -(-x0*x0 + x0*x1 + x0*x2 - 2*x0*x3 + x0*x4 + x0*x5 -
      x1*x2 + x1*x4 + x2*x5 - x4*x5)
End

Definition bounded_neg_delta_derivative4_def:
  bounded_neg_delta_derivative4 x0 x1 x2 x3 x4 x5 =
    -(x0*x1 - x0*x2 + x0*x3 - x1*x1 + x1*x2 + x1*x3 -
      2*x1*x4 + x1*x5 + x2*x5 - x3*x5)
End

Definition bounded_neg_delta_derivative5_def:
  bounded_neg_delta_derivative5 x0 x1 x2 x3 x4 x5 =
    -(-x0*x1 + x0*x2 + x0*x3 + x1*x2 + x1*x4 - x2*x2 +
      x2*x3 + x2*x4 - 2*x2*x5 - x3*x4)
End

(* Delta is quadratic in each of x3, x4, and x5.  These exact symmetric
   difference identities characterize the three named programs as the
   negatives of the corresponding formal derivatives, without dividing by
   the increment or adding a nonzero side condition. *)
Theorem bounded_neg_delta_derivative3_characterization:
  bounded_delta_value x0 x1 x2 (x3 + h) x4 x5 -
  bounded_delta_value x0 x1 x2 (x3 - h) x4 x5 =
  -2 * h * bounded_neg_delta_derivative3 x0 x1 x2 x3 x4 x5
Proof
  simp [bounded_delta_value_def, bounded_neg_delta_derivative3_def] \\
  INT_RING_TAC
QED

Theorem bounded_neg_delta_derivative4_characterization:
  bounded_delta_value x0 x1 x2 x3 (x4 + h) x5 -
  bounded_delta_value x0 x1 x2 x3 (x4 - h) x5 =
  -2 * h * bounded_neg_delta_derivative4 x0 x1 x2 x3 x4 x5
Proof
  simp [bounded_delta_value_def, bounded_neg_delta_derivative4_def] \\
  INT_RING_TAC
QED

Theorem bounded_neg_delta_derivative5_characterization:
  bounded_delta_value x0 x1 x2 x3 x4 (x5 + h) -
  bounded_delta_value x0 x1 x2 x3 x4 (x5 - h) =
  -2 * h * bounded_neg_delta_derivative5 x0 x1 x2 x3 x4 x5
Proof
  simp [bounded_delta_value_def, bounded_neg_delta_derivative5_def] \\
  INT_RING_TAC
QED

Theorem bounded_neg_delta_derivative3_program_semantics:
  bounded_poly_int_eval
    (THE (bounded_analytic_specialization_program
      (BoundedNegDeltaDerivative 3))) [x0;x1;x2;x3;x4;x5] =
  SOME (bounded_neg_delta_derivative3 x0 x1 x2 x3 x4 x5)
Proof
  simp [bounded_analytic_specialization_program_def,
        bounded_poly_int_eval_def, bounded_poly_int_stack_def,
        bounded_poly_int_stack_step_def,
        bounded_neg_delta_derivative3_def, listTheory.oEL_def] \\
  INT_RING_TAC
QED

Theorem bounded_neg_delta_derivative4_program_semantics:
  bounded_poly_int_eval
    (THE (bounded_analytic_specialization_program
      (BoundedNegDeltaDerivative 4))) [x0;x1;x2;x3;x4;x5] =
  SOME (bounded_neg_delta_derivative4 x0 x1 x2 x3 x4 x5)
Proof
  simp [bounded_analytic_specialization_program_def,
        bounded_poly_int_eval_def, bounded_poly_int_stack_def,
        bounded_poly_int_stack_step_def,
        bounded_neg_delta_derivative4_def, listTheory.oEL_def] \\
  INT_RING_TAC
QED

Theorem bounded_neg_delta_derivative5_program_semantics:
  bounded_poly_int_eval
    (THE (bounded_analytic_specialization_program
      (BoundedNegDeltaDerivative 5))) [x0;x1;x2;x3;x4;x5] =
  SOME (bounded_neg_delta_derivative5 x0 x1 x2 x3 x4 x5)
Proof
  simp [bounded_analytic_specialization_program_def,
        bounded_poly_int_eval_def, bounded_poly_int_stack_def,
        bounded_poly_int_stack_step_def,
        bounded_neg_delta_derivative5_def, listTheory.oEL_def] \\
  INT_RING_TAC
QED

Theorem bounded_four_coordinate_delta0_program_semantics:
  bounded_poly_int_eval
    (THE (bounded_analytic_specialization_program
      (BoundedFourCoordinateDelta 0))) [x0;x1;x2;x3;x4;x5] =
  SOME (4 * x0 * bounded_delta_value x0 x1 x2 x3 x4 x5)
Proof
  simp [bounded_analytic_specialization_program_def,
        bounded_poly_int_eval_def, bounded_poly_int_stack_def,
        bounded_poly_int_stack_step_def, bounded_delta_value_def,
        listTheory.oEL_def] \\
  INT_RING_TAC
QED

Theorem bounded_four_coordinate_delta1_program_semantics:
  bounded_poly_int_eval
    (THE (bounded_analytic_specialization_program
      (BoundedFourCoordinateDelta 1))) [x0;x1;x2;x3;x4;x5] =
  SOME (4 * x1 * bounded_delta_value x0 x1 x2 x3 x4 x5)
Proof
  simp [bounded_analytic_specialization_program_def,
        bounded_poly_int_eval_def, bounded_poly_int_stack_def,
        bounded_poly_int_stack_step_def, bounded_delta_value_def,
        listTheory.oEL_def] \\
  INT_RING_TAC
QED

Theorem bounded_four_coordinate_delta2_program_semantics:
  bounded_poly_int_eval
    (THE (bounded_analytic_specialization_program
      (BoundedFourCoordinateDelta 2))) [x0;x1;x2;x3;x4;x5] =
  SOME (4 * x2 * bounded_delta_value x0 x1 x2 x3 x4 x5)
Proof
  simp [bounded_analytic_specialization_program_def,
        bounded_poly_int_eval_def, bounded_poly_int_stack_def,
        bounded_poly_int_stack_step_def, bounded_delta_value_def,
        listTheory.oEL_def] \\
  INT_RING_TAC
QED

val _ = export_theory ();
