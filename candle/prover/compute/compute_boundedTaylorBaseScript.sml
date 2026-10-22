(*****************************************************************************
 * Constant and coordinate leaves for compact Taylor programs.
 *
 * Constants are supplied as authenticated fixed-scale intervals.  Variables
 * select the corresponding center and whole-box input intervals and receive
 * the exact six-dimensional unit gradient and zero Hessian.  Source-to-data
 * correspondence is intentionally left to the enclosing authenticated plan.
 *****************************************************************************)
Theory compute_boundedTaylorBase
Ancestors
  compute_boundedTaylorMul
Libs
  bossLib preamble

Definition bounded_interval64_zeros_def:
  bounded_interval64_zeros 0 = [] ∧
  bounded_interval64_zeros (SUC count) =
    bounded_interval64_zero::bounded_interval64_zeros count
End

Definition bounded_interval64_nth_def:
  bounded_interval64_nth [] index = NONE ∧
  bounded_interval64_nth (value::rest) 0 = SOME value ∧
  bounded_interval64_nth (value::rest) (SUC index) =
    bounded_interval64_nth rest index
End

Definition bounded_interval64_unit_vector_def:
  bounded_interval64_unit_vector index =
    if index < 6 then
      SOME
        (GENLIST
          (λposition.
             if position = index then bounded_atan_one
             else bounded_interval64_zero)
          6)
    else NONE
End

Definition bounded_taylor64_constant_def:
  bounded_taylor64_constant value =
    bounded_taylor64_make T value
      (bounded_interval64_zeros 6) value
      (bounded_interval64_zeros 6)
      (bounded_interval64_zeros 21)
End

Definition bounded_taylor64_variable_def:
  bounded_taylor64_variable center_environment box_environment index =
    if LENGTH center_environment ≠ 6 ∨ LENGTH box_environment ≠ 6
    then NONE
    else
      case bounded_interval64_unit_vector index of
      | NONE => NONE
      | SOME gradient =>
        case bounded_interval64_nth center_environment index of
        | NONE => NONE
        | SOME center_value =>
          case bounded_interval64_nth box_environment index of
          | NONE => NONE
          | SOME box_value =>
              bounded_taylor64_make T center_value gradient
                box_value gradient (bounded_interval64_zeros 21)
End

Theorem bounded_taylor64_constant_some:
  bounded_taylor64_constant value = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_constant_def]
  >> imp_res_tac
       compute_boundedTaylorStateTheory.bounded_taylor64_make_some
QED

Theorem bounded_taylor64_variable_some:
  bounded_taylor64_variable center_environment box_environment index =
    SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_variable_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorStateTheory.bounded_taylor64_make_some
QED

Theorem bounded_taylor64_base_closed_tests:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let unit0 = one::REPLICATE 5 bounded_interval64_zero in
  bounded_taylor64_constant one =
    SOME (BoundedTaylor64 T one zeros6 one zeros6 zeros21) ∧
  bounded_taylor64_variable (REPLICATE 6 one) (REPLICATE 6 one) 0 =
    SOME (BoundedTaylor64 T one unit0 one unit0 zeros21) ∧
  bounded_taylor64_variable (REPLICATE 6 one) (REPLICATE 6 one) 6 = NONE ∧
  bounded_taylor64_variable [one] (REPLICATE 6 one) 0 = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
