(*****************************************************************************
 * Genuine polynomial-only case16594 batch boundary.
 *
 * This focused DEVELOPMENT runner selects the authenticated 85-instruction
 * polynomial at outer-plan index 35 and evaluates it on all prepared cells.
 * It intentionally stops before the first scalar certificate boundary.  The
 * result count is useful for exercising the real fixed-word Taylor path while
 * the typed scalar certificate fixture is assembled independently.
 *****************************************************************************)
Theory compute_boundedCase16594PolynomialBatch
Ancestors
  compute_boundedCase16594PreparedPlan
  compute_boundedCase16594PreparedInput
Libs
  bossLib preamble wordsLib

Definition bounded_case16594_analytic64_nth_def:
  bounded_case16594_analytic64_nth [] index = NONE ∧
  bounded_case16594_analytic64_nth (instruction::instructions) 0 =
    SOME instruction ∧
  bounded_case16594_analytic64_nth (instruction::instructions) (SUC index) =
    bounded_case16594_analytic64_nth instructions index
End

Definition bounded_case16594_eval_polynomial_def:
  bounded_case16594_eval_polynomial instruction input =
    case (instruction,input) of
    | (BoundedAnalytic64Polynomial program,
       BoundedCase16594PreparedInput center_environment box_environment
         radii center_sqrt box_sqrt) =>
        bounded_taylor64_program_eval radii center_environment
          box_environment program
    | _ => NONE
End

Definition bounded_case16594_eval_polynomial_batch_def:
  bounded_case16594_eval_polynomial_batch instruction [] count = SOME count ∧
  bounded_case16594_eval_polynomial_batch instruction (input::inputs) count =
    case bounded_case16594_eval_polynomial instruction input of
    | NONE => NONE
    | SOME result =>
        bounded_case16594_eval_polynomial_batch instruction inputs
          (SUC count)
End

Definition bounded_case16594_polynomial35_batch_def:
  bounded_case16594_polynomial35_batch =
    case bounded_case16594_analytic64_nth
      bounded_case16594_prepared_program 35 of
    | NONE => NONE
    | SOME instruction =>
        bounded_case16594_eval_polynomial_batch instruction
          bounded_case16594_prepared_inputs 0
End

Definition bounded_case16594_polynomial35_batch_ok_def:
  bounded_case16594_polynomial35_batch_ok ⇔
    bounded_case16594_polynomial35_batch = SOME 875
End

Theorem bounded_case16594_polynomial35_source_shape:
  (case bounded_case16594_analytic64_nth
      bounded_case16594_prepared_program 35 of
   | SOME (BoundedAnalytic64Polynomial program) => LENGTH program = 85
   | _ => F)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_eval_polynomial_some:
  bounded_case16594_eval_polynomial instruction input = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  Cases_on `instruction` >> Cases_on `input`
  >> rw [bounded_case16594_eval_polynomial_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorProgramTheory.bounded_taylor64_program_eval_some
QED

val _ = export_theory ();
