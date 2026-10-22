(*****************************************************************************
 * Streaming genuine case16594 polynomial batch.
 *
 * Unlike the first batch probe, this runner obtains and prepares exactly one
 * authenticated cell at a time.  The complete 875-row fixture is therefore
 * represented in code by an indexed accessor, not as one eagerly allocated
 * ML value retained across evaluation.
 *****************************************************************************)
Theory compute_boundedCase16594StreamingPolynomialBatch
Ancestors
  compute_boundedCase16594PreparedPlan
  compute_boundedCase16594PreparedInput
  compute_boundedCase16594StreamingInputData
Libs
  bossLib preamble wordsLib

Definition bounded_case16594_streaming_analytic64_nth_def:
  bounded_case16594_streaming_analytic64_nth [] index = NONE ∧
  bounded_case16594_streaming_analytic64_nth
      (instruction::instructions) 0 = SOME instruction ∧
  bounded_case16594_streaming_analytic64_nth
      (instruction::instructions) (SUC index) =
    bounded_case16594_streaming_analytic64_nth instructions index
End

Definition bounded_case16594_eval_streaming_polynomial_def:
  bounded_case16594_eval_streaming_polynomial instruction input =
    case (instruction,input) of
    | (BoundedAnalytic64Polynomial program,
       BoundedCase16594StreamingInput box centers radii) =>
        if LENGTH box = 6 ∧ LENGTH centers = 6 ∧ LENGTH radii = 6 then
          bounded_taylor64_program_eval radii
            (bounded_case16594_positive_intervals centers)
            (bounded_case16594_positive_intervals box) program
        else NONE
    | _ => NONE
End

Definition bounded_case16594_eval_streaming_polynomial_batch_def:
  bounded_case16594_eval_streaming_polynomial_batch
      instruction 0 count = SOME count ∧
  bounded_case16594_eval_streaming_polynomial_batch
      instruction (SUC remaining) count =
    (case bounded_case16594_streaming_input_at (875 - SUC remaining) of
     | NONE => NONE
     | SOME input =>
       case bounded_case16594_eval_streaming_polynomial instruction input of
       | NONE => NONE
       | SOME result =>
         bounded_case16594_eval_streaming_polynomial_batch instruction
           remaining (SUC count))
End

Definition bounded_case16594_streaming_polynomial35_batch_def:
  bounded_case16594_streaming_polynomial35_batch =
    case bounded_case16594_streaming_analytic64_nth
      bounded_case16594_prepared_program 35 of
    | NONE => NONE
    | SOME instruction =>
        bounded_case16594_eval_streaming_polynomial_batch instruction 875 0
End

Definition bounded_case16594_streaming_polynomial35_batch_ok_def:
  bounded_case16594_streaming_polynomial35_batch_ok ⇔
    bounded_case16594_streaming_polynomial35_batch = SOME 875
End

Theorem bounded_case16594_streaming_polynomial35_source_shape:
  (case bounded_case16594_streaming_analytic64_nth
      bounded_case16594_prepared_program 35 of
   | SOME (BoundedAnalytic64Polynomial program) => LENGTH program = 85
   | _ => F)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_eval_streaming_polynomial_some:
  bounded_case16594_eval_streaming_polynomial instruction input =
      SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  Cases_on `instruction` >> Cases_on `input`
  >> rw [bounded_case16594_eval_streaming_polynomial_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorProgramTheory.bounded_taylor64_program_eval_some
QED

val _ = export_theory ();
