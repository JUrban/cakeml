(*****************************************************************************
 * Packet-parametric shape of the prepared case-10173 source programs.
 *
 * The registered source checker consumes a proper cv list of seven square-
 * root intervals.  This layer proves that successful preparation exhausts
 * that list and preserves the literal 54-instruction program shape.  These
 * facts are the structural inputs required by the memoized program runner;
 * they do not replay any numerical cell.
 *****************************************************************************)
Theory compute_registeredCase10173ProgramShapePacketEval
Ancestors
  compute_registeredCase10173ProgramPreparationPacketEval
Libs
  bossLib preamble

Definition registered_case10173_cv_list_zero_terminated_def:
  registered_case10173_cv_list_zero_terminated (Num n : cv) = (n = 0) /\
  registered_case10173_cv_list_zero_terminated (Pair item items) =
    registered_case10173_cv_list_zero_terminated items
End

Theorem registered_case10173_positive_q_interval_list_zero_terminated:
  !encoded intervals.
    bounded_object_positive_q_interval64_decimal_list encoded =
      SOME intervals ==>
    registered_case10173_cv_list_zero_terminated encoded
Proof
  ho_match_mp_tac
    compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_ind
  >> rw
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_def,
        registered_case10173_cv_list_zero_terminated_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_patch_instruction_preserves_exact_and_zero:
  !instruction program intervals remaining patched_instruction.
    registered_case10173_analytic_program_sqrt_data_exact_cv intervals
        (Pair instruction program) = Num 1 /\
    registered_case10173_cv_list_zero_terminated intervals /\
    registered_case10173_analytic_instruction_patch_sqrt_cv intervals
        instruction = Pair remaining patched_instruction ==>
    registered_case10173_analytic_program_sqrt_data_exact_cv remaining
        program = Num 1 /\
    registered_case10173_cv_list_zero_terminated remaining
Proof
  Cases_on `instruction`
  >> Cases_on `intervals`
  >> simp
       [compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_sqrt_data_exact_cv_def,
        compute_registeredCase10173AnalyticSqrtEvalTheory.registered_case10173_analytic_instruction_is_sqrt_cv_def,
        compute_registeredCase10173AnalyticSqrtEvalTheory.registered_case10173_analytic_instruction_patch_sqrt_cv_def,
        registered_case10173_cv_list_zero_terminated_def]
  >> every_case_tac
  >> gvs []
  >> rpt strip_tac
  >> gvs [registered_case10173_cv_list_zero_terminated_def]
QED

Theorem registered_case10173_patch_sqrt_zero_remainder_result:
  !program intervals remainder patched_program.
    registered_case10173_analytic_program_sqrt_data_exact_cv intervals
        program = Num 1 /\
    registered_case10173_cv_list_zero_terminated intervals /\
    registered_case10173_analytic_program_patch_sqrt_cv intervals program =
      Pair remainder patched_program ==>
    remainder = Num 0
Proof
  Induct_on `program`
  >- (rpt gen_tac
      >> Cases_on `intervals`
      >> simp
           [compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_sqrt_data_exact_cv_def,
            compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_def,
            registered_case10173_cv_list_zero_terminated_def]
      >> metis_tac [])
  >> rpt gen_tac
  >> qspecl_then [`intervals`,`program`] strip_assume_tac
       (GEN_ALL
         compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_instruction_patch_sqrt_cv_pair)
  >> qspecl_then [`program'`,`remaining`] strip_assume_tac
       compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_pair
  >> strip_tac
  >> imp_res_tac
       registered_case10173_patch_instruction_preserves_exact_and_zero
  >> qpat_x_assum
       `!intervals remainder patched_program. _`
       (qspecl_then [`remaining`,`remaining'`,`patched_program'`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> qpat_x_assum
       `registered_case10173_analytic_program_patch_sqrt_cv intervals
          (Pair program program') = Pair remainder patched_program`
       mp_tac
  >> PURE_ONCE_REWRITE_TAC
       [compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_def]
  >> asm_rewrite_tac [compute_execTheory.cv_case_def]
  >> strip_tac
  >> gvs [compute_execTheory.cv_11]
QED

Theorem registered_case10173_patch_sqrt_zero_remainder:
  registered_case10173_analytic_program_sqrt_data_exact_cv intervals
      program = Num 1 /\
  registered_case10173_cv_list_zero_terminated intervals ==>
  ?patched_program.
    registered_case10173_analytic_program_patch_sqrt_cv intervals program =
      Pair (Num 0) patched_program
Proof
  strip_tac
  >> qspecl_then [`program`,`intervals`] strip_assume_tac
       compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_pair
  >> imp_res_tac registered_case10173_patch_sqrt_zero_remainder_result
  >> gvs []
QED

Theorem registered_case10173_patch_sqrt_program_length:
  !program intervals remainder patched_program.
    registered_case10173_analytic_program_patch_sqrt_cv intervals program =
      Pair remainder patched_program ==>
    registered_case10173_cv_list_length patched_program =
      registered_case10173_cv_list_length program
Proof
  Induct_on `program`
  >- simp
       [compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> rpt gen_tac
  >> strip_tac
  >> qspecl_then [`intervals`,`program`] strip_assume_tac
       (GEN_ALL
         compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_instruction_patch_sqrt_cv_pair)
  >> qspecl_then [`program'`,`remaining`] strip_assume_tac
       compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_pair
  >> qpat_x_assum
       `!intervals remainder patched_program. _`
       (qspecl_then [`remaining`,`remaining'`,`patched_program'`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> qpat_x_assum
       `registered_case10173_analytic_program_patch_sqrt_cv intervals
          (Pair program program') = Pair remainder patched_program`
       mp_tac
  >> PURE_ONCE_REWRITE_TAC
       [compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_def]
  >> asm_rewrite_tac [compute_execTheory.cv_case_def]
  >> strip_tac
  >> gvs
       [compute_execTheory.cv_11,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
QED

Theorem registered_case10173_source_program_length:
  registered_case10173_cv_list_length
      registered_case10173_genuine_source_program = 54
Proof
  mp_tac
    compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_program_data_shape
  >> simp []
QED

Theorem registered_case10173_authenticated_source_program_shape:
  bounded_packed_chars_case10173_decimal_packet_ok packet /\
  bounded_case10173_decimal_packet_root_inputs_exact
    packet object_job root_record ==>
  ?box_sqrt_data center_sqrt_data boxes box_program center_program.
    object_job = Pair box_sqrt_data (Pair center_sqrt_data boxes) /\
    registered_case10173_analytic_program_patch_sqrt_cv box_sqrt_data
      registered_case10173_genuine_source_program =
        Pair (Num 0) box_program /\
    registered_case10173_analytic_program_patch_sqrt_cv center_sqrt_data
      registered_case10173_genuine_source_program =
        Pair (Num 0) center_program /\
    registered_case10173_cv_list_length box_program = 54 /\
    registered_case10173_cv_list_length center_program = 54
Proof
  strip_tac
  >> drule
       compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_authenticated_source_program_preparation
  >> simp []
  >> disch_then (qspecl_then [`root_record`,`object_job`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> fs
       [compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_root_inputs_exact_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_input_binding_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_auxiliary_binding_def]
  >> imp_res_tac
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_binding_components
  >> gvs [compute_execTheory.cv_11]
  >> imp_res_tac
       registered_case10173_positive_q_interval_list_zero_terminated
  >> imp_res_tac
       compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_packet_sqrt_root_lengths
  >> imp_res_tac
       compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_positive_q_interval_list_length
  >> subgoal `registered_case10173_cv_list_length box_sqrt_data = 7`
  >- gvs []
  >> subgoal `registered_case10173_cv_list_length center_sqrt_data = 7`
  >- gvs []
  >> imp_res_tac
       compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_source_program_seven_sqrt_data_exact
  >> imp_res_tac registered_case10173_patch_sqrt_zero_remainder_result
  >> imp_res_tac registered_case10173_patch_sqrt_program_length
  >> metis_tac [registered_case10173_source_program_length]
QED

val _ = export_theory ();
