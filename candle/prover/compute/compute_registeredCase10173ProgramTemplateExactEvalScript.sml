(*****************************************************************************
 * Reassemble authenticated source-program template fragments.
 *
 * The template theorem exposes the 31-instruction prefix, one opcode-9
 * instruction, and the 15-instruction suffix separately.  The source trace
 * consumes their complete zero-terminated append, so record that exact
 * identity once for arbitrary prepared programs.
 *****************************************************************************)
Theory compute_registeredCase10173ProgramTemplateExactEval
Ancestors
  compute_registeredCase10173ProgramTemplatePacketEval
Libs
  bossLib preamble

Theorem registered_case10173_program_from_template_fragments:
  registered_case10173_cv_list_length program = 47 /\
  registered_case10173_cv_take 31 program = prefix /\
  registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31 program) = Pair (Num 9) (Num 0) /\
  registered_case10173_cv_drop 32 program = suffix ==>
  program =
    registered_case10173_cv_append prefix (Pair (Num 9) suffix)
Proof
  strip_tac
  >> subgoal
       `registered_case10173_cv_drop 1
          (registered_case10173_cv_drop 31 program) = suffix`
  >- (once_rewrite_tac
        [GSYM
          (Q.SPECL [`31`,`1`,`program`]
            compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_drop_add)]
      >> simp [])
  >> subgoal
       `registered_case10173_cv_drop 31 program = Pair (Num 9) suffix`
  >- (mp_tac
        (Q.SPECL
          [`1`,`registered_case10173_cv_drop 31 program`]
          compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_append_take_drop)
      >> impl_tac
      >- (mp_tac
            (Q.SPECL [`31`,`program`]
              compute_registeredCase10173ProgramSplicePacketEvalTheory.registered_case10173_cv_drop_length)
          >> simp [])
      >> simp
           [compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_append_def])
  >> mp_tac
       (Q.SPECL [`31`,`program`]
         compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_append_take_drop)
  >> impl_tac >- simp []
  >> metis_tac []
QED

Theorem registered_case10173_authenticated_source_programs_exact:
  bounded_packed_chars_case10173_decimal_packet_ok packet /\
  bounded_case10173_decimal_packet_root_inputs_exact
    packet object_job root_record ==>
  ?box_sqrt_data center_sqrt_data boxes box_program center_program
   box0 box1 box2 box3 box4 box5 box6
   center0 center1 center2 center3 center4 center5 center6.
    object_job = Pair box_sqrt_data (Pair center_sqrt_data boxes) /\
    box_sqrt_data = registered_case10173_cv_of_list
      [box0;box1;box2;box3;box4;box5;box6] /\
    center_sqrt_data = registered_case10173_cv_of_list
      [center0;center1;center2;center3;center4;center5;center6] /\
    registered_case10173_analytic_program_patch_sqrt_cv box_sqrt_data
      registered_case10173_genuine_source_program =
        Pair (Num 0) box_program /\
    registered_case10173_analytic_program_patch_sqrt_cv center_sqrt_data
      registered_case10173_genuine_source_program =
        Pair (Num 0) center_program /\
    registered_case10173_hist_splice_cv 31 box_program =
      registered_case10173_cv_append
        (registered_case10173_source_prefix_template
          box0 box1 box2 box3 box4 box5)
        (Pair (Num 9) registered_case10173_source_suffix_template) /\
    registered_case10173_hist_splice_cv 31 center_program =
      registered_case10173_cv_append
        (registered_case10173_source_prefix_template
          center0 center1 center2 center3 center4 center5)
        (Pair (Num 9) registered_case10173_source_suffix_template) /\
    registered_case10173_cv_list_length box_program = 54 /\
    registered_case10173_cv_list_length center_program = 54
Proof
  strip_tac
  >> drule
       compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_authenticated_source_program_templates
  >> simp []
  >> disch_then (qspecl_then [`root_record`,`object_job`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> drule
       compute_registeredCase10173ProgramShapePacketEvalTheory.registered_case10173_authenticated_source_program_shape
  >> simp []
  >> disch_then (qspecl_then [`root_record`,`object_job`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> gvs []
  >> imp_res_tac
       compute_registeredCase10173ProgramSplicePacketEvalTheory.registered_case10173_prepared_program_splice_length
  >> imp_res_tac registered_case10173_program_from_template_fragments
  >> metis_tac []
QED

val _ = export_theory ();
