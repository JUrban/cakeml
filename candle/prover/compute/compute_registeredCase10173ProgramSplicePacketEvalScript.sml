(*****************************************************************************
 * Packet-parametric shape of the historical source-program splice.
 *
 * The registered checker replaces the eight-instruction historical
 * subexpression at position 31 by one authenticated opcode-9 item.  These
 * lemmas prove the resulting 54 - 8 + 1 = 47 instruction shape for arbitrary
 * prepared programs; no numerical instruction or certificate cell is run.
 *****************************************************************************)
Theory compute_registeredCase10173ProgramSplicePacketEval
Ancestors
  compute_registeredCase10173ProgramShapePacketEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_cv_drop_length:
  !count program.
    count <= registered_case10173_cv_list_length program ==>
    registered_case10173_cv_list_length
      (registered_case10173_cv_drop count program) =
    registered_case10173_cv_list_length program - count
Proof
  Induct
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def]
  >> Cases_on `program`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
QED

Theorem registered_case10173_hist_splice_length:
  !count program.
    count + 8 <= registered_case10173_cv_list_length program ==>
    registered_case10173_cv_list_length
      (registered_case10173_hist_splice_cv count program) =
    registered_case10173_cv_list_length program - 7
Proof
  Induct
  >- (rpt gen_tac
      >> strip_tac
      >> simp
           [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_hist_splice_cv_def,
            compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def,
            registered_case10173_cv_drop_length]
      >> intLib.ARITH_TAC)
  >> Cases_on `program`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_hist_splice_cv_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_hist_splice_cv_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> strip_tac
  >> first_x_assum drule
  >> strip_tac
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_prepared_program_splice_length:
  registered_case10173_cv_list_length program = 54 ==>
  registered_case10173_cv_list_length
    (registered_case10173_hist_splice_cv 31 program) = 47
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL [`31`,`program`]
         registered_case10173_hist_splice_length)
  >> impl_tac >- simp []
  >> simp []
QED

Theorem registered_case10173_authenticated_source_program_splice_shape:
  bounded_packed_chars_case10173_decimal_packet_ok packet /\
  bounded_case10173_decimal_packet_root_inputs_exact
    packet object_job root_record ==>
  ?box_sqrt_data center_sqrt_data boxes box_program center_program
   spliced_box_program spliced_center_program.
    object_job = Pair box_sqrt_data (Pair center_sqrt_data boxes) /\
    registered_case10173_analytic_program_patch_sqrt_cv box_sqrt_data
      registered_case10173_genuine_source_program =
        Pair (Num 0) box_program /\
    registered_case10173_analytic_program_patch_sqrt_cv center_sqrt_data
      registered_case10173_genuine_source_program =
        Pair (Num 0) center_program /\
    spliced_box_program =
      registered_case10173_hist_splice_cv 31 box_program /\
    spliced_center_program =
      registered_case10173_hist_splice_cv 31 center_program /\
    registered_case10173_cv_list_length spliced_box_program = 47 /\
    registered_case10173_cv_list_length spliced_center_program = 47
Proof
  strip_tac
  >> drule
       compute_registeredCase10173ProgramShapePacketEvalTheory.registered_case10173_authenticated_source_program_shape
  >> simp []
  >> disch_then (qspecl_then [`root_record`,`object_job`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> metis_tac [registered_case10173_prepared_program_splice_length]
QED

val _ = export_theory ();
