(*****************************************************************************
 * Packet-parametric decomposition of the historical source program.
 *
 * The prepared 47-instruction program consists of an ordinary 31-step
 * prefix, the authenticated opcode-9 historical item, and an ordinary
 * 15-step suffix.  This theory exposes that decomposition and proves a
 * continuation law for the memoized runner, so the two ordinary fragments
 * can be refined independently of the expensive historical calculation.
 *****************************************************************************)
Theory compute_registeredCase10173ProgramSplitPacketEval
Ancestors
  compute_registeredCase10173ProgramSplicePacketEval
  compute_registeredCase10173HistProgramMemoEval
Libs
  bossLib preamble intLib

Definition registered_case10173_cv_take_def:
  registered_case10173_cv_take 0 program = Num 0 /\
  registered_case10173_cv_take (SUC count) (Pair instruction program) =
    Pair instruction (registered_case10173_cv_take count program) /\
  registered_case10173_cv_take (SUC count) (Num n) = Num 0
End

Definition registered_case10173_cv_append_def:
  registered_case10173_cv_append (Num n : cv) suffix = suffix /\
  registered_case10173_cv_append (Pair instruction program) suffix =
    Pair instruction (registered_case10173_cv_append program suffix)
End

Theorem registered_case10173_cv_take_length:
  !count program.
    registered_case10173_cv_list_length
      (registered_case10173_cv_take count program) =
    MIN count (registered_case10173_cv_list_length program)
Proof
  Induct
  >- simp
       [registered_case10173_cv_take_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> Cases_on `program`
  >> simp
       [registered_case10173_cv_take_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def,
        MIN_DEF]
QED

Theorem registered_case10173_cv_append_take_drop:
  !count program.
    count <= registered_case10173_cv_list_length program ==>
    registered_case10173_cv_append
      (registered_case10173_cv_take count program)
      (registered_case10173_cv_drop count program) = program
Proof
  Induct
  >- simp
       [registered_case10173_cv_take_def,
        registered_case10173_cv_append_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def]
  >> Cases_on `program`
  >> simp
       [registered_case10173_cv_take_def,
        registered_case10173_cv_append_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
QED

Theorem registered_case10173_cv_drop_num:
  !drop_count n.
    registered_case10173_cv_drop drop_count (Num n) = Num n
Proof
  Cases_on `drop_count`
  >> simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def]
QED

Theorem registered_case10173_cv_drop_add:
  !left_count right_count program.
    registered_case10173_cv_drop (left_count + right_count) program =
    registered_case10173_cv_drop right_count
      (registered_case10173_cv_drop left_count program)
Proof
  Induct_on `left_count`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def]
  >> rpt gen_tac
  >> Cases_on `program`
  >- simp [registered_case10173_cv_drop_num]
  >> PURE_REWRITE_TAC
       [ADD_CLAUSES,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def]
  >> first_x_assum irule
QED

Theorem registered_case10173_hist_program_run_memo_append:
  !center_prefix box_prefix stack.
    registered_case10173_cv_list_length center_prefix =
      registered_case10173_cv_list_length box_prefix ==>
    registered_case10173_hist_program_run_memo fuel
      center_boxes boxes radii roots item
      (registered_case10173_cv_append center_prefix center_suffix)
      (registered_case10173_cv_append box_prefix box_suffix) stack =
    case registered_case10173_hist_program_run_memo fuel
      center_boxes boxes radii roots item center_prefix box_prefix stack of
    | NONE => NONE
    | SOME middle_stack =>
        registered_case10173_hist_program_run_memo fuel
          center_boxes boxes radii roots item
          center_suffix box_suffix middle_stack
Proof
  Induct_on `center_prefix`
  >- (rpt gen_tac
      >> Cases_on `box_prefix`
      >> simp
           [registered_case10173_cv_append_def,
            compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def,
            compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_hist_program_run_memo_def])
  >> rpt gen_tac
  >> Cases_on `box_prefix`
  >- simp
       [registered_case10173_cv_append_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> simp
       [registered_case10173_cv_append_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def,
        compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_hist_program_run_memo_def]
  >> strip_tac
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_hist_program_run_memo_split:
  split_count <= registered_case10173_cv_list_length center_program /\
  split_count <= registered_case10173_cv_list_length box_program ==>
  registered_case10173_hist_program_run_memo fuel
      center_boxes boxes radii roots item center_program box_program stack =
    case registered_case10173_hist_program_run_memo fuel
      center_boxes boxes radii roots item
      (registered_case10173_cv_take split_count center_program)
      (registered_case10173_cv_take split_count box_program) stack of
    | NONE => NONE
    | SOME middle_stack =>
        registered_case10173_hist_program_run_memo fuel
          center_boxes boxes radii roots item
          (registered_case10173_cv_drop split_count center_program)
          (registered_case10173_cv_drop split_count box_program) middle_stack
Proof
  strip_tac
  >> mp_tac
    (INST
      [``center_suffix:cv`` |->
         ``registered_case10173_cv_drop split_count center_program``,
       ``box_suffix:cv`` |->
         ``registered_case10173_cv_drop split_count box_program``]
      (SPECL
        [``registered_case10173_cv_take split_count center_program``,
         ``registered_case10173_cv_take split_count box_program``,
         ``stack:cv``]
        registered_case10173_hist_program_run_memo_append))
  >> simp
       [registered_case10173_cv_take_length,
        registered_case10173_cv_append_take_drop,MIN_DEF]
QED

Theorem registered_case10173_cv_drop_hist_splice:
  !count program.
    count <= registered_case10173_cv_list_length program ==>
    registered_case10173_cv_drop count
      (registered_case10173_hist_splice_cv count program) =
    Pair (Num 9)
      (registered_case10173_cv_drop 8
        (registered_case10173_cv_drop count program))
Proof
  Induct
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_hist_splice_cv_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def]
  >> Cases_on `program`
  >> simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_hist_splice_cv_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
QED

Theorem registered_case10173_prepared_program_splice_split:
  registered_case10173_cv_list_length program = 54 ==>
  let spliced = registered_case10173_hist_splice_cv 31 program in
    registered_case10173_cv_list_length
      (registered_case10173_cv_take 31 spliced) = 31 /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31 spliced) =
        Pair (Num 9) (Num 0) /\
    registered_case10173_cv_list_length
      (registered_case10173_cv_drop 32 spliced) = 15
Proof
  strip_tac
  >> simp
       [registered_case10173_prepared_program_splice_length,
        registered_case10173_cv_take_length]
  >> subgoal
       `registered_case10173_cv_drop 31
          (registered_case10173_hist_splice_cv 31 program) =
        Pair (Num 9)
          (registered_case10173_cv_drop 8
            (registered_case10173_cv_drop 31 program))`
  >- (irule registered_case10173_cv_drop_hist_splice
      >> simp [])
  >> conj_tac
  >- (qpat_x_assum
        `registered_case10173_cv_drop 31 _ = _`
        (fn th => once_rewrite_tac [th])
      >> EVAL_TAC)
  >> mp_tac
       (Q.SPECL
         [`32`,`registered_case10173_hist_splice_cv 31 program`]
         compute_registeredCase10173ProgramSplicePacketEvalTheory.registered_case10173_cv_drop_length)
  >> simp [registered_case10173_prepared_program_splice_length]
QED

Theorem registered_case10173_authenticated_source_program_split_shape:
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
    registered_case10173_cv_list_length
      (registered_case10173_cv_take 31 spliced_box_program) = 31 /\
    registered_case10173_cv_list_length
      (registered_case10173_cv_take 31 spliced_center_program) = 31 /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31 spliced_box_program) =
        Pair (Num 9) (Num 0) /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31 spliced_center_program) =
        Pair (Num 9) (Num 0) /\
    registered_case10173_cv_list_length
      (registered_case10173_cv_drop 32 spliced_box_program) = 15 /\
    registered_case10173_cv_list_length
      (registered_case10173_cv_drop 32 spliced_center_program) = 15
Proof
  strip_tac
  >> drule
       compute_registeredCase10173ProgramShapePacketEvalTheory.registered_case10173_authenticated_source_program_shape
  >> simp []
  >> disch_then (qspecl_then [`root_record`,`object_job`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> imp_res_tac registered_case10173_prepared_program_splice_split
  >> metis_tac []
QED

val _ = export_theory ();
