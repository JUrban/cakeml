(*****************************************************************************
 * Exact prepared-program identity for the genuine first fast NL job.
 *****************************************************************************)
Theory compute_registeredCase10173FastGenuineProgramIdentity
Ancestors
  compute_registeredCase10173FastGenuineContractData
  compute_registeredCase10173FastGenuinePacketData
  compute_registeredCase10173SourceProgramIdentity
Libs
  bossLib preamble

Theorem registered_case10173_first_job_root_inputs_exact:
  bounded_case10173_decimal_packet_root_inputs_exact
    bounded_case10173_decimal_packet0_source_aligned
    registered_case10173_first_job_object_job
    registered_case10173_first_job_roots
Proof
  mp_tac
    compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet0_source_aligned_root_inputs_exact
  >> strip_tac
  >> mp_tac
       compute_registeredCase10173FastGenuineContractDataTheory.registered_case10173_first_job_object_job_exact
  >> strip_tac
  >> gvs []
QED

Theorem registered_case10173_genuine_spliced_programs_exact:
  ?box0 box1 box2 box3 box4 box5 box6
   center0 center1 center2 center3 center4 center5 center6.
    registered_case10173_first_job_box_sqrt_data =
      registered_case10173_cv_of_list
        [box0;box1;box2;box3;box4;box5;box6] /\
    registered_case10173_first_job_center_sqrt_data =
      registered_case10173_cv_of_list
        [center0;center1;center2;center3;center4;center5;center6] /\
    registered_case10173_genuine_spliced_box_program =
      registered_case10173_cv_append
        (registered_case10173_source_prefix_template
          box0 box1 box2 box3 box4 box5)
        (Pair (Num 9) registered_case10173_source_suffix_template) /\
    registered_case10173_genuine_spliced_center_program =
      registered_case10173_cv_append
        (registered_case10173_source_prefix_template
          center0 center1 center2 center3 center4 center5)
        (Pair (Num 9) registered_case10173_source_suffix_template)
Proof
  mp_tac
    (MATCH_MP
      compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_authenticated_source_program_templates
      (CONJ
        compute_registeredCase10173FastGenuinePacketDataTheory.registered_case10173_source_aligned_decimal_packet_ok
        registered_case10173_first_job_root_inputs_exact))
  >> strip_tac
  >> `registered_case10173_first_job_box_sqrt_data = box_sqrt_data /\
      registered_case10173_first_job_center_sqrt_data = center_sqrt_data` by
       simp
         [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_first_job_box_sqrt_data_def,
          compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_first_job_center_sqrt_data_def,
          compute_registeredCase10173FastGenuineContractDataTheory.registered_case10173_first_job_object_job_exact]
  >> qexists_tac `box0`
  >> qexists_tac `box1`
  >> qexists_tac `box2`
  >> qexists_tac `box3`
  >> qexists_tac `box4`
  >> qexists_tac `box5`
  >> qexists_tac `box6`
  >> qexists_tac `center0`
  >> qexists_tac `center1`
  >> qexists_tac `center2`
  >> qexists_tac `center3`
  >> qexists_tac `center4`
  >> qexists_tac `center5`
  >> qexists_tac `center6`
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (fs
        [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_spliced_box_program_def,
         compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_box_program_def,
         compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_box_patch_def,
         compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_patch_program_def]
      >> mp_tac
           (SIMP_RULE std_ss [LET_THM]
             (INST
               [``certificate0:cv`` |-> ``box0:cv``,
                ``certificate1:cv`` |-> ``box1:cv``,
                ``certificate2:cv`` |-> ``box2:cv``,
                ``certificate3:cv`` |-> ``box3:cv``,
                ``certificate4:cv`` |-> ``box4:cv``,
                ``certificate5:cv`` |-> ``box5:cv``,
                ``certificate6:cv`` |-> ``box6:cv``]
               compute_registeredCase10173SourceProgramIdentityTheory.registered_case10173_prepared_source_program_exact))
      >> metis_tac [])
  >> fs
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_spliced_center_program_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_center_program_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_center_patch_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_patch_program_def]
  >> mp_tac
       (SIMP_RULE std_ss [LET_THM]
         (INST
           [``certificate0:cv`` |-> ``center0:cv``,
            ``certificate1:cv`` |-> ``center1:cv``,
            ``certificate2:cv`` |-> ``center2:cv``,
            ``certificate3:cv`` |-> ``center3:cv``,
            ``certificate4:cv`` |-> ``center4:cv``,
            ``certificate5:cv`` |-> ``center5:cv``,
            ``certificate6:cv`` |-> ``center6:cv``]
           compute_registeredCase10173SourceProgramIdentityTheory.registered_case10173_prepared_source_program_exact))
  >> metis_tac []
QED

val _ = export_theory ();
