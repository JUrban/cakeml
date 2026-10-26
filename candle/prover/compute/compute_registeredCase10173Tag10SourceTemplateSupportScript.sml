Theory compute_registeredCase10173Tag10SourceTemplateSupport
Ancestors
  compute_registeredCase10173ProgramTemplatePacketEval
  compute_registeredCase10173Tag10OrdinaryTraceEval
Libs
  bossLib preamble

Theorem registered_case10173_tag10_source_prefix_supported:
  registered_case10173_tag10_supported_program_pair
    (registered_case10173_source_prefix_template
      center0 center1 center2 center3 center4 center5)
    (registered_case10173_source_prefix_template
      box0 box1 box2 box3 box4 box5)
Proof
  simp
    [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_source_prefix_template_def,
     compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
     compute_registeredCase10173Tag10OrdinaryTraceEvalTheory.registered_case10173_tag10_supported_program_pair_def,
     compute_registeredCase10173Tag10OrdinaryStepEquivalenceTheory.registered_case10173_tag10_supported_instruction_pair_def]
QED

Theorem registered_case10173_tag10_source_suffix_supported:
  registered_case10173_tag10_supported_program_pair
    registered_case10173_source_suffix_template
    registered_case10173_source_suffix_template
Proof
  simp
    [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_source_suffix_template_def,
     compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
     compute_registeredCase10173Tag10OrdinaryTraceEvalTheory.registered_case10173_tag10_supported_program_pair_def,
     compute_registeredCase10173Tag10OrdinaryStepEquivalenceTheory.registered_case10173_tag10_supported_instruction_pair_def]
QED

Theorem registered_case10173_tag10_source_prefix_trace_from_old:
  1 < step_floor /\
  registered_case10173_ordinary_program_trace step_floor
    center_boxes boxes radii
    (registered_case10173_source_prefix_template
      center0 center1 center2 center3 center4 center5)
    (registered_case10173_source_prefix_template
      box0 box1 box2 box3 box4 box5)
    stack final_stack ==>
  registered_case10173_tag10_ordinary_program_trace step_floor
    center_boxes boxes radii
    (registered_case10173_source_prefix_template
      center0 center1 center2 center3 center4 center5)
    (registered_case10173_source_prefix_template
      box0 box1 box2 box3 box4 box5)
    stack final_stack
Proof
  strip_tac
  >> irule
       compute_registeredCase10173Tag10OrdinaryTraceEvalTheory.registered_case10173_tag10_ordinary_program_trace_from_old
  >> simp [registered_case10173_tag10_source_prefix_supported]
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_tag10_source_suffix_trace_from_old:
  1 < step_floor /\
  registered_case10173_ordinary_program_trace step_floor
    center_boxes boxes radii
    registered_case10173_source_suffix_template
    registered_case10173_source_suffix_template stack final_stack ==>
  registered_case10173_tag10_ordinary_program_trace step_floor
    center_boxes boxes radii
    registered_case10173_source_suffix_template
    registered_case10173_source_suffix_template stack final_stack
Proof
  strip_tac
  >> irule
       compute_registeredCase10173Tag10OrdinaryTraceEvalTheory.registered_case10173_tag10_ordinary_program_trace_from_old
  >> simp [registered_case10173_tag10_source_suffix_supported]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
