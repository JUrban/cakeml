(*****************************************************************************
 * Authenticated genuine-source instance of the generic polynomial runner.
 *
 * This connects the exact cell-0 source-0 payload and radii extracted from
 * the production entry to the representation-independent whole-program
 * invariant.  The center and outer environments remain abstract but are
 * constrained by the exact runtime/semantic relations required by the
 * production evaluator.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectFirstPolyRunBridge
Ancestors
  compute_boundedCase16594ObjectPolyRunInvariant
  compute_boundedCase16594ObjectFirstNegSemanticEval
  compute_boundedCase16594ObjectFirstPolySemantic
  compute_boundedCase16594ObjectDispatchPrefix8Eval
Libs
  bossLib preamble intLib

val source0_cv_tm =
  rhs
    (concl
      compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_source0_cv_def);

val (_,source0_arguments) = strip_comb source0_cv_tm;
val [source0_tag_tm,source0_program_cv_tm] = source0_arguments;

val bounded_case16594_object_source0_program_cv_def =
  new_definition
    ("bounded_case16594_object_source0_program_cv_def",
     mk_eq
       (mk_var ("bounded_case16594_object_source0_program_cv",``:cv``),
        source0_program_cv_tm));

Theorem bounded_case16594_object_source0_payload_split:
  bounded_case16594_object_cell0_source0_cv =
    Pair (Num 0) bounded_case16594_object_source0_program_cv
Proof
  simp
    [compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_source0_cv_def,
     bounded_case16594_object_source0_program_cv_def]
QED

Theorem bounded_case16594_object_source0_poly_program_cv_canonical:
  bounded_case16594_object_source0_program_cv =
    bounded_object_q_cv_list
      (MAP bounded_object_q_poly_instruction_cv
        bounded_case16594_object_source0_poly_program)
Proof
  simp
    [bounded_case16594_object_source0_program_cv_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_poly_program_def,
     compute_boundedCase16594ObjectPolyStepInvariantTheory.bounded_object_q_poly_instruction_cv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def]
QED

Theorem bounded_case16594_object_source0_runtime_radii_length:
  LENGTH bounded_case16594_object_cell0_runtime_radii = 6
Proof
  mp_tac
    compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_equivalent
  >> disch_then
       (mp_tac o MATCH_MP LIST_REL_LENGTH)
  >> simp
    [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def]
QED

Theorem bounded_case16594_object_source0_poly_run_runtime_refines:
  LENGTH runtime_center_boxes = 6 /\
  LENGTH runtime_outer_boxes = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_boxes semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_outer_boxes semantic_outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes /\
  4107 < clock ==>
  ?runtime_result_stack.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv (bounded_object_q_cv_list runtime_center_boxes);
         from_cv (bounded_object_q_cv_list runtime_outer_boxes);
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_source0_program_cv;
         from_cv (Pair (compute_exec$Num 1) (compute_exec$Num 0))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (compute_exec$Num 1)
          (bounded_object_q_cv_list runtime_result_stack))),refs) /\
    bounded_object_q_taylor_stack_runtime_refines
      runtime_result_stack [bounded_case16594_object_source0_result]
Proof
  strip_tac
  >> PURE_REWRITE_TAC
       [bounded_case16594_object_source0_poly_program_cv_canonical,
        GSYM
          compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encode,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
         (Q.SPECL
           [`bounded_case16594_object_source0_poly_program`, `[]`,
            `[bounded_case16594_object_source0_result]`, `[]`,
            `clock`, `refs`]
           (Q.INST
             [`runtime_radii` |->
                `bounded_case16594_object_cell0_runtime_radii`,
              `semantic_radii` |->
                `bounded_case16594_object_cell0_word_radii`,
              `weights` |->
                `bounded_case16594_object_cell0_weights`,
              `runtime_center_boxes` |-> `runtime_center_boxes`,
              `runtime_outer_boxes` |-> `runtime_outer_boxes`,
              `semantic_center_boxes` |-> `semantic_center_boxes`,
              `semantic_outer_boxes` |-> `semantic_outer_boxes`]
             compute_boundedCase16594ObjectPolyRunInvariantTheory.bounded_case16594_object_poly_run_eval_runtime_refines)))
  >> simp
       [compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encoded,
        bounded_case16594_object_source0_runtime_radii_length,
        compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_equivalent,
        compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs,
        compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_semantic_trace,
        compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_poly_program_def]
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
  >> qexists_tac `semantic_center_boxes`
  >> qexists_tac `semantic_outer_boxes`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
