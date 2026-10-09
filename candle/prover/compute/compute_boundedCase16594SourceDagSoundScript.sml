(*****************************************************************************
 * Proof-only schedule bridge for the exact case16594 source DAG.
 *
 * The executable checker consumes prepared instructions and identities.  This
 * validator ties every such pair back to the original source instruction,
 * declared specialization role, structural DAG node, and identity-stack
 * transition.  It is deliberately outside the recurring executable path.
 *****************************************************************************)
Theory compute_boundedCase16594SourceDagSound
Ancestors
  compute_boundedCase16594SourceDagEval
Libs
  bossLib preamble wordsLib

Definition bounded_analytic64_dag_schedule_step_def:
  bounded_analytic64_dag_schedule_step nodes source role prepared identity
      identity_stack =
    case bounded_case16594_compile_specialized_instruction source role of
    | NONE => NONE
    | SOME expected_prepared =>
        if expected_prepared <> prepared then NONE
        else
          case bounded_analytic_dag_source_node source role identity_stack of
          | NONE => NONE
          | SOME (expected_node,rest) =>
              case oEL identity nodes of
              | NONE => NONE
              | SOME authenticated_node =>
                  if authenticated_node = expected_node then
                    SOME (identity::rest)
                  else NONE
End

Definition bounded_analytic64_dag_schedule_run_def:
  bounded_analytic64_dag_schedule_run nodes [] [] [] [] identity_stack =
      SOME identity_stack /\
  bounded_analytic64_dag_schedule_run nodes
      (source::sources) (role::roles) (prepared::prepareds)
      (identity::identities) identity_stack =
    (case bounded_analytic64_dag_schedule_step nodes source role prepared
        identity identity_stack of
     | NONE => NONE
     | SOME next_stack =>
         bounded_analytic64_dag_schedule_run nodes sources roles prepareds
           identities next_stack) /\
  bounded_analytic64_dag_schedule_run nodes _ _ _ _ _ = NONE
End

Definition bounded_case16594_source_dag_schedule_ok_def:
  bounded_case16594_source_dag_schedule_ok <=>
    bounded_case16594_prepared_program_ok /\
    bounded_case16594_source_dag_plan_ok /\
    bounded_analytic64_dag_schedule_run
      bounded_case16594_source_dag_nodes bounded_case16594_program
      bounded_case16594_specializations bounded_case16594_prepared_program
      bounded_case16594_source_dag_identities [] =
        SOME [bounded_case16594_source_dag_root]
End

Theorem bounded_case16594_source_dag_schedule_ok_value:
  bounded_case16594_source_dag_schedule_ok
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Definition bounded_analytic_dag_node_children_def:
  bounded_analytic_dag_node_children node =
    case node of
    | BoundedAnalyticDagPolynomial program role => []
    | BoundedAnalyticDagSqrt child => [child]
    | BoundedAnalyticDagNeg child => [child]
    | BoundedAnalyticDagAdd left right => [left;right]
    | BoundedAnalyticDagMul left right => [left;right]
    | BoundedAnalyticDagSquare child => [child]
    | BoundedAnalyticDagInverse child => [child]
    | BoundedAnalyticDagAtan child => [child]
    | BoundedAnalyticDagPiHalf => []
End

Definition bounded_analytic_dag_nodes_topological_from_def:
  bounded_analytic_dag_nodes_topological_from index [] = T /\
  bounded_analytic_dag_nodes_topological_from index (node::nodes) =
    (EVERY (\child. child < index)
      (bounded_analytic_dag_node_children node) /\
     bounded_analytic_dag_nodes_topological_from (SUC index) nodes)
End

Definition bounded_analytic64_dag_stack_refines_def:
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache <=>
    LIST_REL
      (\identity value.
         oEL identity result_cache = SOME (SOME value))
      identity_stack value_stack
End

(* The source-side stack transition is independent of the numerical result.
 * Keeping it explicit lets the soundness proof relate a cache hit to the
 * ordinary sequential step without re-running that step. *)
Definition bounded_analytic64_identity_reuse_stack_def:
  bounded_analytic64_identity_reuse_stack identity arity identity_stack =
    if arity = 0 then SOME (identity::identity_stack)
    else if arity = 1 then
      case identity_stack of
      | operand::rest => SOME (identity::rest)
      | _ => NONE
    else if arity = 2 then
      case identity_stack of
      | right::left::rest => SOME (identity::rest)
      | _ => NONE
    else NONE
End

Definition bounded_analytic64_dag_node_instruction_def:
  bounded_analytic64_dag_node_instruction node =
    case node of
    | BoundedAnalyticDagPolynomial program role =>
        bounded_case16594_compile_specialized_instruction
          (BoundedAnalyticPolynomial program) role
    | BoundedAnalyticDagSqrt child => SOME BoundedAnalytic64Sqrt
    | BoundedAnalyticDagNeg child => SOME BoundedAnalytic64Neg
    | BoundedAnalyticDagAdd left right => SOME BoundedAnalytic64Add
    | BoundedAnalyticDagMul left right => SOME BoundedAnalytic64Mul
    | BoundedAnalyticDagSquare child => SOME BoundedAnalytic64Square
    | BoundedAnalyticDagInverse child => SOME BoundedAnalytic64Inverse
    | BoundedAnalyticDagAtan child => SOME BoundedAnalytic64Atan
    | BoundedAnalyticDagPiHalf => SOME BoundedAnalytic64PiHalf
End

Definition bounded_analytic64_dag_cache_result_def:
  bounded_analytic64_dag_cache_result identity result_cache =
    case oEL identity result_cache of
    | SOME (SOME result) => SOME result
    | _ => NONE
End

Definition bounded_analytic64_dag_node_operand_stack_def:
  bounded_analytic64_dag_node_operand_stack node result_cache =
    case node of
    | BoundedAnalyticDagPolynomial program role => SOME []
    | BoundedAnalyticDagSqrt child =>
        (case bounded_analytic64_dag_cache_result child result_cache of
         | SOME value => SOME [value]
         | NONE => NONE)
    | BoundedAnalyticDagNeg child =>
        (case bounded_analytic64_dag_cache_result child result_cache of
         | SOME value => SOME [value]
         | NONE => NONE)
    | BoundedAnalyticDagAdd left right =>
        (case (bounded_analytic64_dag_cache_result left result_cache,
               bounded_analytic64_dag_cache_result right result_cache) of
         | (SOME left_value,SOME right_value) =>
             SOME [right_value;left_value]
         | _ => NONE)
    | BoundedAnalyticDagMul left right =>
        (case (bounded_analytic64_dag_cache_result left result_cache,
               bounded_analytic64_dag_cache_result right result_cache) of
         | (SOME left_value,SOME right_value) =>
             SOME [right_value;left_value]
         | _ => NONE)
    | BoundedAnalyticDagSquare child =>
        (case bounded_analytic64_dag_cache_result child result_cache of
         | SOME value => SOME [value]
         | NONE => NONE)
    | BoundedAnalyticDagInverse child =>
        (case bounded_analytic64_dag_cache_result child result_cache of
         | SOME value => SOME [value]
         | NONE => NONE)
    | BoundedAnalyticDagAtan child =>
        (case bounded_analytic64_dag_cache_result child result_cache of
         | SOME value => SOME [value]
         | NONE => NONE)
    | BoundedAnalyticDagPiHalf => SOME []
End

Definition bounded_analytic64_dag_node_eval_def:
  bounded_analytic64_dag_node_eval radii center_environment box_environment
      node cached_certificate result_cache =
    case bounded_analytic64_dag_node_instruction node of
    | NONE => NONE
    | SOME instruction =>
        case bounded_analytic64_dag_node_operand_stack node result_cache of
        | NONE => NONE
        | SOME operand_stack =>
            case bounded_analytic64_program_step radii center_environment
              box_environment instruction
              (operand_stack,
               case cached_certificate of NONE => [] | SOME value => [value])
            of
            | SOME ([result],[]) => SOME result
            | _ => NONE
End

Definition bounded_analytic64_dag_cache_valid_def:
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
      nodes result_cache certificate_cache <=>
    LENGTH result_cache = LENGTH nodes /\
    LENGTH certificate_cache = LENGTH nodes /\
    !identity node result cached_certificate.
      oEL identity nodes = SOME node /\
      oEL identity result_cache = SOME (SOME result) /\
      oEL identity certificate_cache = SOME cached_certificate ==>
      bounded_analytic64_dag_node_eval radii center_environment
        box_environment node cached_certificate result_cache = SOME result
End

Theorem bounded_case16594_source_dag_nodes_topological:
  bounded_analytic_dag_nodes_topological_from 0
    bounded_case16594_source_dag_nodes
Proof
  EVAL_TAC
QED

Theorem bounded_analytic64_dag_stack_refines_empty:
  bounded_analytic64_dag_stack_refines [] [] result_cache
Proof
  simp [bounded_analytic64_dag_stack_refines_def]
QED

Theorem bounded_analytic64_dag_stack_refines_cons:
  bounded_analytic64_dag_stack_refines (identity::identity_stack)
      (value::value_stack) result_cache <=>
    oEL identity result_cache = SOME (SOME value) /\
    bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache
Proof
  simp [bounded_analytic64_dag_stack_refines_def]
QED

Theorem bounded_analytic64_dag_stack_refines_unique:
  bounded_analytic64_dag_stack_refines identity_stack left_value_stack
      result_cache /\
  bounded_analytic64_dag_stack_refines identity_stack right_value_stack
      result_cache ==>
  left_value_stack = right_value_stack
Proof
  rw [bounded_analytic64_dag_stack_refines_def,LIST_REL_EL_EQN] >>
  irule LIST_EQ >>
  gvs [] >>
  rw [] >>
  res_tac >>
  gvs []
QED

Theorem bounded_analytic64_dag_node_instruction_arity:
  bounded_analytic64_dag_node_instruction node = SOME instruction ==>
  bounded_analytic64_instruction_arity instruction =
    &(LENGTH (bounded_analytic_dag_node_children node))
Proof
  Cases_on `node` >>
  simp [bounded_analytic64_dag_node_instruction_def,
    bounded_analytic_dag_node_children_def,
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_instruction_def,
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_analytic_instruction_def,
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_ok_def,
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_program_def,
    bounded_analytic64_instruction_arity_def] >>
  every_case_tac >> gvs []
QED

Theorem bounded_analytic64_dag_node_operand_stack_length:
  bounded_analytic64_dag_node_instruction node = SOME instruction /\
  bounded_analytic64_dag_node_operand_stack node result_cache = SOME stack ==>
  &(LENGTH stack) = bounded_analytic64_instruction_arity instruction
Proof
  strip_tac >>
  imp_res_tac bounded_analytic64_dag_node_instruction_arity >>
  Cases_on `node` >>
  gvs [bounded_analytic64_dag_node_operand_stack_def,
    bounded_analytic64_dag_cache_result_def,
    bounded_analytic_dag_node_children_def] >>
  every_case_tac >> gvs []
QED

Theorem bounded_analytic64_dag_cache_valid_empty:
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
    nodes (REPLICATE (LENGTH nodes) NONE)
    (REPLICATE (LENGTH nodes) NONE)
Proof
  rw [bounded_analytic64_dag_cache_valid_def,LENGTH_REPLICATE] >>
  gvs [oEL_THM,EL_REPLICATE]
QED

Theorem bounded_analytic64_dag_source_node_operands:
  bounded_analytic_dag_source_node source role identity_stack =
      SOME (node,rest_identity_stack) /\
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache ==>
  ?operand_stack rest_value_stack.
    bounded_analytic64_dag_node_operand_stack node result_cache =
      SOME operand_stack /\
    value_stack = operand_stack ++ rest_value_stack /\
    bounded_analytic64_dag_stack_refines rest_identity_stack
      rest_value_stack result_cache
Proof
  Cases_on `source` >>
  simp [compute_boundedCase16594SourceDagPlanTheory.bounded_analytic_dag_source_node_def] >>
  every_case_tac >>
  gvs [bounded_analytic64_dag_stack_refines_def,
    bounded_analytic64_dag_node_operand_stack_def,
    bounded_analytic64_dag_cache_result_def,LIST_REL_def] >>
  rpt strip_tac >> rveq >> gvs [LIST_REL_def]
QED

Theorem bounded_analytic64_program_step_append:
  bounded_analytic64_program_step radii center_environment box_environment
      instruction (operand_stack,certificate_prefix) =
      SOME ([result],[]) ==>
  bounded_analytic64_program_step radii center_environment box_environment
      instruction
      (operand_stack ++ rest_stack,
       certificate_prefix ++ rest_certificates) =
      SOME (result::rest_stack,rest_certificates)
Proof
  Cases_on `instruction` >>
  simp [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def] >>
  every_case_tac >> gvs []
QED

Theorem bounded_analytic64_program_step_unappend:
  bounded_analytic64_program_step radii center_environment box_environment
      instruction
      (operand_stack ++ rest_stack,
       certificate_prefix ++ rest_certificates) =
      SOME (result::rest_stack,rest_certificates) ==>
  bounded_analytic64_program_step radii center_environment box_environment
      instruction (operand_stack,certificate_prefix) = SOME ([result],[])
Proof
  Cases_on `instruction` >>
  simp [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def] >>
  every_case_tac >> gvs []
QED

(* A successful instruction consumes exactly its arity-sized operand prefix;
 * the remaining value stack is carried through unchanged.  This is the
 * shape fact needed when a cache miss executes an ordinary program step. *)
Theorem bounded_analytic64_program_step_rest:
  &(LENGTH operand_stack) = bounded_analytic64_instruction_arity instruction /\
  bounded_analytic64_program_step radii center_environment box_environment
      instruction (operand_stack ++ rest_stack,certificates) =
      SOME (result::next_rest_stack,next_certificates) ==>
  next_rest_stack = rest_stack
Proof
  Cases_on `instruction` >>
  simp [bounded_analytic64_instruction_arity_def,
    compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def] >>
  every_case_tac >> gvs [] >> rpt strip_tac >> gvs [] >>
  Cases_on `operand_stack` >> gvs [LENGTH_EQ_1]
QED

Theorem oEL_some_length:
  oEL index values = SOME value ==> index < LENGTH values
Proof
  simp [oEL_THM] >> every_case_tac >> gvs []
QED

Theorem bounded_analytic64_current_certificate_prefix:
  bounded_analytic64_current_certificate instruction certificates =
      SOME (current_certificate,rest_certificates) ==>
  certificates =
    (case current_certificate of NONE => [] | SOME value => [value]) ++
    rest_certificates
Proof
  Cases_on `instruction` >> Cases_on `certificates` >>
  simp [bounded_analytic64_current_certificate_def,
    bounded_analytic64_instruction_uses_certificate_def] >>
  rpt strip_tac >> rveq >> simp []
QED

Theorem bounded_analytic64_dag_schedule_step_identity_reuse:
  bounded_analytic64_dag_schedule_step nodes source role prepared identity
      identity_stack = SOME next_identity_stack ==>
  bounded_analytic64_identity_reuse_stack identity
      (bounded_analytic64_instruction_arity prepared) identity_stack =
    SOME next_identity_stack
Proof
  Cases_on `source` >> Cases_on `role` >>
  simp [bounded_analytic64_dag_schedule_step_def,
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_instruction_def,
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_analytic_instruction_def,
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_ok_def,
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_program_def,
    compute_boundedCase16594SourceDagPlanTheory.bounded_analytic_dag_source_node_def,
    bounded_analytic64_identity_reuse_stack_def,
    bounded_analytic64_instruction_arity_def] >>
  every_case_tac >> gvs []
QED

Theorem bounded_analytic64_dag_schedule_step_decompose:
  bounded_analytic64_dag_schedule_step nodes source role prepared identity
      identity_stack = SOME next_identity_stack /\
  oEL identity nodes = SOME node ==>
  bounded_case16594_compile_specialized_instruction source role =
      SOME prepared /\
  ?rest.
    bounded_analytic_dag_source_node source role identity_stack =
      SOME (node,rest) /\
    next_identity_stack = identity::rest
Proof
  simp [bounded_analytic64_dag_schedule_step_def] >>
  every_case_tac >> gvs [] >>
  rpt strip_tac >> rveq >> gvs []
QED

Theorem bounded_analytic64_dag_schedule_step_lookup:
  bounded_analytic64_dag_schedule_step nodes source role prepared identity
      identity_stack = SOME next_identity_stack ==>
  ?node. oEL identity nodes = SOME node
Proof
  simp [bounded_analytic64_dag_schedule_step_def] >>
  every_case_tac >> gvs []
QED

Theorem bounded_analytic64_dag_source_node_instruction:
  bounded_case16594_compile_specialized_instruction source role =
      SOME prepared /\
  bounded_analytic_dag_source_node source role identity_stack =
      SOME (node,rest) ==>
  bounded_analytic64_dag_node_instruction node = SOME prepared
Proof
  Cases_on `source` >> Cases_on `role` >>
  gvs [bounded_analytic64_dag_node_instruction_def,
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_instruction_def,
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_analytic_instruction_def,
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_ok_def,
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_program_def,
    compute_boundedCase16594SourceDagPlanTheory.bounded_analytic_dag_source_node_def] >>
  every_case_tac >> gvs [] >>
  rpt strip_tac >> rveq >> gvs []
QED


Theorem bounded_analytic64_dag_schedule_step_node_instruction:
  bounded_analytic64_dag_schedule_step nodes source role prepared identity
      identity_stack = SOME next_identity_stack /\
  oEL identity nodes = SOME node ==>
  bounded_analytic64_dag_node_instruction node = SOME prepared
Proof
  metis_tac [bounded_analytic64_dag_schedule_step_decompose,
    bounded_analytic64_dag_source_node_instruction]
QED

Theorem bounded_analytic64_dag_node_eval_program_step:
  bounded_analytic64_dag_node_eval radii center_environment box_environment
      node current_certificate result_cache = SOME result /\
  bounded_analytic64_dag_node_instruction node = SOME instruction /\
  bounded_analytic64_dag_node_operand_stack node result_cache =
      SOME operand_stack ==>
  bounded_analytic64_program_step radii center_environment box_environment
    instruction
    (operand_stack,
     case current_certificate of NONE => [] | SOME value => [value]) =
    SOME ([result],[])
Proof
  strip_tac >>
  fs [bounded_analytic64_dag_node_eval_def] >>
  every_case_tac >> gvs []
QED

Theorem bounded_analytic64_dag_node_eval_step:
  bounded_case16594_compile_specialized_instruction source role =
      SOME instruction /\
  bounded_analytic_dag_source_node source role identity_stack =
      SOME (node,rest_identity_stack) /\
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache /\
  bounded_analytic64_dag_node_eval radii center_environment box_environment
      node current_certificate result_cache = SOME result /\
  bounded_analytic64_current_certificate instruction certificates =
      SOME (current_certificate,rest_certificates) ==>
  ?rest_value_stack.
    bounded_analytic64_program_step radii center_environment box_environment
      instruction (value_stack,certificates) =
        SOME (result::rest_value_stack,rest_certificates) /\
    bounded_analytic64_dag_stack_refines rest_identity_stack
      rest_value_stack result_cache
Proof
  strip_tac >>
  imp_res_tac bounded_analytic64_dag_source_node_instruction >>
  imp_res_tac bounded_analytic64_dag_source_node_operands >>
  imp_res_tac bounded_analytic64_dag_node_eval_program_step >>
  imp_res_tac bounded_analytic64_current_certificate_prefix >>
  metis_tac [bounded_analytic64_program_step_append]
QED

Theorem bounded_analytic64_dag_stack_refines_reuse:
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache /\
  oEL identity result_cache = SOME (SOME value) /\
  bounded_analytic64_identity_reuse_stack identity arity identity_stack =
      SOME next_identity_stack /\
  bounded_analytic64_reuse_stack value arity value_stack =
      SOME next_value_stack ==>
  bounded_analytic64_dag_stack_refines next_identity_stack next_value_stack
      result_cache
Proof
  simp [bounded_analytic64_dag_stack_refines_def,
    bounded_analytic64_identity_reuse_stack_def,
    bounded_analytic64_reuse_stack_def] >>
  every_case_tac >> gvs [LIST_REL_def] >>
  rpt strip_tac >> rveq >> gvs [LIST_REL_def]
QED

Theorem bounded_analytic64_dag_cache_hit_refines_sequential:
  bounded_analytic64_dag_schedule_step nodes source role instruction identity
      identity_stack = SOME next_identity_stack /\
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
      nodes result_cache certificate_cache /\
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache /\
  bounded_analytic64_current_certificate instruction certificates =
      SOME (current_certificate,rest_certificates) /\
  oEL identity result_cache = SOME (SOME cached_result) /\
  oEL identity certificate_cache = SOME current_certificate /\
  bounded_analytic64_reuse_stack cached_result
      (bounded_analytic64_instruction_arity instruction) value_stack =
      SOME next_value_stack ==>
  bounded_analytic64_program_step radii center_environment box_environment
      instruction (value_stack,certificates) =
      SOME (next_value_stack,rest_certificates) /\
  bounded_analytic64_dag_stack_refines next_identity_stack next_value_stack
      result_cache
Proof
  strip_tac >>
  imp_res_tac bounded_analytic64_dag_schedule_step_lookup >>
  imp_res_tac bounded_analytic64_dag_schedule_step_decompose >>
  fs [bounded_analytic64_dag_cache_valid_def] >>
  res_tac >>
  imp_res_tac bounded_analytic64_dag_node_eval_step >>
  imp_res_tac bounded_analytic64_dag_schedule_step_identity_reuse >>
  imp_res_tac bounded_analytic64_dag_stack_refines_reuse >>
  metis_tac [bounded_analytic64_dag_stack_refines_cons,
    bounded_analytic64_dag_stack_refines_unique]
QED

(* Conversely, a successful ordinary step can be restricted to the exact
 * operand prefix authenticated by the DAG node.  This is the cache-miss
 * bridge: the top result inserted by the executable step is exactly the
 * result obtained by evaluating the node in isolation. *)
Theorem bounded_analytic64_dag_node_eval_from_program_step:
  bounded_analytic64_dag_node_instruction node = SOME instruction /\
  bounded_analytic64_dag_node_operand_stack node result_cache =
      SOME operand_stack /\
  bounded_analytic64_current_certificate instruction certificates =
      SOME (current_certificate,rest_certificates) /\
  bounded_analytic64_program_step radii center_environment box_environment
      instruction (operand_stack ++ rest_stack,certificates) =
      SOME (result::rest_stack,rest_certificates) ==>
  bounded_analytic64_dag_node_eval radii center_environment box_environment
      node current_certificate result_cache = SOME result
Proof
  strip_tac >>
  imp_res_tac bounded_analytic64_current_certificate_prefix >>
  rveq >>
  imp_res_tac bounded_analytic64_program_step_unappend >>
  fs [bounded_analytic64_dag_node_eval_def]
QED

(* Filling a cache slot that was empty cannot change an already successful
 * operand lookup.  In particular, this covers the new node itself without a
 * separate acyclicity argument: a successful old lookup could not have used
 * the empty slot. *)
Theorem bounded_analytic64_dag_node_operand_stack_insert_empty:
  oEL identity result_cache = SOME NONE /\
  bounded_analytic64_dag_node_operand_stack node result_cache =
      SOME operand_stack ==>
  bounded_analytic64_dag_node_operand_stack node
      (LUPDATE (SOME result) identity result_cache) = SOME operand_stack
Proof
  Cases_on `node` >>
  gvs [bounded_analytic64_dag_node_operand_stack_def,
    bounded_analytic64_dag_cache_result_def,oEL_LUPDATE] >>
  every_case_tac >> gvs []
QED

Theorem bounded_analytic64_dag_node_eval_insert_empty:
  oEL identity result_cache = SOME NONE /\
  bounded_analytic64_dag_node_eval radii center_environment box_environment
      node cached_certificate result_cache = SOME node_result ==>
  bounded_analytic64_dag_node_eval radii center_environment box_environment
      node cached_certificate
      (LUPDATE (SOME inserted_result) identity result_cache) =
    SOME node_result
Proof
  strip_tac >>
  fs [bounded_analytic64_dag_node_eval_def] >>
  every_case_tac >> gvs [] >>
  imp_res_tac bounded_analytic64_dag_node_operand_stack_insert_empty >>
  gvs []
QED

Theorem bounded_analytic64_dag_cache_valid_insert:
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
      nodes result_cache certificate_cache /\
  oEL identity nodes = SOME node /\
  oEL identity result_cache = SOME NONE /\
  oEL identity certificate_cache = SOME old_certificate /\
  bounded_analytic64_dag_node_eval radii center_environment box_environment
      node current_certificate result_cache = SOME result ==>
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
      nodes (LUPDATE (SOME result) identity result_cache)
      (LUPDATE current_certificate identity certificate_cache)
Proof
  rw [bounded_analytic64_dag_cache_valid_def,LENGTH_LUPDATE] >>
  Cases_on `identity = identity'` >>
  gvs [oEL_LUPDATE] >>
  metis_tac [bounded_analytic64_dag_node_eval_insert_empty]
QED

Theorem bounded_analytic64_dag_stack_refines_insert_empty:
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache /\
  oEL identity result_cache = SOME NONE ==>
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      (LUPDATE (SOME result) identity result_cache)
Proof
  rw [bounded_analytic64_dag_stack_refines_def] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  match_mp_tac LIST_REL_mono >>
  rw [] >>
  Cases_on `identity = x` >> gvs [oEL_LUPDATE]
QED

Theorem bounded_analytic64_dag_step_hit_decompose:
  bounded_analytic64_dag_step radii center_environment box_environment
      instruction identity
      (value_stack,certificates,result_cache,certificate_cache) =
      SOME (next_value_stack,next_certificates,next_result_cache,
            next_certificate_cache) /\
  oEL identity result_cache = SOME (SOME cached_result) ==>
  ?current_certificate.
    bounded_analytic64_current_certificate instruction certificates =
      SOME (current_certificate,next_certificates) /\
    oEL identity certificate_cache = SOME current_certificate /\
    bounded_analytic64_reuse_stack cached_result
      (bounded_analytic64_instruction_arity instruction) value_stack =
      SOME next_value_stack /\
    next_result_cache = result_cache /\
    next_certificate_cache = certificate_cache
Proof
  strip_tac >>
  fs [compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_step_def] >>
  every_case_tac >> gvs []
QED

Theorem bounded_analytic64_dag_step_cache_lookup:
  bounded_analytic64_dag_step radii center_environment box_environment
      instruction identity
      (value_stack,certificates,result_cache,certificate_cache) =
      SOME next_state ==>
  ?cache_entry. oEL identity result_cache = SOME cache_entry
Proof
  strip_tac >>
  fs [compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_step_def] >>
  every_case_tac >> gvs []
QED

Theorem bounded_analytic64_program_step_certificate_rest:
  bounded_analytic64_current_certificate instruction certificates =
      SOME (current_certificate,rest_certificates) /\
  bounded_analytic64_program_step radii center_environment box_environment
      instruction (value_stack,certificates) =
      SOME (next_value_stack,next_certificates) ==>
  next_certificates = rest_certificates
Proof
  Cases_on `instruction` >>
  simp [bounded_analytic64_current_certificate_def,
    bounded_analytic64_instruction_uses_certificate_def,
    compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def] >>
  every_case_tac >> gvs [] >> rpt strip_tac >> gvs []
QED

Theorem bounded_analytic64_dag_step_miss_decompose:
  bounded_analytic64_dag_step radii center_environment box_environment
      instruction identity
      (value_stack,certificates,result_cache,certificate_cache) =
      SOME (next_value_stack,next_certificates,next_result_cache,
            next_certificate_cache) /\
  oEL identity result_cache = SOME NONE ==>
  ?current_certificate result rest_value_stack.
    bounded_analytic64_current_certificate instruction certificates =
      SOME (current_certificate,next_certificates) /\
    bounded_analytic64_program_step radii center_environment box_environment
      instruction (value_stack,certificates) =
      SOME (next_value_stack,next_certificates) /\
    next_value_stack = result::rest_value_stack /\
    next_result_cache =
      LUPDATE (SOME result) identity result_cache /\
    next_certificate_cache =
      LUPDATE current_certificate identity certificate_cache
Proof
  strip_tac >>
  fs [compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_step_def] >>
  every_case_tac >> gvs [] >>
  metis_tac [bounded_analytic64_program_step_certificate_rest]
QED

Theorem bounded_analytic64_dag_cache_miss_refines_sequential:
  bounded_analytic64_dag_schedule_step nodes source role instruction identity
      identity_stack = SOME next_identity_stack /\
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
      nodes result_cache certificate_cache /\
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache /\
  bounded_analytic64_dag_step radii center_environment box_environment
      instruction identity
      (value_stack,certificates,result_cache,certificate_cache) =
      SOME (next_value_stack,next_certificates,next_result_cache,
            next_certificate_cache) /\
  oEL identity result_cache = SOME NONE ==>
  bounded_analytic64_program_step radii center_environment box_environment
      instruction (value_stack,certificates) =
      SOME (next_value_stack,next_certificates) /\
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
      nodes next_result_cache next_certificate_cache /\
  bounded_analytic64_dag_stack_refines next_identity_stack next_value_stack
      next_result_cache
Proof
  strip_tac >>
  imp_res_tac bounded_analytic64_dag_schedule_step_lookup >>
  imp_res_tac bounded_analytic64_dag_schedule_step_decompose >>
  fs [compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_step_def] >>
  every_case_tac >> gvs [] >>
  imp_res_tac bounded_analytic64_dag_source_node_instruction >>
  imp_res_tac bounded_analytic64_dag_source_node_operands >>
  imp_res_tac bounded_analytic64_dag_node_operand_stack_length >>
  imp_res_tac bounded_analytic64_program_step_certificate_rest >>
  `t = rest_value_stack` by
    metis_tac [bounded_analytic64_program_step_rest] >>
  gvs [] >>
  `bounded_analytic64_dag_node_eval radii center_environment
     box_environment node q result_cache = SOME h` by
    metis_tac [bounded_analytic64_dag_node_eval_from_program_step] >>
  `oEL identity certificate_cache =
     SOME (EL identity certificate_cache)` by gvs [oEL_THM] >>
  `bounded_analytic64_dag_cache_valid radii center_environment
     box_environment nodes (LUPDATE (SOME h) identity result_cache)
       (LUPDATE q identity certificate_cache)` by
    (match_mp_tac (Q.INST
       [`old_certificate` |-> `EL identity certificate_cache`]
       bounded_analytic64_dag_cache_valid_insert) >>
     gvs []) >>
  `bounded_analytic64_dag_stack_refines rest rest_value_stack
     (LUPDATE (SOME h) identity result_cache)` by
    metis_tac [bounded_analytic64_dag_stack_refines_insert_empty] >>
  gvs [bounded_analytic64_dag_stack_refines_cons,oEL_LUPDATE]
QED

Theorem bounded_analytic64_dag_cache_hit_step_refines_sequential:
  bounded_analytic64_dag_schedule_step nodes source role instruction identity
      identity_stack = SOME next_identity_stack /\
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
      nodes result_cache certificate_cache /\
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache /\
  bounded_analytic64_dag_step radii center_environment box_environment
      instruction identity
      (value_stack,certificates,result_cache,certificate_cache) =
      SOME (next_value_stack,next_certificates,next_result_cache,
            next_certificate_cache) /\
  oEL identity result_cache = SOME (SOME cached_result) ==>
  bounded_analytic64_program_step radii center_environment box_environment
      instruction (value_stack,certificates) =
      SOME (next_value_stack,next_certificates) /\
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
      nodes next_result_cache next_certificate_cache /\
  bounded_analytic64_dag_stack_refines next_identity_stack next_value_stack
      next_result_cache
Proof
  strip_tac >>
  fs [compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_step_def] >>
  every_case_tac >> gvs [] >>
  match_mp_tac (Q.INST [`current_certificate` |-> `q`,
                         `cached_result` |-> `cached_result`]
    bounded_analytic64_dag_cache_hit_refines_sequential) >>
  gvs []
QED

(* Every authenticated DAG step is the corresponding ordinary sequential
 * instruction step.  Cache hits reuse an already validated node result;
 * cache misses execute the ordinary step and extend both cache invariants. *)
Theorem bounded_analytic64_dag_step_refines_sequential:
  bounded_analytic64_dag_schedule_step nodes source role instruction identity
      identity_stack = SOME next_identity_stack /\
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
      nodes result_cache certificate_cache /\
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache /\
  bounded_analytic64_dag_step radii center_environment box_environment
      instruction identity
      (value_stack,certificates,result_cache,certificate_cache) =
      SOME (next_value_stack,next_certificates,next_result_cache,
            next_certificate_cache) ==>
  bounded_analytic64_program_step radii center_environment box_environment
      instruction (value_stack,certificates) =
      SOME (next_value_stack,next_certificates) /\
  bounded_analytic64_dag_cache_valid radii center_environment box_environment
      nodes next_result_cache next_certificate_cache /\
  bounded_analytic64_dag_stack_refines next_identity_stack next_value_stack
      next_result_cache
Proof
  strip_tac >>
  imp_res_tac bounded_analytic64_dag_schedule_step_lookup >>
  imp_res_tac bounded_analytic64_dag_schedule_step_decompose >>
  drule bounded_analytic64_dag_step_cache_lookup >>
  disch_then (qx_choose_then `cache_entry` assume_tac) >>
  Cases_on `cache_entry` >-
    (metis_tac [bounded_analytic64_dag_cache_miss_refines_sequential]) >-
    (metis_tac [bounded_analytic64_dag_cache_hit_step_refines_sequential])
QED

(* The one-step refinement composes across the complete authenticated
 * schedule.  The executable DAG run and the ordinary sequential run consume
 * the same prepared instruction and certificate streams; the two cache
 * invariants are threaded only on the DAG side. *)
Theorem bounded_analytic64_dag_run_refines_sequential:
  !sources roles instructions identities identity_stack value_stack
      certificates result_cache certificate_cache next_identity_stack
      next_value_stack next_certificates next_result_cache
      next_certificate_cache.
    bounded_analytic64_dag_schedule_run nodes sources roles instructions
        identities identity_stack = SOME next_identity_stack /\
    bounded_analytic64_dag_cache_valid radii center_environment
        box_environment nodes result_cache certificate_cache /\
    bounded_analytic64_dag_stack_refines identity_stack value_stack
        result_cache /\
    bounded_analytic64_dag_run radii center_environment box_environment
        instructions identities
        (value_stack,certificates,result_cache,certificate_cache) =
      SOME (next_value_stack,next_certificates,next_result_cache,
            next_certificate_cache) ==>
    bounded_analytic64_program_run radii center_environment box_environment
        instructions (value_stack,certificates) =
      SOME (next_value_stack,next_certificates) /\
    bounded_analytic64_dag_cache_valid radii center_environment
        box_environment nodes next_result_cache next_certificate_cache /\
    bounded_analytic64_dag_stack_refines next_identity_stack
        next_value_stack next_result_cache
Proof
  Induct_on `sources`
  >- (Cases_on `roles` >> Cases_on `instructions` >>
      Cases_on `identities` >>
      gvs [bounded_analytic64_dag_schedule_run_def,
        compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_run_def,
        compute_boundedAnalyticProgramTheory.bounded_analytic64_program_run_def])
  >- (Cases_on `roles` >> Cases_on `instructions` >>
      Cases_on `identities` >>
      gvs [bounded_analytic64_dag_schedule_run_def,
        compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_run_def] >>
      rpt strip_tac >> every_case_tac >> gvs [] >>
      PairCases_on `x` >> gvs [] >>
      imp_res_tac bounded_analytic64_dag_step_refines_sequential >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      gvs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_run_def])
QED

Theorem bounded_analytic64_dag_eval_refines_sequential:
  bounded_analytic64_dag_schedule_run nodes sources roles instructions
      identities [] = SOME next_identity_stack /\
  bounded_analytic64_dag_eval radii center_environment box_environment
      instructions identities (LENGTH nodes) certificates = SOME result ==>
  bounded_analytic64_program_eval radii center_environment box_environment
      instructions certificates = SOME result
Proof
  rw [compute_boundedCase16594SourceDagEvalTheory.bounded_analytic64_dag_eval_def] >>
  every_case_tac >> gvs [] >>
  PairCases_on `r'` >> gvs [] >>
  `bounded_analytic64_dag_cache_valid radii center_environment
      box_environment nodes
      (REPLICATE (LENGTH nodes) NONE)
      (REPLICATE (LENGTH nodes) NONE)` by
    simp [bounded_analytic64_dag_cache_valid_empty] >>
  `bounded_analytic64_dag_stack_refines [] []
      (REPLICATE (LENGTH nodes) NONE)` by
    simp [bounded_analytic64_dag_stack_refines_empty] >>
  `bounded_analytic64_program_run radii center_environment box_environment
      instructions ([],certificates) = SOME ([h],[]) /\
   bounded_analytic64_dag_cache_valid radii center_environment
      box_environment nodes r'0 r'1 /\
   bounded_analytic64_dag_stack_refines next_identity_stack [h] r'0`
    suffices_by
      gvs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_def] >>
  irule bounded_analytic64_dag_run_refines_sequential >>
  qexists_tac `REPLICATE (LENGTH nodes) NONE` >>
  qexists_tac `identities` >>
  qexists_tac `[]` >>
  qexists_tac `REPLICATE (LENGTH nodes) NONE` >>
  qexists_tac `roles` >>
  qexists_tac `sources` >>
  gvs [] >>
  simp [bounded_analytic64_dag_stack_refines_empty]
QED

Theorem bounded_case16594_source_dag_eval_refines_sequential:
  bounded_case16594_source_dag_eval radii center_environment
      box_environment certificates = SOME result ==>
  bounded_analytic64_program_eval radii center_environment box_environment
      bounded_case16594_prepared_program certificates = SOME result
Proof
  assume_tac bounded_case16594_source_dag_schedule_ok_value >>
  rw [compute_boundedCase16594SourceDagEvalTheory.bounded_case16594_source_dag_eval_def] >>
  gvs [bounded_case16594_source_dag_schedule_ok_def] >>
  metis_tac [bounded_analytic64_dag_eval_refines_sequential]
QED

Theorem bounded_analytic64_dag_schedule_rejects_prepared_alias:
  bounded_analytic64_dag_schedule_step
    [BoundedAnalyticDagPiHalf] BoundedAnalyticPiHalf
    BoundedAnalyticGeneral BoundedAnalytic64Neg 0 [] = NONE
Proof
  EVAL_TAC
QED

Theorem bounded_analytic64_dag_schedule_rejects_identity_alias:
  bounded_analytic64_dag_schedule_step
    [BoundedAnalyticDagPiHalf;BoundedAnalyticDagNeg 0]
    BoundedAnalyticPiHalf BoundedAnalyticGeneral
    BoundedAnalytic64PiHalf 1 [] = NONE
Proof
  EVAL_TAC
QED

Theorem bounded_analytic64_dag_schedule_rejects_role_alias:
  bounded_analytic64_dag_schedule_step
    [BoundedAnalyticDagPolynomial
      (THE (bounded_analytic_specialization_program
        (BoundedNegDeltaDerivative 3))) BoundedAnalyticGeneral]
    (BoundedAnalyticPolynomial
      (THE (bounded_analytic_specialization_program
        (BoundedNegDeltaDerivative 3))))
    (BoundedNegDeltaDerivative 3)
    (BoundedAnalytic64NegDeltaDerivative 3) 0 [] = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
