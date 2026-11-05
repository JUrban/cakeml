(*****************************************************************************
 * Exact six-field payload of the authenticated case-16594 cell-0 call.
 *
 * The values below are projected from the already-authenticated entry term;
 * no boxes, radii, dispatch codes, sources, or certificates are copied by
 * hand.  The code/source pair is then identified with the checked 167-step
 * runtime plan.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchCell0PayloadIdentity
Ancestors
  compute_boundedCase16594DispatchRuntimePlanIdentity
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  bossLib preamble

val full_entry_tm =
  rhs
    (concl
      compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_cexp_def);

val (_,full_entry_constructor_arguments) = strip_comb full_entry_tm;
val [_,full_entry_arguments_tm] = full_entry_constructor_arguments;
val (full_entry_arguments,_) = listSyntax.dest_list full_entry_arguments_tm;

val [center_boxes_exp_tm,outer_boxes_exp_tm,radii_exp_tm,codes_exp_tm,
     sources_exp_tm,certificates_exp_tm] = full_entry_arguments;

val compute_exec_cv_num_tm =
  prim_mk_const {Name="Num",Thy="compute_exec"};
val compute_exec_cv_pair_tm =
  prim_mk_const {Name="Pair",Thy="compute_exec"};

fun mk_compute_exec_cv_num number =
  mk_comb (compute_exec_cv_num_tm,number);

fun mk_compute_exec_cv_pair (left,right) =
  mk_comb (mk_comb (compute_exec_cv_pair_tm,left),right);

fun compute_exp_value_to_cv tm =
  let
    val (head,arguments) = strip_comb tm
    val constructor = fst (dest_const head)
  in
    case (constructor,arguments) of
      ("Num",[number]) => mk_compute_exec_cv_num number
    | ("Pair",[left,right]) =>
        mk_compute_exec_cv_pair
          (compute_exp_value_to_cv left,compute_exp_value_to_cv right)
    | _ => raise Fail "non-value in authenticated object-dispatch entry"
  end;

fun define_cv_constant name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val bounded_case16594_runtime_cell0_center_boxes_cv_def =
  define_cv_constant "bounded_case16594_runtime_cell0_center_boxes_cv"
    (compute_exp_value_to_cv center_boxes_exp_tm);
val bounded_case16594_runtime_cell0_outer_boxes_cv_def =
  define_cv_constant "bounded_case16594_runtime_cell0_outer_boxes_cv"
    (compute_exp_value_to_cv outer_boxes_exp_tm);
val bounded_case16594_runtime_cell0_radii_cv_def =
  define_cv_constant "bounded_case16594_runtime_cell0_radii_cv"
    (compute_exp_value_to_cv radii_exp_tm);
val bounded_case16594_runtime_cell0_codes_cv_def =
  define_cv_constant "bounded_case16594_runtime_cell0_codes_cv"
    (compute_exp_value_to_cv codes_exp_tm);
val bounded_case16594_runtime_cell0_sources_cv_def =
  define_cv_constant "bounded_case16594_runtime_cell0_sources_cv"
    (compute_exp_value_to_cv sources_exp_tm);
val bounded_case16594_runtime_cell0_certificates_cv_def =
  define_cv_constant "bounded_case16594_runtime_cell0_certificates_cv"
    (compute_exp_value_to_cv certificates_exp_tm);

Theorem bounded_case16594_runtime_cell0_payload_identity:
  bounded_case16594_object_dispatch_cell0_cexp =
    App «candle_cv_q_packed_object_dispatch_entry»
      [from_cv bounded_case16594_runtime_cell0_center_boxes_cv;
       from_cv bounded_case16594_runtime_cell0_outer_boxes_cv;
       from_cv bounded_case16594_runtime_cell0_radii_cv;
       from_cv bounded_case16594_runtime_cell0_codes_cv;
       from_cv bounded_case16594_runtime_cell0_sources_cv;
       from_cv bounded_case16594_runtime_cell0_certificates_cv]
Proof
  simp
    [compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_cexp_def,
     bounded_case16594_runtime_cell0_center_boxes_cv_def,
     bounded_case16594_runtime_cell0_outer_boxes_cv_def,
     bounded_case16594_runtime_cell0_radii_cv_def,
     bounded_case16594_runtime_cell0_codes_cv_def,
     bounded_case16594_runtime_cell0_sources_cv_def,
     bounded_case16594_runtime_cell0_certificates_cv_def,
     compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_runtime_cell0_sources_identity:
  bounded_case16594_runtime_cell0_sources_cv =
    bounded_case16594_source_program_cv
Proof
  simp
    [bounded_case16594_runtime_cell0_sources_cv_def,
     compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_def]
QED

Theorem bounded_case16594_runtime_cell0_codes_identity:
  bounded_case16594_runtime_cell0_codes_cv =
    bounded_case16594_dispatch_codes_cv
Proof
  simp
    [bounded_case16594_runtime_cell0_codes_cv_def,
     compute_boundedCase16594DispatchRuntimePlanIdentityTheory.bounded_case16594_dispatch_codes_cv_def,
     compute_boundedCase16594DispatchRuntimePlanIdentityTheory.bounded_case16594_dispatch_code_cv_def,
     compute_boundedCase16594ProgramDataTheory.bounded_case16594_specializations_def]
QED

Theorem bounded_case16594_runtime_cell0_dispatch_plan_authenticated:
  bounded_case16594_dispatch_runtime_plan bounded_case16594_program
    bounded_case16594_specializations bounded_case16594_prepared_program
    bounded_case16594_runtime_cell0_codes_cv
    bounded_case16594_runtime_cell0_sources_cv
Proof
  metis_tac
    [bounded_case16594_runtime_cell0_codes_identity,
     bounded_case16594_runtime_cell0_sources_identity,
     compute_boundedCase16594DispatchRuntimePlanIdentityTheory.bounded_case16594_dispatch_runtime_plan_value]
QED

val _ = export_theory ();
