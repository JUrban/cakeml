(*****************************************************************************
 * Exact six-field payload of the authenticated case-16594 cell-0 call.
 *
 * The center, radii, dispatch codes, sources, and legacy certificates are
 * projected from the already-authenticated entry term.  The outer box is the
 * independently frozen minimal scale-2^40 box that both covers the genuine
 * source and is covered by the authenticated Taylor radii.  Its exact
 * rational encoding is intentionally not imported from the HOL Light call:
 * the later cross-system identity must check that import against this value.
 * The code/source pair is then identified with the checked 167-step runtime
 * plan.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchCell0PayloadIdentity
Ancestors
  compute_boundedCase16594DispatchRuntimePlanIdentity
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  bossLib preamble

val legacy_entry_tm =
  rhs
    (concl
      compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_cexp_def);

val (_,legacy_entry_constructor_arguments) = strip_comb legacy_entry_tm;
val [_,legacy_entry_arguments_tm] = legacy_entry_constructor_arguments;
val (legacy_entry_arguments,_) = listSyntax.dest_list legacy_entry_arguments_tm;

val [center_boxes_exp_tm,_,radii_exp_tm,codes_exp_tm,
     sources_exp_tm,certificates_exp_tm] = legacy_entry_arguments;

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

(* Canonically reduced encodings of the twelve tight scale-2^40 endpoints. *)
val tight_outer_boxes_cv_tm =
  ``Pair
      (Pair
        (Pair (Pair (Num 2845096288033) (Num 0)) (Num 549755813887))
        (Pair (Pair (Num 6013229092309) (Num 0)) (Num 1099511627775)))
      (Pair
        (Pair
          (Pair (Pair (Num 4) (Num 0)) (Num 0))
          (Pair (Pair (Num 4721083027347) (Num 0)) (Num 1099511627775)))
        (Pair
          (Pair
            (Pair (Pair (Num 2845096288033) (Num 0))
              (Num 549755813887))
            (Pair (Pair (Num 6013229092309) (Num 0))
              (Num 1099511627775)))
          (Pair
            (Pair
              (Pair (Pair (Num 4) (Num 0)) (Num 0))
              (Pair (Pair (Num 5044119543587) (Num 0))
                (Num 1099511627775)))
            (Pair
              (Pair
                (Pair (Pair (Num 1456519617341) (Num 0))
                  (Num 137438953471))
                (Pair (Pair (Num 12074774848709) (Num 0))
                  (Num 1099511627775)))
              (Pair
                (Pair
                  (Pair (Pair (Num 2845096288033) (Num 0))
                    (Num 549755813887))
                  (Pair (Pair (Num 3168132804275) (Num 0))
                    (Num 549755813887)))
                (Num 0)))))) : cv``;

val bounded_case16594_runtime_cell0_center_boxes_cv_def =
  define_cv_constant "bounded_case16594_runtime_cell0_center_boxes_cv"
    (compute_exp_value_to_cv center_boxes_exp_tm);
val bounded_case16594_runtime_cell0_outer_boxes_cv_def =
  define_cv_constant "bounded_case16594_runtime_cell0_outer_boxes_cv"
    tight_outer_boxes_cv_tm;
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
