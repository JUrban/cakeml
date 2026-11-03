(*****************************************************************************
 * Authenticated field projection for the first genuine object result.
 *
 * The exact multiplication result contains roughly 2.8 million term nodes.
 * Rewriting that monolith for every bridge experiment is both slow and a poor
 * diagnostic.  Project its six already-proved fields once, without rerunning
 * the evaluator, so representation checks can proceed independently by field.
 *****************************************************************************)
open compute_boundedCase16594ObjectFirstPolyEvalTheory
open preamble

Theory compute_boundedCase16594ObjectFirstPolyResultFields
Ancestors
  compute_boundedCase16594ObjectFirstPolyEval
Libs
  bossLib preamble

fun dest_compute_exec_cv_pair tm =
  let
    val (pair_left,right) = dest_comb tm
    val (pair_const,left) = dest_comb pair_left
    val {Name,Thy,Ty} = dest_thy_const pair_const
  in
    if Name = "Pair" andalso Thy = "compute_exec" then (left,right)
    else raise Fail "expected compute_exec$Pair in first object result"
  end;

val first_result_tm =
  rhs
    (concl
      compute_boundedCase16594ObjectFirstPolyEvalTheory.bounded_case16594_object_first_mul_result_cv_def);

val (first_domain_tm,first_tail1_tm) =
  dest_compute_exec_cv_pair first_result_tm;
val (first_center_tm,first_tail2_tm) =
  dest_compute_exec_cv_pair first_tail1_tm;
val (first_center_gradient_tm,first_tail3_tm) =
  dest_compute_exec_cv_pair first_tail2_tm;
val (first_value_bound_tm,first_tail4_tm) =
  dest_compute_exec_cv_pair first_tail3_tm;
val (first_gradient_bounds_tm,first_hessian_tm) =
  dest_compute_exec_cv_pair first_tail4_tm;

fun define_cv_field name value =
  new_definition
    (name ^ "_def",
     mk_eq (mk_var (name,``:cv``),value));

val bounded_case16594_object_first_result_domain_cv_def =
  define_cv_field
    "bounded_case16594_object_first_result_domain_cv" first_domain_tm;
val bounded_case16594_object_first_result_center_cv_def =
  define_cv_field
    "bounded_case16594_object_first_result_center_cv" first_center_tm;
val bounded_case16594_object_first_result_center_gradient_cv_def =
  define_cv_field
    "bounded_case16594_object_first_result_center_gradient_cv"
    first_center_gradient_tm;
val bounded_case16594_object_first_result_value_bound_cv_def =
  define_cv_field
    "bounded_case16594_object_first_result_value_bound_cv"
    first_value_bound_tm;
val bounded_case16594_object_first_result_gradient_bounds_cv_def =
  define_cv_field
    "bounded_case16594_object_first_result_gradient_bounds_cv"
    first_gradient_bounds_tm;
val bounded_case16594_object_first_result_hessian_cv_def =
  define_cv_field
    "bounded_case16594_object_first_result_hessian_cv" first_hessian_tm;

Theorem bounded_case16594_object_first_result_fields:
  bounded_case16594_object_first_mul_result_cv =
    bounded_case16594_object_state_cv
      bounded_case16594_object_first_result_domain_cv
      bounded_case16594_object_first_result_center_cv
      bounded_case16594_object_first_result_center_gradient_cv
      bounded_case16594_object_first_result_value_bound_cv
      bounded_case16594_object_first_result_gradient_bounds_cv
      bounded_case16594_object_first_result_hessian_cv
Proof
  rewrite_tac
    [compute_boundedCase16594ObjectFirstPolyEvalTheory.bounded_case16594_object_first_mul_result_cv_def,
     compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def,
     bounded_case16594_object_first_result_domain_cv_def,
     bounded_case16594_object_first_result_center_cv_def,
     bounded_case16594_object_first_result_center_gradient_cv_def,
     bounded_case16594_object_first_result_value_bound_cv_def,
     bounded_case16594_object_first_result_gradient_bounds_cv_def,
     bounded_case16594_object_first_result_hessian_cv_def]
QED

val _ = export_theory ();
