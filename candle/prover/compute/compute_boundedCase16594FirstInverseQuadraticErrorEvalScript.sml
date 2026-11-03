(*****************************************************************************
 * Exact quadratic error term for the first genuine case-16594 inverse state.
 *****************************************************************************)
Theory compute_boundedCase16594FirstInverseQuadraticErrorEval
Ancestors
  compute_boundedCase16594FirstInverseLinearErrorEval
Libs
  bossLib preamble cv_transLib

Definition bounded_case16594_first_inverse_quadratic_error_cexp_def:
  bounded_case16594_first_inverse_quadratic_error_cexp =
    App «candle_cv_q_packed_quadratic_abs_upper6»
      [from_cv bounded_case16594_first_inverse_radii_cv;
       from_cv bounded_case16594_first_inverse_hessian_cv]
End

val _ = cv_trans
  compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def;
val _ = cv_trans
  compute_boundedCase16594FirstInverseZeroScaleEvalTheory.bounded_case16594_cv_repeat_def;
val _ = cv_trans
  compute_boundedCase16594FirstInverseZeroHessianEvalTheory.bounded_case16594_first_inverse_hessian_entry_cv_def;
val _ = cv_trans
  compute_boundedCase16594FirstInverseZeroHessianEvalTheory.bounded_case16594_first_inverse_hessian_cv_def;
val _ = cv_trans
  compute_boundedCase16594FirstInverseLinearErrorEvalTheory.bounded_case16594_first_inverse_radii_cv_def;
val _ = cv_trans compute_execTheory.from_cv_def;
val _ = cv_trans bounded_case16594_first_inverse_quadratic_error_cexp_def;

val first_inverse_quadratic_error_diagnostic =
  time cv_eval
    ``compute_eval_pure 1024 bounded_case16594_object_dispatch_cell0_ceqs
        bounded_case16594_first_inverse_quadratic_error_cexp``;

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
    | _ => raise Fail "non-value compute expression in quadratic result"
  end;

val first_inverse_quadratic_error_cv_tm =
  compute_exp_value_to_cv
    (optionSyntax.dest_some
      (rhs (concl first_inverse_quadratic_error_diagnostic)));

val _ =
  if type_of first_inverse_quadratic_error_cv_tm = ``:cv`` then ()
  else raise Fail
    ("quadratic result conversion has type " ^
     type_to_string (type_of first_inverse_quadratic_error_cv_tm));

val bounded_case16594_first_inverse_quadratic_error_cv_def =
  new_definition
    ("bounded_case16594_first_inverse_quadratic_error_cv_def",
     mk_eq
       (mk_var
         ("bounded_case16594_first_inverse_quadratic_error_cv",``:cv``),
        first_inverse_quadratic_error_cv_tm));

Theorem bounded_case16594_first_inverse_quadratic_error_pure_eval:
  compute_eval_pure 1024 bounded_case16594_object_dispatch_cell0_ceqs
      bounded_case16594_first_inverse_quadratic_error_cexp =
    SOME (from_cv bounded_case16594_first_inverse_quadratic_error_cv)
Proof
  rewrite_tac [bounded_case16594_first_inverse_quadratic_error_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC first_inverse_quadratic_error_diagnostic
QED

Theorem bounded_case16594_first_inverse_quadratic_error_eval:
  1024 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      bounded_case16594_first_inverse_quadratic_error_cexp
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_first_inverse_quadratic_error_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `1024`
  >> asm_rewrite_tac
       [bounded_case16594_first_inverse_quadratic_error_pure_eval]
QED

val _ = export_theory ();
