(*****************************************************************************
 * Complete proof-producing evaluator result for the first genuine inverse.
 *
 * The closed result is computed by the verified CV evaluator, converted back
 * to Candle's object-cv datatype, and lifted to ordinary compute_eval for all
 * sufficient clocks.  No untrusted result bytes are admitted.
 *****************************************************************************)
Theory compute_boundedCase16594FirstInverseStateEval
Ancestors
  compute_boundedCase16594FirstInverseQuadraticErrorEval
Libs
  bossLib preamble cv_transLib

Definition bounded_case16594_first_inverse_input_cv_def:
  bounded_case16594_first_inverse_input_cv =
    Pair
      (Pair (Pair (Num 1036597572434) (Num 0)) (Num 549755813887))
      (Pair (Pair (Num 1036652548017) (Num 0)) (Num 549755813887))
End

Definition bounded_case16594_first_inverse_source_state_cv_def:
  bounded_case16594_first_inverse_source_state_cv =
    bounded_case16594_object_state_cv
      (Num 1)
      bounded_case16594_first_inverse_input_cv
      bounded_case16594_zero_gradient6_cv
      bounded_case16594_first_inverse_input_cv
      bounded_case16594_zero_gradient6_cv
      bounded_case16594_zero_hessian21_cv
End

Definition bounded_case16594_first_inverse_state_cexp_def:
  bounded_case16594_first_inverse_state_cexp =
    App «candle_cv_q_packed_object_state_inverse»
      [from_cv bounded_case16594_first_inverse_radii_cv;
       from_cv bounded_case16594_first_inverse_reciprocal_cv;
       from_cv bounded_case16594_first_inverse_reciprocal_cv;
       from_cv bounded_case16594_first_inverse_source_state_cv]
End

val _ = cv_trans
  compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def;
val _ = cv_trans
  compute_boundedCase16594FirstInverseDerivativeEvalTheory.bounded_case16594_first_inverse_reciprocal_cv_def;
val _ = cv_trans
  compute_boundedCase16594FirstInverseZeroScaleEvalTheory.bounded_case16594_zero_q_cv_def;
val _ = cv_trans
  compute_boundedCase16594FirstInverseZeroScaleEvalTheory.bounded_case16594_zero_interval_cv_def;
val _ = cv_trans
  compute_boundedCase16594FirstInverseZeroScaleEvalTheory.bounded_case16594_zero_gradient6_cv_def;
val _ = cv_trans
  compute_boundedCase16594FirstInverseZeroScaleEvalTheory.bounded_case16594_zero_hessian21_cv_def;
val _ = cv_trans bounded_case16594_first_inverse_input_cv_def;
val _ = cv_trans bounded_case16594_first_inverse_source_state_cv_def;
val _ = cv_trans bounded_case16594_first_inverse_state_cexp_def;

val first_inverse_state_diagnostic =
  time cv_eval
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        bounded_case16594_first_inverse_state_cexp``;

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
    | _ => raise Fail "non-value compute expression in inverse-state result"
  end;

val first_inverse_result_state_cv_tm =
  compute_exp_value_to_cv
    (optionSyntax.dest_some (rhs (concl first_inverse_state_diagnostic)));

val _ =
  if type_of first_inverse_result_state_cv_tm = ``:cv`` then ()
  else raise Fail
    ("inverse-state result conversion has type " ^
     type_to_string (type_of first_inverse_result_state_cv_tm));

val bounded_case16594_first_inverse_result_state_cv_def =
  new_definition
    ("bounded_case16594_first_inverse_result_state_cv_def",
     mk_eq
       (mk_var
         ("bounded_case16594_first_inverse_result_state_cv",``:cv``),
        first_inverse_result_state_cv_tm));

Theorem bounded_case16594_first_inverse_state_pure_eval:
  compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      bounded_case16594_first_inverse_state_cexp =
    SOME (from_cv bounded_case16594_first_inverse_result_state_cv)
Proof
  rewrite_tac [bounded_case16594_first_inverse_result_state_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC first_inverse_state_diagnostic
QED

Theorem bounded_case16594_first_inverse_state_eval:
  4096 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      bounded_case16594_first_inverse_state_cexp (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_first_inverse_result_state_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac [bounded_case16594_first_inverse_state_pure_eval]
QED

val _ = export_theory ();
