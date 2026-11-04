(*****************************************************************************
 * Closed proof-producing evaluations of the three authenticated
 * -d(delta)/dx_i instructions in the genuine case-16594 program.
 *
 * These are deliberately kept separate from the product-delta instructions:
 * the latter have a materially different evaluator cost and need their own
 * bounded experiment.  The inputs below are extracted by the authenticated
 * cell-0 fixture, not copied numerical examples.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaNegSpecialEval
Ancestors
  compute_boundedCase16594ObjectDispatchPrefix8Eval
  compute_boundedCase16594ObjectDispatchStepAboveEval
Libs
  bossLib preamble cv_transLib intLib

val _ = cv_trans
  compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def;
val _ = cv_trans
  compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_radii_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_center_boxes_cv_def;

fun genuine_neg_expression coordinate =
  ``compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;
         Num ^coordinate])``;

val genuine_neg3_diagnostic =
  time cv_eval (genuine_neg_expression ``3:num``);
val genuine_neg4_diagnostic =
  time cv_eval (genuine_neg_expression ``4:num``);
val genuine_neg5_diagnostic =
  time cv_eval (genuine_neg_expression ``5:num``);

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
    | _ => raise Fail "non-value genuine delta-neg evaluator result"
  end;

fun diagnostic_result_cv diagnostic =
  compute_exp_value_to_cv
    (optionSyntax.dest_some (rhs (concl diagnostic)));

fun define_cv_constant name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val bounded_case16594_object_delta_neg3_result_cv_def =
  define_cv_constant "bounded_case16594_object_delta_neg3_result_cv"
    (diagnostic_result_cv genuine_neg3_diagnostic);
val bounded_case16594_object_delta_neg4_result_cv_def =
  define_cv_constant "bounded_case16594_object_delta_neg4_result_cv"
    (diagnostic_result_cv genuine_neg4_diagnostic);
val bounded_case16594_object_delta_neg5_result_cv_def =
  define_cv_constant "bounded_case16594_object_delta_neg5_result_cv"
    (diagnostic_result_cv genuine_neg5_diagnostic);

Theorem bounded_case16594_object_delta_neg3_pure_eval:
  compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;Num 3]) =
    SOME (from_cv bounded_case16594_object_delta_neg3_result_cv)
Proof
  rewrite_tac [bounded_case16594_object_delta_neg3_result_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC genuine_neg3_diagnostic
QED

Theorem bounded_case16594_object_delta_neg4_pure_eval:
  compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;Num 4]) =
    SOME (from_cv bounded_case16594_object_delta_neg4_result_cv)
Proof
  rewrite_tac [bounded_case16594_object_delta_neg4_result_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC genuine_neg4_diagnostic
QED

Theorem bounded_case16594_object_delta_neg5_pure_eval:
  compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;Num 5]) =
    SOME (from_cv bounded_case16594_object_delta_neg5_result_cv)
Proof
  rewrite_tac [bounded_case16594_object_delta_neg5_result_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC genuine_neg5_diagnostic
QED

Theorem bounded_case16594_object_delta_neg3_eval_above:
  bounded_case16594_object_expression_eval_above 65535
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;Num 3])
      bounded_case16594_object_delta_neg3_result_cv
Proof
  rw [compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_expression_eval_above_def]
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `65536`
  >> simp [bounded_case16594_object_delta_neg3_pure_eval]
QED

Theorem bounded_case16594_object_delta_neg4_eval_above:
  bounded_case16594_object_expression_eval_above 65535
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;Num 4])
      bounded_case16594_object_delta_neg4_result_cv
Proof
  rw [compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_expression_eval_above_def]
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `65536`
  >> simp [bounded_case16594_object_delta_neg4_pure_eval]
QED

Theorem bounded_case16594_object_delta_neg5_eval_above:
  bounded_case16594_object_expression_eval_above 65535
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;Num 5])
      bounded_case16594_object_delta_neg5_result_cv
Proof
  rw [compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_expression_eval_above_def]
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `65536`
  >> simp [bounded_case16594_object_delta_neg5_pure_eval]
QED

Theorem bounded_case16594_object_delta_neg3_dispatch_eval_above:
  bounded_case16594_object_dispatch_step_eval_above 65537
      bounded_case16594_object_cell0_center_boxes_cv
      bounded_case16594_object_cell0_outer_boxes_cv
      bounded_case16594_object_cell0_radii_cv (Num 4)
      bounded_case16594_object_source34_cv certificates stack
      (Pair bounded_case16594_object_delta_neg3_result_cv stack)
      certificates
Proof
  irule
    (SIMP_RULE std_ss []
      (Q.INST [`numeric_floor` |-> `65535`]
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_neg3_eval_above))
  >> ACCEPT_TAC bounded_case16594_object_delta_neg3_eval_above
QED

Theorem bounded_case16594_object_delta_neg4_dispatch_eval_above:
  bounded_case16594_object_dispatch_step_eval_above 65537
      bounded_case16594_object_cell0_center_boxes_cv
      bounded_case16594_object_cell0_outer_boxes_cv
      bounded_case16594_object_cell0_radii_cv (Num 5)
      bounded_case16594_object_source77_cv certificates stack
      (Pair bounded_case16594_object_delta_neg4_result_cv stack)
      certificates
Proof
  irule
    (SIMP_RULE std_ss []
      (Q.INST [`numeric_floor` |-> `65535`]
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_neg4_eval_above))
  >> ACCEPT_TAC bounded_case16594_object_delta_neg4_eval_above
QED

Theorem bounded_case16594_object_delta_neg5_dispatch_eval_above:
  bounded_case16594_object_dispatch_step_eval_above 65537
      bounded_case16594_object_cell0_center_boxes_cv
      bounded_case16594_object_cell0_outer_boxes_cv
      bounded_case16594_object_cell0_radii_cv (Num 6)
      bounded_case16594_object_source120_cv certificates stack
      (Pair bounded_case16594_object_delta_neg5_result_cv stack)
      certificates
Proof
  irule
    (SIMP_RULE std_ss []
      (Q.INST [`numeric_floor` |-> `65535`]
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_neg5_eval_above))
  >> ACCEPT_TAC bounded_case16594_object_delta_neg5_eval_above
QED

val _ = export_theory ();
