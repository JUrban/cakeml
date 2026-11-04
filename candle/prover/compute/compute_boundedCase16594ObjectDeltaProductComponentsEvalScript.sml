(*****************************************************************************
 * Closed proof-producing evaluations of the reusable components of the
 * three authenticated 4*x_i*delta states in genuine case 16594.
 *
 * Full numerical evaluation of object-state recompletion needlessly expands
 * the large exact-rational value and gradient bounds.  These six component
 * results stop immediately before that shared boundary; the already-proved
 * structural recompletion evaluator can consume them without replaying those
 * folds numerically.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductComponentsEval
Ancestors
  compute_boundedCase16594ObjectDispatchPrefix8Eval
Libs
  bossLib preamble cv_transLib intLib

val _ = cv_trans
  compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def;
val _ = cv_trans
  compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_radii_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_center_boxes_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_outer_boxes_cv_def;

fun product_center_expression coordinate =
  ``compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [Num ^coordinate;
         from_cv bounded_case16594_object_cell0_center_boxes_cv])``;

fun product_hessian_expression coordinate =
  ``compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         Num ^coordinate])``;

val product0_center_diagnostic =
  time cv_eval (product_center_expression ``0:num``);
val product0_hessian_diagnostic =
  time cv_eval (product_hessian_expression ``0:num``);
val product1_center_diagnostic =
  time cv_eval (product_center_expression ``1:num``);
val product1_hessian_diagnostic =
  time cv_eval (product_hessian_expression ``1:num``);
val product2_center_diagnostic =
  time cv_eval (product_center_expression ``2:num``);
val product2_hessian_diagnostic =
  time cv_eval (product_hessian_expression ``2:num``);

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
    | _ => raise Fail "non-value genuine delta-product component result"
  end;

fun diagnostic_result_cv diagnostic =
  compute_exp_value_to_cv
    (optionSyntax.dest_some (rhs (concl diagnostic)));

fun define_cv_constant name tm =
  new_definition
    (name ^ "_def",mk_eq (mk_var (name,``:cv``),tm));

val bounded_case16594_object_delta_product0_center_jet_cv_def =
  define_cv_constant
    "bounded_case16594_object_delta_product0_center_jet_cv"
    (diagnostic_result_cv product0_center_diagnostic);
val bounded_case16594_object_delta_product0_hessian_cv_def =
  define_cv_constant
    "bounded_case16594_object_delta_product0_hessian_cv"
    (diagnostic_result_cv product0_hessian_diagnostic);
val bounded_case16594_object_delta_product1_center_jet_cv_def =
  define_cv_constant
    "bounded_case16594_object_delta_product1_center_jet_cv"
    (diagnostic_result_cv product1_center_diagnostic);
val bounded_case16594_object_delta_product1_hessian_cv_def =
  define_cv_constant
    "bounded_case16594_object_delta_product1_hessian_cv"
    (diagnostic_result_cv product1_hessian_diagnostic);
val bounded_case16594_object_delta_product2_center_jet_cv_def =
  define_cv_constant
    "bounded_case16594_object_delta_product2_center_jet_cv"
    (diagnostic_result_cv product2_center_diagnostic);
val bounded_case16594_object_delta_product2_hessian_cv_def =
  define_cv_constant
    "bounded_case16594_object_delta_product2_hessian_cv"
    (diagnostic_result_cv product2_hessian_diagnostic);

Theorem bounded_case16594_object_delta_product0_center_pure_eval:
  compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [Num 0;from_cv bounded_case16594_object_cell0_center_boxes_cv]) =
    SOME
      (from_cv bounded_case16594_object_delta_product0_center_jet_cv)
Proof
  rewrite_tac
    [bounded_case16594_object_delta_product0_center_jet_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC product0_center_diagnostic
QED

Theorem bounded_case16594_object_delta_product0_hessian_pure_eval:
  compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;Num 0]) =
    SOME (from_cv bounded_case16594_object_delta_product0_hessian_cv)
Proof
  rewrite_tac
    [bounded_case16594_object_delta_product0_hessian_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC product0_hessian_diagnostic
QED

Theorem bounded_case16594_object_delta_product1_center_pure_eval:
  compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [Num 1;from_cv bounded_case16594_object_cell0_center_boxes_cv]) =
    SOME
      (from_cv bounded_case16594_object_delta_product1_center_jet_cv)
Proof
  rewrite_tac
    [bounded_case16594_object_delta_product1_center_jet_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC product1_center_diagnostic
QED

Theorem bounded_case16594_object_delta_product1_hessian_pure_eval:
  compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;Num 1]) =
    SOME (from_cv bounded_case16594_object_delta_product1_hessian_cv)
Proof
  rewrite_tac
    [bounded_case16594_object_delta_product1_hessian_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC product1_hessian_diagnostic
QED

Theorem bounded_case16594_object_delta_product2_center_pure_eval:
  compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [Num 2;from_cv bounded_case16594_object_cell0_center_boxes_cv]) =
    SOME
      (from_cv bounded_case16594_object_delta_product2_center_jet_cv)
Proof
  rewrite_tac
    [bounded_case16594_object_delta_product2_center_jet_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC product2_center_diagnostic
QED

Theorem bounded_case16594_object_delta_product2_hessian_pure_eval:
  compute_eval_pure 65536 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;Num 2]) =
    SOME (from_cv bounded_case16594_object_delta_product2_hessian_cv)
Proof
  rewrite_tac
    [bounded_case16594_object_delta_product2_hessian_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC product2_hessian_diagnostic
QED

Theorem bounded_case16594_object_delta_product0_center_eval:
  65536 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [Num 0;from_cv bounded_case16594_object_cell0_center_boxes_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_delta_product0_center_jet_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `65536`
  >> simp [bounded_case16594_object_delta_product0_center_pure_eval]
QED

Theorem bounded_case16594_object_delta_product0_hessian_eval:
  65536 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;Num 0])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_delta_product0_hessian_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `65536`
  >> simp [bounded_case16594_object_delta_product0_hessian_pure_eval]
QED

Theorem bounded_case16594_object_delta_product1_center_eval:
  65536 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [Num 1;from_cv bounded_case16594_object_cell0_center_boxes_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_delta_product1_center_jet_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `65536`
  >> simp [bounded_case16594_object_delta_product1_center_pure_eval]
QED

Theorem bounded_case16594_object_delta_product1_hessian_eval:
  65536 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;Num 1])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_delta_product1_hessian_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `65536`
  >> simp [bounded_case16594_object_delta_product1_hessian_pure_eval]
QED

Theorem bounded_case16594_object_delta_product2_center_eval:
  65536 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_environment»
        [Num 2;from_cv bounded_case16594_object_cell0_center_boxes_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_delta_product2_center_jet_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `65536`
  >> simp [bounded_case16594_object_delta_product2_center_pure_eval]
QED

Theorem bounded_case16594_object_delta_product2_hessian_eval:
  65536 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_hessian»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;Num 2])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_delta_product2_hessian_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `65536`
  >> simp [bounded_case16594_object_delta_product2_hessian_pure_eval]
QED

val _ = export_theory ();
