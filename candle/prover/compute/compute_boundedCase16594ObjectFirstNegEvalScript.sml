(*****************************************************************************
 * Closed proof-producing evaluation of the first genuine object negation.
 *
 * The production rational operations intentionally do not normalize their
 * results.  In particular, recompleting a mathematically constant state does
 * not return the canonical zero-gradient representation.  We therefore
 * compute and name the exact evaluator results, rather than assuming a
 * representation-level zero identity.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectFirstNegEval
Ancestors
  compute_boundedCase16594ObjectStateNegEval
  compute_boundedCase16594ObjectDispatchPrefix8Eval
Libs
  bossLib preamble cv_transLib intLib

val _ = cv_trans
  compute_boundedCase16594ObjectDispatchCell0DataTheory.bounded_case16594_object_dispatch_cell0_ceqs_def;
val _ = cv_trans
  compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_radii_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_cv_list_def;
val _ = cv_trans
  compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_zero_interval_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_zero_gradient6_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_zero_hessian21_cv_def;

val first_neg_gradient_diagnostic =
  time cv_eval
    ``compute_eval_pure 2048 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_gradient_complete6»
          [from_cv bounded_case16594_object_cell0_radii_cv;
           from_cv bounded_case16594_object_zero_gradient6_cv;
           from_cv bounded_case16594_object_zero_hessian21_cv])``;

val first_neg_value_diagnostic =
  time cv_eval
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_value_bound6»
          [from_cv bounded_case16594_object_cell0_radii_cv;
           from_cv
             (Pair (Pair (Pair (Num 0) (Num 13)) (Num 499))
               (Pair (Pair (Num 0) (Num 13)) (Num 499)));
           from_cv bounded_case16594_object_zero_gradient6_cv;
           from_cv bounded_case16594_object_zero_hessian21_cv])``;

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
    | _ => raise Fail "non-value compute expression in first negation result"
  end;

val first_neg_gradient_result_cv_tm =
  compute_exp_value_to_cv
    (optionSyntax.dest_some
      (rhs (concl first_neg_gradient_diagnostic)));

val first_neg_value_result_cv_tm =
  compute_exp_value_to_cv
    (optionSyntax.dest_some
      (rhs (concl first_neg_value_diagnostic)));

val bounded_case16594_object_first_neg_gradient_result_cv_def =
  new_definition
    ("bounded_case16594_object_first_neg_gradient_result_cv_def",
     mk_eq
       (mk_var
         ("bounded_case16594_object_first_neg_gradient_result_cv",``:cv``),
        first_neg_gradient_result_cv_tm));

val bounded_case16594_object_first_neg_value_result_cv_def =
  new_definition
    ("bounded_case16594_object_first_neg_value_result_cv_def",
     mk_eq
       (mk_var
         ("bounded_case16594_object_first_neg_value_result_cv",``:cv``),
        first_neg_value_result_cv_tm));

Theorem bounded_case16594_object_first_neg_gradient_pure_eval:
  compute_eval_pure 2048 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_complete6»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv]) =
    SOME (from_cv bounded_case16594_object_first_neg_gradient_result_cv)
Proof
  rewrite_tac [bounded_case16594_object_first_neg_gradient_result_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC first_neg_gradient_diagnostic
QED

Theorem bounded_case16594_object_first_neg_value_pure_eval:
  compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_value_bound6»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv
           (Pair (Pair (Pair (Num 0) (Num 13)) (Num 499))
             (Pair (Pair (Num 0) (Num 13)) (Num 499)));
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv]) =
    SOME (from_cv bounded_case16594_object_first_neg_value_result_cv)
Proof
  rewrite_tac [bounded_case16594_object_first_neg_value_result_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC first_neg_value_diagnostic
QED

Theorem bounded_case16594_object_first_neg_gradient_eval:
  2048 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_complete6»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_first_neg_gradient_result_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `2048`
  >> asm_rewrite_tac [bounded_case16594_object_first_neg_gradient_pure_eval]
QED

Theorem bounded_case16594_object_first_neg_value_eval:
  4096 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_value_bound6»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv
           (Pair (Pair (Pair (Num 0) (Num 13)) (Num 499))
             (Pair (Pair (Num 0) (Num 13)) (Num 499)));
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_first_neg_value_result_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac [bounded_case16594_object_first_neg_value_pure_eval]
QED

val first_neg_state_from_bounds =
  Q.INST
    [`radii` |-> `bounded_case16594_object_cell0_radii_cv`,
     `positive` |-> `Num 13`,
     `negative` |-> `Num 0`,
     `denominator` |-> `Num 499`,
     `value_bound` |->
       `bounded_case16594_object_first_neg_value_result_cv`,
     `gradient_bounds` |->
       `bounded_case16594_object_first_neg_gradient_result_cv`]
    compute_boundedCase16594ObjectStateNegEvalTheory.bounded_case16594_object_state_neg_constant_eval_from_bounds;

Theorem bounded_case16594_object_first_neg_state_eval:
  4101 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_neg»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv
           (bounded_case16594_object_constant_state_cv
             (Pair (Pair (Num 13) (Num 0)) (Num 499)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv
          (Num 1)
          (Pair (Pair (Pair (Num 0) (Num 13)) (Num 499))
            (Pair (Pair (Num 0) (Num 13)) (Num 499)))
          bounded_case16594_object_zero_gradient6_cv
          bounded_case16594_object_first_neg_value_result_cv
          bounded_case16594_object_first_neg_gradient_result_cv
          bounded_case16594_object_zero_hessian21_cv)),refs)
Proof
  strip_tac
  >> MATCH_MP_TAC first_neg_state_from_bounds
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (MATCH_MP_TAC bounded_case16594_object_first_neg_value_eval
      >> intLib.ARITH_TAC)
  >> MATCH_MP_TAC bounded_case16594_object_first_neg_gradient_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
