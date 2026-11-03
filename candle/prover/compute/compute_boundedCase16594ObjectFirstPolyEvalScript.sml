(*****************************************************************************
 * Exact evaluator and production-dispatch result for the first genuine
 * case-16594 polynomial source.
 *
 * The first negation result is supplied by the preceding theory.  This file
 * computes the final multiplication with the verified CV evaluator, then
 * proves the four instruction steps, recursive runner trace, and ordinary
 * dispatch wrapper without monolithic replay.
 *****************************************************************************)
open compute_boundedCase16594ObjectPolyStepControlEvalTheory
open compute_boundedCase16594ObjectFirstNegEvalTheory
open compute_boundedCase16594ObjectPolyTraceEvalTheory

Theory compute_boundedCase16594ObjectFirstPolyEval
Ancestors
  compute_boundedCase16594ObjectFirstNegEval
  compute_boundedCase16594ObjectPolyTraceEval
  compute_boundedCase16594ObjectDispatchStepControlEval
Libs
  bossLib preamble cv_transLib intLib

Definition bounded_case16594_object_first_one_state_cv_def:
  bounded_case16594_object_first_one_state_cv =
    bounded_case16594_object_constant_state_cv
      (Pair (Pair (Num 1) (Num 0)) (Num 0))
End

Definition bounded_case16594_object_first_thirteen_state_cv_def:
  bounded_case16594_object_first_thirteen_state_cv =
    bounded_case16594_object_constant_state_cv
      (Pair (Pair (Num 13) (Num 0)) (Num 499))
End

Definition bounded_case16594_object_first_neg_state_cv_def:
  bounded_case16594_object_first_neg_state_cv =
    bounded_case16594_object_state_cv
      (Num 1)
      (Pair (Pair (Pair (Num 0) (Num 13)) (Num 499))
        (Pair (Pair (Num 0) (Num 13)) (Num 499)))
      bounded_case16594_object_zero_gradient6_cv
      bounded_case16594_object_first_neg_value_result_cv
      bounded_case16594_object_first_neg_gradient_result_cv
      bounded_case16594_object_zero_hessian21_cv
End

Definition bounded_case16594_object_first_poly_program_cv_def:
  bounded_case16594_object_first_poly_program_cv =
    Pair (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
      (Pair (Pair (Num 0) (Pair (Pair (Num 13) (Num 0)) (Num 499)))
        (Pair (Num 2) (Pair (Num 4) (Num 0))))
End

Theorem bounded_case16594_object_source0_runtime_identity:
  bounded_case16594_object_cell0_source0_cv =
    Pair (Num 0) bounded_case16594_object_first_poly_program_cv
Proof
  simp
    [compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_source0_cv_def,
     bounded_case16594_object_first_poly_program_cv_def]
QED

val _ = cv_trans
  compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_constant_state_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectFirstNegEvalTheory.bounded_case16594_object_first_neg_gradient_result_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectFirstNegEvalTheory.bounded_case16594_object_first_neg_value_result_cv_def;
val _ = cv_trans bounded_case16594_object_first_one_state_cv_def;
val _ = cv_trans bounded_case16594_object_first_neg_state_cv_def;

val first_mul_diagnostic =
  time cv_eval
    ``compute_eval_pure 16384 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_state_mul»
          [from_cv bounded_case16594_object_cell0_radii_cv;
           from_cv bounded_case16594_object_first_one_state_cv;
           from_cv bounded_case16594_object_first_neg_state_cv])``;

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
    | _ => raise Fail "non-value compute expression in first product result"
  end;

val first_mul_result_cv_tm =
  compute_exp_value_to_cv
    (optionSyntax.dest_some (rhs (concl first_mul_diagnostic)));

val bounded_case16594_object_first_mul_result_cv_def =
  new_definition
    ("bounded_case16594_object_first_mul_result_cv_def",
     mk_eq
       (mk_var
         ("bounded_case16594_object_first_mul_result_cv",``:cv``),
        first_mul_result_cv_tm));

Theorem bounded_case16594_object_first_mul_pure_eval:
  compute_eval_pure 16384 bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_mul»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_first_one_state_cv;
         from_cv bounded_case16594_object_first_neg_state_cv]) =
    SOME (from_cv bounded_case16594_object_first_mul_result_cv)
Proof
  rewrite_tac [bounded_case16594_object_first_mul_result_cv_def]
  >> CONV_TAC (RAND_CONV EVAL)
  >> ACCEPT_TAC first_mul_diagnostic
QED

Theorem bounded_case16594_object_first_mul_eval:
  16384 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_mul»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_first_one_state_cv;
         from_cv bounded_case16594_object_first_neg_state_cv])
      (refs:hol_refs) =
    (M_success (from_cv bounded_case16594_object_first_mul_result_cv),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `16384`
  >> asm_rewrite_tac [bounded_case16594_object_first_mul_pure_eval]
QED

Theorem bounded_case16594_object_first_one_step_eval:
  3 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)));
         from_cv (Num 0)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair bounded_case16594_object_first_one_state_cv (Num 0)))),refs)
Proof
  strip_tac
  >> rewrite_tac [bounded_case16594_object_first_one_state_cv_def]
  >> irule bounded_case16594_object_poly_step_constant_eval_from_state
  >> conj_tac >- intLib.ARITH_TAC
  >> irule bounded_case16594_object_constant_state_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_first_thirteen_step_eval:
  3 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv
           (Pair (Num 0) (Pair (Pair (Num 13) (Num 0)) (Num 499)));
         from_cv
           (Pair bounded_case16594_object_first_one_state_cv (Num 0))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair bounded_case16594_object_first_thirteen_state_cv
            (Pair bounded_case16594_object_first_one_state_cv (Num 0))))),refs)
Proof
  strip_tac
  >> rewrite_tac [bounded_case16594_object_first_thirteen_state_cv_def]
  >> irule bounded_case16594_object_poly_step_constant_eval_from_state
  >> conj_tac >- intLib.ARITH_TAC
  >> irule bounded_case16594_object_constant_state_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_first_neg_step_eval:
  4102 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv (Num 2);
         from_cv
           (Pair bounded_case16594_object_first_thirteen_state_cv
             (Pair bounded_case16594_object_first_one_state_cv (Num 0)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair bounded_case16594_object_first_neg_state_cv
            (Pair bounded_case16594_object_first_one_state_cv (Num 0))))),refs)
Proof
  strip_tac
  >> rewrite_tac
       [bounded_case16594_object_first_thirteen_state_cv_def,
        bounded_case16594_object_first_neg_state_cv_def]
  >> irule bounded_case16594_object_poly_step_neg_eval_from_state
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       compute_boundedCase16594ObjectFirstNegEvalTheory.bounded_case16594_object_first_neg_state_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_first_mul_step_eval:
  16385 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv (Num 4);
         from_cv
           (Pair bounded_case16594_object_first_neg_state_cv
             (Pair bounded_case16594_object_first_one_state_cv (Num 0)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair bounded_case16594_object_first_mul_result_cv (Num 0)))),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_poly_step_mul_eval_from_state
  >> conj_tac >- intLib.ARITH_TAC
  >> irule bounded_case16594_object_first_mul_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_first_one_step_above:
  bounded_case16594_object_poly_step_eval_above 16384
    center_boxes outer_boxes bounded_case16594_object_cell0_radii_cv
    (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0))) (Num 0)
    (Pair bounded_case16594_object_first_one_state_cv (Num 0))
Proof
  PURE_REWRITE_TAC [bounded_case16594_object_poly_step_eval_above_def]
  >> rpt gen_tac >> strip_tac
  >> MATCH_MP_TAC bounded_case16594_object_first_one_step_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_first_thirteen_step_above:
  bounded_case16594_object_poly_step_eval_above 16384
    center_boxes outer_boxes bounded_case16594_object_cell0_radii_cv
    (Pair (Num 0) (Pair (Pair (Num 13) (Num 0)) (Num 499)))
    (Pair bounded_case16594_object_first_one_state_cv (Num 0))
    (Pair bounded_case16594_object_first_thirteen_state_cv
      (Pair bounded_case16594_object_first_one_state_cv (Num 0)))
Proof
  PURE_REWRITE_TAC [bounded_case16594_object_poly_step_eval_above_def]
  >> rpt gen_tac >> strip_tac
  >> MATCH_MP_TAC bounded_case16594_object_first_thirteen_step_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_first_neg_step_above:
  bounded_case16594_object_poly_step_eval_above 16384
    center_boxes outer_boxes bounded_case16594_object_cell0_radii_cv
    (Num 2)
    (Pair bounded_case16594_object_first_thirteen_state_cv
      (Pair bounded_case16594_object_first_one_state_cv (Num 0)))
    (Pair bounded_case16594_object_first_neg_state_cv
      (Pair bounded_case16594_object_first_one_state_cv (Num 0)))
Proof
  PURE_REWRITE_TAC [bounded_case16594_object_poly_step_eval_above_def]
  >> rpt gen_tac >> strip_tac
  >> MATCH_MP_TAC bounded_case16594_object_first_neg_step_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_first_mul_step_above:
  bounded_case16594_object_poly_step_eval_above 16384
    center_boxes outer_boxes bounded_case16594_object_cell0_radii_cv
    (Num 4)
    (Pair bounded_case16594_object_first_neg_state_cv
      (Pair bounded_case16594_object_first_one_state_cv (Num 0)))
    (Pair bounded_case16594_object_first_mul_result_cv (Num 0))
Proof
  PURE_REWRITE_TAC [bounded_case16594_object_poly_step_eval_above_def]
  >> rpt gen_tac >> strip_tac
  >> MATCH_MP_TAC bounded_case16594_object_first_mul_step_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_first_poly_trace:
  bounded_case16594_object_poly_program_trace 16384
    center_boxes outer_boxes bounded_case16594_object_cell0_radii_cv
    bounded_case16594_object_first_poly_program_cv (Num 0)
    (Pair bounded_case16594_object_first_mul_result_cv (Num 0))
Proof
  simp
    [bounded_case16594_object_first_poly_program_cv_def,
     bounded_case16594_object_poly_program_trace_def]
  >> metis_tac
       [bounded_case16594_object_first_one_step_above,
        bounded_case16594_object_first_thirteen_step_above,
        bounded_case16594_object_first_neg_step_above,
        bounded_case16594_object_first_mul_step_above]
QED

val first_poly_run_sound =
  Q.SPECL
    [`bounded_case16594_object_first_poly_program_cv`,`Num 0`,
     `Pair bounded_case16594_object_first_mul_result_cv (Num 0)`,
     `clock`,`refs`]
    (Q.INST
      [`step_floor` |-> `16384`,
       `center_boxes` |-> `center_boxes`,
       `outer_boxes` |-> `outer_boxes`,
       `radii` |-> `bounded_case16594_object_cell0_radii_cv`]
      compute_boundedCase16594ObjectPolyTraceEvalTheory.bounded_case16594_object_poly_program_trace_sound);

Theorem bounded_case16594_object_first_poly_run_eval:
  16390 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv bounded_case16594_object_first_poly_program_cv;
         from_cv (Pair (Num 1) (Num 0))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair bounded_case16594_object_first_mul_result_cv (Num 0)))),refs)
Proof
  strip_tac
  >> MATCH_MP_TAC first_poly_run_sound
  >> conj_tac >- MATCH_ACCEPT_TAC bounded_case16594_object_first_poly_trace
  >> simp
       [bounded_case16594_object_first_poly_program_cv_def,
        compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_cv_list_length_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_eval_tagged_pair:
  compute_eval clock ceqs (Pair (Num 0) (from_cv program))
      (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 0) program)),refs)
Proof
  PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- MATCH_ACCEPT_TAC bounded_case16594_object_compute_eval_num
  >> MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv
QED

Theorem bounded_case16594_object_eval_snd_tagged_pair:
  compute_eval clock ceqs
      (Uop Snd (from_cv (Pair (Num 0) program))) (refs:hol_refs) =
    (M_success (from_cv program),refs)
Proof
  PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> PURE_ONCE_REWRITE_TAC [compute_evalTheory.compute_eval_def]
  >> sg
       `compute_eval clock ceqs (Pair (Num 0) (from_cv program)) refs =
          (M_success (Pair (Num 0) (from_cv program)),refs)`
  >- MATCH_ACCEPT_TAC
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_eval_tagged_pair)
  >> asm_rewrite_tac []
  >> simp
       [compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_poly_run_arguments_normalize:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         Uop Snd (from_cv (Pair (Num 0) program));
         Pair (Num 1) (Num 0)]) (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv program;from_cv (Pair (Num 1) (Num 0))]) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyTraceEvalTheory.bounded_case16594_object_compute_eval_app5_argument_results
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv
  >> conj_tac >- MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv
  >> conj_tac >- MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv
  >> conj_tac >- MATCH_ACCEPT_TAC bounded_case16594_object_eval_snd_tagged_pair
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule bounded_case16594_object_compute_eval_pair_from_raw_results
  >> simp [bounded_case16594_object_compute_eval_num]
QED

Theorem bounded_case16594_object_first_poly_expression_eval:
  16390 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv bounded_case16594_object_cell0_radii_cv;
         Uop Snd
           (from_cv
             (Pair (Num 0)
               bounded_case16594_object_first_poly_program_cv));
         Pair (Num 1) (Num 0)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair bounded_case16594_object_first_mul_result_cv (Num 0)))),refs)
Proof
  strip_tac
  >> sg `0:num < clock` >- intLib.ARITH_TAC
  >> PURE_ONCE_REWRITE_TAC
       [MATCH_MP
          (Q.INST
            [`program` |->
               `bounded_case16594_object_first_poly_program_cv`]
            bounded_case16594_object_poly_run_arguments_normalize)
          (ASSUME ``0:num < clock``)]
  >> MATCH_MP_TAC bounded_case16594_object_first_poly_run_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_first_poly_ordinary_eval:
  16391 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_ordinary_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv
           (Pair (Num 0) bounded_case16594_object_first_poly_program_cv);
         from_cv certificates;from_cv stack]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (Pair bounded_case16594_object_first_mul_result_cv stack)
            certificates))),refs)
Proof
  strip_tac
  >> MATCH_MP_TAC
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_poly_success_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> MATCH_MP_TAC bounded_case16594_object_first_poly_expression_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_first_poly_dispatch_step_eval:
  16392 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv (Num 0);
         from_cv
           (Pair (Num 0) bounded_case16594_object_first_poly_program_cv);
         from_cv certificates;from_cv stack]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (Pair bounded_case16594_object_first_mul_result_cv stack)
            certificates))),refs)
Proof
  strip_tac
  >> MATCH_MP_TAC
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> MATCH_MP_TAC bounded_case16594_object_first_poly_ordinary_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_source0_dispatch_step_eval:
  16392 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv (Num 0);
         from_cv bounded_case16594_object_cell0_source0_cv;
         from_cv certificates;from_cv stack]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (Pair bounded_case16594_object_first_mul_result_cv stack)
            certificates))),refs)
Proof
  strip_tac
  >> rewrite_tac [bounded_case16594_object_source0_runtime_identity]
  >> MATCH_MP_TAC bounded_case16594_object_first_poly_dispatch_step_eval
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
