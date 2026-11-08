(*****************************************************************************
 * Complete exact evaluator theorem for the production compact delta Hessian.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaHessianCompleteEval
Ancestors
  compute_boundedCase16594ObjectDeltaHessianEval
Libs
  bossLib preamble intLib

val inherited_object_q_cv_list_def =
  DB.fetch "compute_boundedPackedObjectEntryContract"
    "bounded_object_q_cv_list_def";
val inherited_let_result =
  DB.fetch "compute_boundedCase16594ObjectDispatchProgramTraceEval"
    "bounded_case16594_object_compute_eval_let_result";
val inherited_pair_from_raw_results =
  DB.fetch "compute_boundedCase16594ObjectPolyStepControlEval"
    "bounded_case16594_object_compute_eval_pair_from_raw_results";
val inherited_compute_eval_num =
  DB.fetch "compute_boundedCase16594ObjectPolyStepControlEval"
    "bounded_case16594_object_compute_eval_num";
val inherited_delta_two_eval =
  DB.fetch "compute_boundedCase16594ObjectDeltaHessianPrimitiveEval"
    "bounded_case16594_object_delta_two_eval";
val inherited_delta_three_eval =
  DB.fetch "compute_boundedCase16594ObjectDeltaHessianPrimitiveEval"
    "bounded_case16594_object_delta_three_eval";
val inherited_delta_eight_eval =
  DB.fetch "compute_boundedCase16594ObjectDeltaHessianPrimitiveEval"
    "bounded_case16594_object_delta_eight_eval";

Theorem bounded_case16594_object_delta_two_raw_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_two» [from_cv a;from_cv b])
      (refs:hol_refs) =
    (M_success (Pair (from_cv a) (Pair (from_cv b) (Num 0))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `(M_success (from_cv (bounded_object_q_cv_list [a;b])),refs)`
  >> conj_tac
  >- (irule inherited_delta_two_eval
      >> intLib.ARITH_TAC)
  >> simp [inherited_object_q_cv_list_def,compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_delta_row_pair_eval:
  compute_eval clock ceqs row_expression (refs:hol_refs) =
      (M_success (from_cv row),refs) /\
  compute_eval clock ceqs rest_expression refs =
      (M_success (from_cv rest),refs) ==>
  compute_eval clock ceqs
      (Pair row_expression rest_expression) refs =
    (M_success (from_cv (Pair row rest)),refs)
Proof
  strip_tac
  >> simp [compute_execTheory.from_cv_def]
  >> irule inherited_pair_from_raw_results
  >> simp []
QED

fun bounded_case16594_object_delta_hessian_neg_let_tac result =
  irule inherited_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac result
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_packed_interval_neg_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv];

val bounded_case16594_object_delta_hessian_stack = ref “Num 0”;

fun bounded_case16594_object_delta_hessian_row_cons_let_tac row eval_theorem =
  let
    val row_term = Parse.Term row
    val result =
      “Pair (bounded_object_q_cv_list ^row_term)
          ^(!bounded_case16594_object_delta_hessian_stack)”
    val tactic =
      irule inherited_let_result
      >> conj_tac >- intLib.ARITH_TAC
      >> exists_tac result
      >> conj_tac
      >- (irule bounded_case16594_object_delta_row_pair_eval
          >> conj_tac
          >- simp
               [compute_evalTheory.compute_eval_def,
                compute_execProofTheory.compute_eval_from_cv,
                inherited_compute_eval_num,
                ml_monadBaseTheory.st_ex_bind_def,
                ml_monadBaseTheory.st_ex_return_def]
          >> irule eval_theorem
          >> intLib.ARITH_TAC)
      >> simp
           [compute_evalTheory.subst_def,
            compute_execProofTheory.subst_from_cv]
  in
    bounded_case16594_object_delta_hessian_stack := result;
    tactic
  end;

Theorem bounded_case16594_object_delta_hessian_rows_six_eval:
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] /\
  65536 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_hessian_rows_six»
        [from_cv x0;from_cv x1;from_cv x2;from_cv x3;from_cv x4;
         from_cv x5]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (MAP bounded_object_q_cv_list
            (bounded_case16594_object_delta_hessian_rows_six_cv
              x0 x1 x2 x3 x4 x5)))),refs)
Proof
  strip_tac
  >> fs []
  >> rw
       [compute_boundedCase16594ObjectDeltaHessianEvalTheory.bounded_case16594_object_delta_hessian_rows_six_unfold]
  >> simp
       [compute_boundedCase16594ObjectDeltaHessianEvalTheory.bounded_case16594_object_delta_hessian_rows_six_body_def,
        compute_evalTheory.subst_def]
  >> bounded_case16594_object_delta_hessian_neg_let_tac
       `bounded_object_q_interval_neg_cv x0`
  >> bounded_case16594_object_delta_hessian_neg_let_tac
       `bounded_object_q_interval_neg_cv x1`
  >> bounded_case16594_object_delta_hessian_neg_let_tac
       `bounded_object_q_interval_neg_cv x2`
  >> bounded_case16594_object_delta_hessian_neg_let_tac
       `bounded_object_q_interval_neg_cv x3`
  >> bounded_case16594_object_delta_hessian_neg_let_tac
       `bounded_object_q_interval_neg_cv x4`
  >> bounded_case16594_object_delta_hessian_neg_let_tac
       `bounded_object_q_interval_neg_cv x5`
  >> irule inherited_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `Num 0`
  >> conj_tac
  >- simp [inherited_compute_eval_num]
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[bounded_object_q_interval_neg_cv x2;
          bounded_object_q_interval_neg_cv x2]` inherited_delta_two_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[x1;x2;bounded_object_q_interval_neg_cv x3]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[bounded_object_q_interval_neg_cv x1;
          bounded_object_q_interval_neg_cv x1]` inherited_delta_two_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[x0;x2;bounded_object_q_interval_neg_cv x4]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[x0;x1;bounded_object_q_interval_neg_cv x5]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[bounded_object_q_interval_neg_cv x0;
          bounded_object_q_interval_neg_cv x0]` inherited_delta_two_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[x0;x1;bounded_object_q_interval_neg_cv x2;
          bounded_object_q_interval_neg_cv x2;x3;x4;
          bounded_object_q_interval_neg_cv x5;
          bounded_object_q_interval_neg_cv x5]` inherited_delta_eight_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[bounded_object_q_interval_neg_cv x0;x1;x5]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[x0;bounded_object_q_interval_neg_cv x1;x5]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[bounded_object_q_interval_neg_cv x5;
          bounded_object_q_interval_neg_cv x5]` inherited_delta_two_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[bounded_object_q_interval_neg_cv x0;x2;x4]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[x0;bounded_object_q_interval_neg_cv x1;
          bounded_object_q_interval_neg_cv x1;x2;x3;
          bounded_object_q_interval_neg_cv x4;
          bounded_object_q_interval_neg_cv x4;x5]` inherited_delta_eight_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[x0;bounded_object_q_interval_neg_cv x2;x4]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[bounded_object_q_interval_neg_cv x3;x4;x5]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[bounded_object_q_interval_neg_cv x4;
          bounded_object_q_interval_neg_cv x4]` inherited_delta_two_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[bounded_object_q_interval_neg_cv x1;x2;x3]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[x1;bounded_object_q_interval_neg_cv x2;x3]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[bounded_object_q_interval_neg_cv x0;
          bounded_object_q_interval_neg_cv x0;x1;x2;
          bounded_object_q_interval_neg_cv x3;
          bounded_object_q_interval_neg_cv x3;x4;x5]` inherited_delta_eight_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[x3;bounded_object_q_interval_neg_cv x4;x5]` inherited_delta_three_eval
  >> bounded_case16594_object_delta_hessian_row_cons_let_tac
       `[x3;x4;bounded_object_q_interval_neg_cv x5]` inherited_delta_three_eval
  >> rw
       [compute_boundedCase16594ObjectDeltaHessianEvalTheory.bounded_case16594_object_delta_hessian_rows_six_cv_def,
        inherited_object_q_cv_list_def]
  >> irule inherited_pair_from_raw_results
  >> conj_tac
  >- (irule bounded_case16594_object_delta_two_raw_eval
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        inherited_compute_eval_num,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
