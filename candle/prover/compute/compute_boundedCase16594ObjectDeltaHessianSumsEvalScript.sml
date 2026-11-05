(*****************************************************************************
 * Exact evaluator semantics for the recursive compact delta row sums.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaHessianSumsEval
Ancestors
  compute_boundedCase16594ObjectDeltaHessianPrimitiveEval
Libs
  bossLib preamble intLib

val inherited_object_q_cv_list_def =
  DB.fetch "compute_boundedPackedObjectEntryContract"
    "bounded_object_q_cv_list_def";
val inherited_interval_sums_cv_def =
  DB.fetch "compute_boundedAnalyticObjectDeltaLinearRefinement"
    "bounded_object_q_interval_sums_cv_def";
val inherited_literal_app1 =
  DB.fetch "compute_boundedCase16594ObjectStateControlEval"
    "bounded_case16594_object_compute_eval_literal_app1";
val inherited_pair_from_raw_results =
  DB.fetch "compute_boundedCase16594ObjectPolyStepControlEval"
    "bounded_case16594_object_compute_eval_pair_from_raw_results";
val inherited_if_ispair_pair_components =
  DB.fetch "compute_boundedCase16594ObjectGradientCompleteEval"
    "bounded_case16594_object_compute_eval_if_ispair_pair_components";
val inherited_pair_fst_components =
  DB.fetch "compute_boundedCase16594ObjectGradientCompleteEval"
    "bounded_case16594_object_compute_eval_pair_fst_components";
val inherited_pair_snd_components =
  DB.fetch "compute_boundedCase16594ObjectGradientCompleteEval"
    "bounded_case16594_object_compute_eval_pair_snd_components";
val inherited_compute_eval_num =
  DB.fetch "compute_boundedCase16594ObjectPolyStepControlEval"
    "bounded_case16594_object_compute_eval_num";

Definition bounded_case16594_object_delta_sums_body_def:
  bounded_case16594_object_delta_sums_body =
    If (Uop Ispair (Var «row_lists»))
      (Pair
        (App «candle_cv_q_packed_delta_sum»
          [Uop Fst (Var «row_lists»)])
        (App «candle_cv_q_packed_delta_sums»
          [Uop Snd (Var «row_lists»)]))
      (Num 0)
End

Theorem bounded_case16594_object_compute_eval_app1_argument_result:
  0 < clock /\
  compute_eval clock ceqs expression (refs:hol_refs) =
      (M_success (from_cv result),refs) ==>
  compute_eval clock ceqs (App function_name [expression]) refs =
    compute_eval clock ceqs (App function_name [from_cv result]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 1`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_delta_sums_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_sums» =
    SOME ([«row_lists»],bounded_case16594_object_delta_sums_body)
Proof
  rw [bounded_case16594_object_delta_sums_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_sums_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sums» [from_cv row_lists])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«row_lists»,from_cv row_lists)]
        bounded_case16594_object_delta_sums_body) refs
Proof
  strip_tac
  >> irule inherited_literal_app1
  >> simp [bounded_case16594_object_delta_sums_lookup]
QED

Theorem bounded_case16594_object_delta_sums_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sums» [from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_cv_list [])),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_delta_sums_unfold]
  >> simp
       [bounded_case16594_object_delta_sums_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
        compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_if_ispair_num,
        inherited_object_q_cv_list_def,
        compute_execProofTheory.compute_eval_from_cv]
  >> irule inherited_compute_eval_num
QED

Theorem bounded_case16594_object_delta_sums_cons_eval:
  EVERY bounded_packed_q_interval_encoded row /\
  10 * (LENGTH row + 1) + 2 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sums»
        [from_cv
          (bounded_object_q_cv_list
            (MAP bounded_object_q_cv_list rest))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (MAP bounded_object_q_interval_sum_cv rest))),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sums»
        [from_cv
          (bounded_object_q_cv_list
            (bounded_object_q_cv_list row::
             MAP bounded_object_q_cv_list rest))]) refs =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_interval_sum_cv row::
           MAP bounded_object_q_interval_sum_cv rest))),refs)
Proof
  strip_tac
  >> rw
       [bounded_case16594_object_delta_sums_unfold,
        inherited_object_q_cv_list_def]
  >> simp
       [bounded_case16594_object_delta_sums_body_def,
        compute_evalTheory.subst_def,
        inherited_if_ispair_pair_components]
  >> irule inherited_pair_from_raw_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_delta_sum»
                [from_cv (bounded_object_q_cv_list row)]) refs`
      >> conj_tac
      >- (irule bounded_case16594_object_compute_eval_app1_argument_result
          >> simp [inherited_pair_fst_components]
          >> intLib.ARITH_TAC)
      >> irule
           compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_sums»
            [from_cv (bounded_object_q_cv_list
              (MAP bounded_object_q_cv_list rest))]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app1_argument_result
      >> simp [inherited_pair_snd_components]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_delta_sums_eval:
  !row_lists clock refs.
    EVERY (EVERY bounded_packed_q_interval_encoded) row_lists /\
    20 * (SUM (MAP LENGTH row_lists) + LENGTH row_lists + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sums»
        [from_cv
          (bounded_object_q_cv_list
            (MAP bounded_object_q_cv_list row_lists))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_interval_sums_cv row_lists))),refs)
Proof
  Induct_on `row_lists`
  >- (rpt strip_tac
      >> PURE_REWRITE_TAC
           [inherited_interval_sums_cv_def,MAP,
            inherited_object_q_cv_list_def]
      >> irule
           (REWRITE_RULE [inherited_object_q_cv_list_def]
             bounded_case16594_object_delta_sums_nil_eval)
      >> intLib.ARITH_TAC)
  >> rpt strip_tac
  >> gvs []
  >> PURE_REWRITE_TAC [inherited_interval_sums_cv_def,MAP]
  >> irule bounded_case16594_object_delta_sums_cons_eval
  >> simp []
  >> simp [inherited_interval_sums_cv_def]
QED

val _ = export_theory ();
