(*****************************************************************************
 * Exact evaluator semantics for the compact delta interval-sum helper.
 *
 * This is the first arbitrary-input component needed by both the product
 * center jet and the packed outer Hessian.  It follows the production
 * left-fold order exactly; no rational normalization or reassociation is
 * introduced by the proof.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaSumEval
Ancestors
  compute_boundedCase16594ObjectDeltaProductSourceItemEval
  compute_boundedCase16594ObjectDeltaProductSemanticBridge
Libs
  bossLib preamble intLib

val inherited_literal_app2 =
  DB.fetch "compute_boundedCase16594ObjectPolyStepControlEval"
    "bounded_case16594_object_compute_eval_literal_app2";
val inherited_if_ispair_pair_components =
  DB.fetch "compute_boundedCase16594ObjectGradientCompleteEval"
    "bounded_case16594_object_compute_eval_if_ispair_pair_components";
val inherited_pair_fst_components =
  DB.fetch "compute_boundedCase16594ObjectGradientCompleteEval"
    "bounded_case16594_object_compute_eval_pair_fst_components";
val inherited_pair_snd_components =
  DB.fetch "compute_boundedCase16594ObjectGradientCompleteEval"
    "bounded_case16594_object_compute_eval_pair_snd_components";
val inherited_app2_argument_results =
  DB.fetch "compute_boundedPackedObjectPrimitiveAbsEval"
    "bounded_packed_compute_eval_app2_argument_results";
val inherited_interval_add_eval =
  DB.fetch "compute_boundedCase16594ObjectMulEval"
    "bounded_case16594_object_interval_add_eval";
val inherited_interval_packed_encoded =
  DB.fetch "compute_boundedCase16594ObjectMulEval"
    "bounded_case16594_object_interval_packed_encoded";
val inherited_interval_add_cv_encoded =
  DB.fetch "compute_boundedObjectTaylorZeroAlgebra"
    "bounded_object_q_interval_add_cv_encoded";
val inherited_source_interval_encoded =
  DB.fetch "compute_boundedObjectTaylorZeroAlgebra"
    "bounded_analytic_source_q_interval_cv_encoded";
val inherited_packed_interval_object_encoded =
  DB.fetch "compute_boundedCase16594ObjectMulEval"
    "bounded_case16594_packed_interval_object_encoded";
val inherited_object_q_cv_list_def =
  DB.fetch "compute_boundedPackedObjectEntryContract"
    "bounded_object_q_cv_list_def";
val inherited_literal_app1 =
  DB.fetch "compute_boundedCase16594ObjectStateControlEval"
    "bounded_case16594_object_compute_eval_literal_app1";
val inherited_interval_sum_aux_cv_def =
  DB.fetch "compute_boundedAnalyticObjectDeltaLinearRefinement"
    "bounded_object_q_interval_sum_aux_cv_def";
val inherited_interval_sum_cv_def =
  DB.fetch "compute_boundedAnalyticObjectDeltaLinearRefinement"
    "bounded_object_q_interval_sum_cv_def";

Definition bounded_case16594_object_delta_sum_aux_body_def:
  bounded_case16594_object_delta_sum_aux_body =
    If (Uop Ispair (Var «values»))
      (App «candle_cv_q_packed_delta_sum_aux»
        [Uop Snd (Var «values»);
         App «candle_cv_q_interval_add»
           [Var «accumulator»;Uop Fst (Var «values»)]])
      (Var «accumulator»)
End

Definition bounded_case16594_object_delta_sum_body_def:
  bounded_case16594_object_delta_sum_body =
    App «candle_cv_q_packed_delta_sum_aux»
      [Var «values»;
       Pair
         (Pair (Pair (Num 0) (Num 0)) (Num 0))
         (Pair (Pair (Num 0) (Num 0)) (Num 0))]
End

Theorem bounded_case16594_object_delta_sum_if_ispair_num:
  compute_eval clock ceqs
      (If (Uop Ispair (Num number)) yes_branch no_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs no_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_delta_sum_zero_interval:
  bounded_analytic_source_q_interval_cv 0 0 0 =
    Pair
      (Pair (Pair (Num 0) (Num 0)) (Num 0))
      (Pair (Pair (Num 0) (Num 0)) (Num 0))
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_delta_sum_aux_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_sum_aux» =
    SOME
      ([«values»;«accumulator»],
       bounded_case16594_object_delta_sum_aux_body)
Proof
  rw [bounded_case16594_object_delta_sum_aux_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_sum_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_sum» =
    SOME ([«values»],bounded_case16594_object_delta_sum_body)
Proof
  rw [bounded_case16594_object_delta_sum_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_sum_aux_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sum_aux»
        [from_cv values;from_cv accumulator]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«values»,from_cv values);(«accumulator»,from_cv accumulator)]
        bounded_case16594_object_delta_sum_aux_body) refs
Proof
  strip_tac
  >> irule
       inherited_literal_app2
  >> simp [bounded_case16594_object_delta_sum_aux_lookup]
QED

Theorem bounded_case16594_object_delta_sum_aux_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sum_aux»
        [from_cv (Num 0);from_cv accumulator]) (refs:hol_refs) =
    (M_success (from_cv accumulator),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_delta_sum_aux_unfold]
  >> simp
       [bounded_case16594_object_delta_sum_aux_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
        bounded_case16594_object_delta_sum_if_ispair_num,
        compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_case16594_object_delta_sum_aux_cons_eval:
  bounded_packed_q_interval_encoded accumulator /\
  bounded_packed_q_interval_encoded value /\
  7 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sum_aux»
        [from_cv rest;
         from_cv (bounded_object_q_interval_add_cv accumulator value)])
      (refs:hol_refs) = (M_success (from_cv result),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sum_aux»
        [from_cv (Pair value rest);from_cv accumulator]) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_delta_sum_aux_unfold]
  >> simp
       [bounded_case16594_object_delta_sum_aux_body_def,
        compute_evalTheory.subst_def,
        inherited_if_ispair_pair_components]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_sum_aux»
            [from_cv rest;
             from_cv
               (bounded_object_q_interval_add_cv accumulator value)]) refs`
  >> conj_tac
  >- (irule
        inherited_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp [inherited_pair_snd_components]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_interval_add»
                [from_cv accumulator;from_cv value]) refs`
      >> conj_tac
      >- (irule inherited_app2_argument_results
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                inherited_pair_fst_components]
          >> intLib.ARITH_TAC)
      >> irule inherited_interval_add_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_delta_sum_aux_eval:
  !values accumulator clock refs.
    EVERY bounded_packed_q_interval_encoded values /\
    bounded_packed_q_interval_encoded accumulator /\
    10 * (LENGTH values + 1) < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sum_aux»
        [from_cv (bounded_object_q_cv_list values);from_cv accumulator])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_interval_sum_aux_cv values accumulator)),refs)
Proof
  Induct_on `values`
  >- (rpt strip_tac
      >> PURE_REWRITE_TAC
           [inherited_interval_sum_aux_cv_def,
            inherited_object_q_cv_list_def]
      >> irule bounded_case16594_object_delta_sum_aux_nil_eval
      >> intLib.ARITH_TAC)
  >> rpt strip_tac
  >> gvs []
  >> PURE_REWRITE_TAC
       [inherited_interval_sum_aux_cv_def,
        inherited_object_q_cv_list_def]
  >> irule bounded_case16594_object_delta_sum_aux_cons_eval
  >> simp []
  >> first_x_assum irule
  >> simp []
  >> irule inherited_interval_packed_encoded
  >> irule inherited_interval_add_cv_encoded
  >> simp [inherited_packed_interval_object_encoded]
QED

Theorem bounded_case16594_object_delta_sum_aux_packed_encoded:
  !values accumulator.
    EVERY bounded_packed_q_interval_encoded values /\
    bounded_packed_q_interval_encoded accumulator ==>
    bounded_packed_q_interval_encoded
      (bounded_object_q_interval_sum_aux_cv values accumulator)
Proof
  Induct_on `values`
  >- simp [inherited_interval_sum_aux_cv_def]
  >> rpt strip_tac
  >> gvs []
  >> PURE_REWRITE_TAC [inherited_interval_sum_aux_cv_def]
  >> first_x_assum irule
  >> simp []
  >> irule inherited_interval_packed_encoded
  >> irule inherited_interval_add_cv_encoded
  >> simp [inherited_packed_interval_object_encoded]
QED

Theorem bounded_case16594_object_delta_sum_packed_encoded:
  EVERY bounded_packed_q_interval_encoded values ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_sum_cv values)
Proof
  strip_tac
  >> rw [inherited_interval_sum_cv_def]
  >> irule bounded_case16594_object_delta_sum_aux_packed_encoded
  >> simp []
  >> irule inherited_interval_packed_encoded
  >> simp [inherited_source_interval_encoded]
QED

Theorem bounded_case16594_object_delta_sum_eval:
  EVERY bounded_packed_q_interval_encoded values /\
  10 * (LENGTH values + 1) + 1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sum»
        [from_cv (bounded_object_q_cv_list values)]) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_sum_cv values)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«values»,from_cv (bounded_object_q_cv_list values))]
            bounded_case16594_object_delta_sum_body) refs`
  >> conj_tac
  >- (irule
        inherited_literal_app1
      >> simp []
      >> ACCEPT_TAC bounded_case16594_object_delta_sum_lookup)
  >> simp
       [bounded_case16594_object_delta_sum_body_def,
        compute_evalTheory.subst_def,
        inherited_interval_sum_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_sum_aux»
            [from_cv (bounded_object_q_cv_list values);
             from_cv (bounded_analytic_source_q_interval_cv 0 0 0)]) refs`
  >> conj_tac
  >- simp
       [bounded_case16594_object_delta_sum_zero_interval,
        compute_execTheory.from_cv_def]
  >> irule bounded_case16594_object_delta_sum_aux_eval
  >> simp []
  >> irule inherited_interval_packed_encoded
  >> simp [inherited_source_interval_encoded]
QED

val _ = export_theory ();
