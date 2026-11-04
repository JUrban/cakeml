(*****************************************************************************
 * Exact evaluator semantics for the compact delta source primitives.
 *
 * These constructors and the three-factor product are shared by the generic
 * delta value, gradient, and Hessian evaluators.  The theorems preserve the
 * production representation and multiplication order exactly.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaPrimitiveEval
Ancestors
  compute_boundedCase16594ObjectDeltaProductSourceItemEval
  compute_boundedCase16594ObjectDeltaProductSemanticBridge
Libs
  bossLib preamble intLib

val inherited_object_q_cv_list_def =
  DB.fetch "compute_boundedPackedObjectEntryContract"
    "bounded_object_q_cv_list_def";

Theorem bounded_case16594_object_compute_eval_literal_app11:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME
      ([name0;name1;name2;name3;name4;name5;name6;name7;name8;name9;
        name10],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv argument0;from_cv argument1;from_cv argument2;
         from_cv argument3;from_cv argument4;from_cv argument5;
         from_cv argument6;from_cv argument7;from_cv argument8;
         from_cv argument9;from_cv argument10]) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name0,from_cv argument0);(name1,from_cv argument1);
         (name2,from_cv argument2);(name3,from_cv argument3);
         (name4,from_cv argument4);(name5,from_cv argument5);
         (name6,from_cv argument6);(name7,from_cv argument7);
         (name8,from_cv argument8);(name9,from_cv argument9);
         (name10,from_cv argument10)] body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Definition bounded_case16594_object_delta_six_body_def:
  bounded_case16594_object_delta_six_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d»)
            (Pair (Var «e»)
              (Pair (Var «f») (Num 0))))))
End

Theorem bounded_case16594_object_delta_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_six» =
    SOME
      ([«a»;«b»;«c»;«d»;«e»;«f»],
       bounded_case16594_object_delta_six_body)
Proof
  rw [bounded_case16594_object_delta_six_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_six_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_six»
        [from_cv a;from_cv b;from_cv c;from_cv d;from_cv e;from_cv f])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_cv_list [a;b;c;d;e;f])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«a»,from_cv a);(«b»,from_cv b);(«c»,from_cv c);
             («d»,from_cv d);(«e»,from_cv e);(«f»,from_cv f)]
            bounded_case16594_object_delta_six_body) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
      >> simp []
      >> ACCEPT_TAC bounded_case16594_object_delta_six_lookup)
  >> simp
       [bounded_case16594_object_delta_six_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (from_cv (bounded_object_q_cv_list [a;b;c;d;e;f])) refs`
  >> conj_tac
  >- simp
       [inherited_object_q_cv_list_def,compute_execTheory.from_cv_def]
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Definition bounded_case16594_object_delta_seven_body_def:
  bounded_case16594_object_delta_seven_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d»)
            (Pair (Var «e»)
              (Pair (Var «f»)
                (Pair (Var «g») (Num 0)))))))
End

Theorem bounded_case16594_object_delta_seven_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_seven» =
    SOME
      ([«a»;«b»;«c»;«d»;«e»;«f»;«g»],
       bounded_case16594_object_delta_seven_body)
Proof
  rw [bounded_case16594_object_delta_seven_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_seven_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_seven»
        [from_cv a;from_cv b;from_cv c;from_cv d;from_cv e;from_cv f;
         from_cv g]) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_cv_list [a;b;c;d;e;f;g])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«a»,from_cv a);(«b»,from_cv b);(«c»,from_cv c);
             («d»,from_cv d);(«e»,from_cv e);(«f»,from_cv f);
             («g»,from_cv g)]
            bounded_case16594_object_delta_seven_body) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_literal_app7
      >> simp []
      >> ACCEPT_TAC bounded_case16594_object_delta_seven_lookup)
  >> simp
       [bounded_case16594_object_delta_seven_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (from_cv (bounded_object_q_cv_list [a;b;c;d;e;f;g])) refs`
  >> conj_tac
  >- simp
       [inherited_object_q_cv_list_def,compute_execTheory.from_cv_def]
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Definition bounded_case16594_object_delta_eleven_body_def:
  bounded_case16594_object_delta_eleven_body =
    Pair (Var «a0»)
      (Pair (Var «a1»)
        (Pair (Var «a2»)
          (Pair (Var «a3»)
            (Pair (Var «a4»)
              (Pair (Var «a5»)
                (Pair (Var «a6»)
                  (Pair (Var «a7»)
                    (Pair (Var «a8»)
                      (Pair (Var «a9»)
                        (Pair (Var «a10») (Num 0)))))))))))
End

Theorem bounded_case16594_object_delta_eleven_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_eleven» =
    SOME
      ([«a0»;«a1»;«a2»;«a3»;«a4»;«a5»;«a6»;«a7»;«a8»;«a9»;
        «a10»],bounded_case16594_object_delta_eleven_body)
Proof
  rw [bounded_case16594_object_delta_eleven_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_eleven_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_eleven»
        [from_cv a0;from_cv a1;from_cv a2;from_cv a3;from_cv a4;
         from_cv a5;from_cv a6;from_cv a7;from_cv a8;from_cv a9;
         from_cv a10]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«a0»,from_cv a0);(«a1»,from_cv a1);(«a2»,from_cv a2);
             («a3»,from_cv a3);(«a4»,from_cv a4);(«a5»,from_cv a5);
             («a6»,from_cv a6);(«a7»,from_cv a7);(«a8»,from_cv a8);
             («a9»,from_cv a9);(«a10»,from_cv a10)]
            bounded_case16594_object_delta_eleven_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_literal_app11
      >> simp []
      >> ACCEPT_TAC bounded_case16594_object_delta_eleven_lookup)
  >> simp
       [bounded_case16594_object_delta_eleven_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (from_cv
            (bounded_object_q_cv_list
              [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10])) refs`
  >> conj_tac
  >- simp
       [inherited_object_q_cv_list_def,compute_execTheory.from_cv_def]
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Definition bounded_case16594_object_delta_mul3_body_def:
  bounded_case16594_object_delta_mul3_body =
    App «candle_cv_q_interval_mul»
      [App «candle_cv_q_interval_mul»
        [Var «first»;Var «second»];
       Var «third»]
End

Theorem bounded_case16594_object_delta_mul3_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_mul3» =
    SOME
      ([«first»;«second»;«third»],
       bounded_case16594_object_delta_mul3_body)
Proof
  rw [bounded_case16594_object_delta_mul3_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_mul3_eval:
  bounded_packed_q_interval_encoded first_value /\
  bounded_packed_q_interval_encoded second_value /\
  bounded_packed_q_interval_encoded third_value /\
  18 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_mul3»
        [from_cv first_value;from_cv second_value;from_cv third_value])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_interval_mul3_cv
          first_value second_value third_value)),refs)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded
        (bounded_object_q_interval_mul_cv first_value second_value)` by
       (irule
          compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
        >> irule
             compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded
        >> simp
             [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«first»,from_cv first_value);(«second»,from_cv second_value);
             («third»,from_cv third_value)]
            bounded_case16594_object_delta_mul3_body) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
      >> simp []
      >> ACCEPT_TAC bounded_case16594_object_delta_mul3_lookup)
  >> simp
       [bounded_case16594_object_delta_mul3_body_def,
        compute_evalTheory.subst_def]
  >> rw
       [compute_boundedAnalyticObjectDeltaProductRefinementTheory.bounded_object_q_interval_mul3_cv_def]
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_mul_argument_results
  >> simp [compute_execProofTheory.compute_eval_from_cv]
  >> irule
       compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_q_interval_mul_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
