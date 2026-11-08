(*****************************************************************************
 * Exact evaluator semantics for the compact delta Hessian list constructors.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaHessianPrimitiveEval
Ancestors
  compute_boundedCase16594ObjectDeltaGradientCompleteEval
Libs
  bossLib preamble intLib

val inherited_object_q_cv_list_def =
  DB.fetch "compute_boundedPackedObjectEntryContract"
    "bounded_object_q_cv_list_def";

Theorem bounded_case16594_object_delta_compute_eval_literal_app8:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME
      ([name1;name2;name3;name4;name5;name6;name7;name8],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv argument1;from_cv argument2;from_cv argument3;
         from_cv argument4;from_cv argument5;from_cv argument6;
         from_cv argument7;from_cv argument8]) (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv argument1);(name2,from_cv argument2);
         (name3,from_cv argument3);(name4,from_cv argument4);
         (name5,from_cv argument5);(name6,from_cv argument6);
         (name7,from_cv argument7);(name8,from_cv argument8)] body) refs
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

Definition bounded_case16594_object_delta_two_body_def:
  bounded_case16594_object_delta_two_body =
    Pair (Var «a») (Pair (Var «b») (Num 0))
End

Theorem bounded_case16594_object_delta_two_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_two» =
    SOME ([«a»;«b»],bounded_case16594_object_delta_two_body)
Proof
  rw [bounded_case16594_object_delta_two_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_two_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_two» [from_cv a;from_cv b])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_cv_list [a;b])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst [(«a»,from_cv a);(«b»,from_cv b)]
            bounded_case16594_object_delta_two_body) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
      >> simp []
      >> ACCEPT_TAC bounded_case16594_object_delta_two_lookup)
  >> simp
       [bounded_case16594_object_delta_two_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (from_cv (bounded_object_q_cv_list [a;b])) refs`
  >> conj_tac
  >- simp [inherited_object_q_cv_list_def,compute_execTheory.from_cv_def]
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Definition bounded_case16594_object_delta_three_body_def:
  bounded_case16594_object_delta_three_body =
    Pair (Var «a») (Pair (Var «b») (Pair (Var «c») (Num 0)))
End

Theorem bounded_case16594_object_delta_three_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_three» =
    SOME ([«a»;«b»;«c»],bounded_case16594_object_delta_three_body)
Proof
  rw [bounded_case16594_object_delta_three_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_three_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_three»
        [from_cv a;from_cv b;from_cv c]) (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_cv_list [a;b;c])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst [(«a»,from_cv a);(«b»,from_cv b);(«c»,from_cv c)]
            bounded_case16594_object_delta_three_body) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
      >> simp []
      >> ACCEPT_TAC bounded_case16594_object_delta_three_lookup)
  >> simp
       [bounded_case16594_object_delta_three_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (from_cv (bounded_object_q_cv_list [a;b;c])) refs`
  >> conj_tac
  >- simp [inherited_object_q_cv_list_def,compute_execTheory.from_cv_def]
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Definition bounded_case16594_object_delta_eight_body_def:
  bounded_case16594_object_delta_eight_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d»)
            (Pair (Var «e»)
              (Pair (Var «f»)
                (Pair (Var «g») (Pair (Var «h») (Num 0))))))))
End

Theorem bounded_case16594_object_delta_eight_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_eight» =
    SOME
      ([«a»;«b»;«c»;«d»;«e»;«f»;«g»;«h»],
       bounded_case16594_object_delta_eight_body)
Proof
  rw [bounded_case16594_object_delta_eight_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_eight_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_eight»
        [from_cv a;from_cv b;from_cv c;from_cv d;
         from_cv e;from_cv f;from_cv g;from_cv h]) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_cv_list [a;b;c;d;e;f;g;h])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«a»,from_cv a);(«b»,from_cv b);(«c»,from_cv c);
             («d»,from_cv d);(«e»,from_cv e);(«f»,from_cv f);
             («g»,from_cv g);(«h»,from_cv h)]
            bounded_case16594_object_delta_eight_body) refs`
  >> conj_tac
  >- (irule
        bounded_case16594_object_delta_compute_eval_literal_app8
      >> simp []
      >> ACCEPT_TAC bounded_case16594_object_delta_eight_lookup)
  >> simp
       [bounded_case16594_object_delta_eight_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (from_cv (bounded_object_q_cv_list [a;b;c;d;e;f;g;h])) refs`
  >> conj_tac
  >- simp [inherited_object_q_cv_list_def,compute_execTheory.from_cv_def]
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

val _ = export_theory ();
