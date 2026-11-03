(*****************************************************************************
 * Structural evaluator semantics for the explicit-radius object dispatcher.
 *
 * One exact evaluator premise is required per successful instruction, but the
 * list traversal, state threading, success guards, and terminal shape are
 * proved once here.  A later closed theorem supplies those premises from the
 * already-proved instruction semantics for the genuine 167-entry program.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchProgramTraceEval
Ancestors
  compute_boundedCase16594ObjectDispatchCell0Shape
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_compute_eval_literal_app7:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME ([name1;name2;name3;name4;name5;name6;name7],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv argument1;from_cv argument2;from_cv argument3;
         from_cv argument4;from_cv argument5;from_cv argument6;
         from_cv argument7])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv argument1);(name2,from_cv argument2);
         (name3,from_cv argument3);(name4,from_cv argument4);
         (name5,from_cv argument5);(name6,from_cv argument6);
         (name7,from_cv argument7)] body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_compute_eval_let_result:
  0 < clock /\
  compute_eval clock ceqs bound (refs:hol_refs) =
      (M_success (from_cv value),refs) /\
  compute_eval (clock - 1) ceqs
      (subst [(name,from_cv value)] body) refs = result ==>
  compute_eval clock ceqs (Let name bound body) refs = result
Proof
  Cases_on `clock`
  >> simp
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_app7_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) /\
  compute_eval clock ceqs argument4 refs =
      (M_success (from_cv result4),refs) /\
  compute_eval clock ceqs argument5 refs =
      (M_success (from_cv result5),refs) /\
  compute_eval clock ceqs argument6 refs =
      (M_success (from_cv result6),refs) /\
  compute_eval clock ceqs argument7 refs =
      (M_success (from_cv result7),refs) ==>
  compute_eval clock ceqs
      (App function_name
        [argument1;argument2;argument3;argument4;argument5;argument6;
         argument7]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3;from_cv result4;
         from_cv result5;from_cv result6;from_cv result7]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 7`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_dispatch_program_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_program»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv codes;from_cv sources;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («codes»,from_cv codes);(«sources»,from_cv sources);
         («certificates»,from_cv certificates);(«stack»,from_cv stack)]
        bounded_case16594_object_dispatch_program_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_object_compute_eval_literal_app7
  >> simp [bounded_case16594_object_dispatch_program_lookup]
QED

Theorem bounded_case16594_object_dispatch_program_empty_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_program»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num codes_nil);from_cv (Num sources_nil);
         from_cv certificates;from_cv stack]) (refs:hol_refs) =
    (M_success
      (from_cv (Pair (Num 1) (Pair stack certificates))),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_dispatch_program_unfold]
  >> simp
       [bounded_case16594_object_dispatch_program_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_dispatch_program_cons_eval:
  2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv code;from_cv source;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1) (Pair next_stack next_certificates))),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_program»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv codes;from_cv sources;from_cv next_certificates;
         from_cv next_stack]) refs =
    (M_success (from_cv final_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_program»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Pair code codes);from_cv (Pair source sources);
         from_cv certificates;from_cv stack]) refs =
    (M_success (from_cv final_state),refs)
Proof
  strip_tac
  >> simp [bounded_case16594_object_dispatch_program_unfold]
  >> simp
       [bounded_case16594_object_dispatch_program_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (Uop Ispair (Pair (from_cv code) (from_cv codes))) refs =
      (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_ispair_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (Uop Ispair (Pair (from_cv source) (from_cv sources))) refs =
      (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_ispair_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `Pair (Num 1) (Pair next_stack next_certificates)`
  >> conj_tac
  >- (`compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_dispatch_step»
            [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
             Uop Fst (Pair (from_cv code) (from_cv codes));
             Uop Fst (Pair (from_cv source) (from_cv sources));
             from_cv certificates;from_cv stack]) refs =
        compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_dispatch_step»
            [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
             from_cv code;from_cv source;from_cv certificates;from_cv stack])
          refs` by
        (irule bounded_case16594_object_compute_eval_app7_argument_results
         >> fs
              [compute_evalTheory.compute_eval_def,
               compute_execProofTheory.compute_eval_from_cv,
               compute_evalTheory.do_uop_def,
               compute_evalTheory.do_fst_def,
               ml_monadBaseTheory.st_ex_bind_def,
               ml_monadBaseTheory.st_ex_return_def])
      >> fs [])
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> `compute_eval (clock - 2)
        bounded_case16594_object_dispatch_cell0_ceqs
        (Binop Eq
          (Uop Fst
            (from_cv
              (Pair (Num 1) (Pair next_stack next_certificates))))
          (Num 1)) refs =
      (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_execProofTheory.compute_eval_from_cv,
          compute_evalTheory.do_uop_def,
          compute_evalTheory.do_fst_def,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_eq_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> `compute_eval (clock - 2)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_dispatch_program»
          [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
           Uop Snd (Pair (from_cv code) (from_cv codes));
           Uop Snd (Pair (from_cv source) (from_cv sources));
           Uop Snd
             (Uop Snd
               (from_cv
                 (Pair (Num 1) (Pair next_stack next_certificates))));
           Uop Fst
             (Uop Snd
               (from_cv
                 (Pair (Num 1) (Pair next_stack next_certificates))))]) refs =
      compute_eval (clock - 2)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_dispatch_program»
          [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
           from_cv codes;from_cv sources;from_cv next_certificates;
           from_cv next_stack]) refs` by
       (irule bounded_case16594_object_compute_eval_app7_argument_results
        >> fs
             [compute_evalTheory.compute_eval_def,
              compute_execProofTheory.compute_eval_from_cv,
              compute_evalTheory.do_uop_def,
              compute_evalTheory.do_fst_def,
              compute_evalTheory.do_snd_def,
              ml_monadBaseTheory.st_ex_bind_def,
              ml_monadBaseTheory.st_ex_return_def])
  >> fs []
QED

Definition bounded_case16594_object_dispatch_step_eval_above_def:
  bounded_case16594_object_dispatch_step_eval_above step_floor
      center_boxes outer_boxes radii code source certificates stack
      next_stack next_certificates <=>
    !clock refs.
      step_floor < clock ==>
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_dispatch_step»
          [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
           from_cv code;from_cv source;from_cv certificates;from_cv stack])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1) (Pair next_stack next_certificates))),refs)
End

Definition bounded_case16594_object_dispatch_program_trace_def:
  (bounded_case16594_object_dispatch_program_trace step_floor
      center_boxes outer_boxes radii
      (Num codes_nil) (Num sources_nil) certificates stack final_state <=>
        final_state = Pair (Num 1) (Pair stack certificates)) /\
  (bounded_case16594_object_dispatch_program_trace step_floor
      center_boxes outer_boxes radii
      (Num codes_nil) (Pair source sources) certificates stack final_state <=>
        F) /\
  (bounded_case16594_object_dispatch_program_trace step_floor
      center_boxes outer_boxes radii
      (Pair code codes) (Num sources_nil) certificates stack final_state <=>
        F) /\
  (bounded_case16594_object_dispatch_program_trace step_floor
      center_boxes outer_boxes radii
      (Pair code codes) (Pair source sources) certificates stack final_state <=>
        ?next_stack next_certificates.
          bounded_case16594_object_dispatch_step_eval_above step_floor
            center_boxes outer_boxes radii code source certificates stack
            next_stack next_certificates /\
          bounded_case16594_object_dispatch_program_trace step_floor
            center_boxes outer_boxes radii codes sources next_certificates
            next_stack final_state)
End

Definition bounded_case16594_object_cv_list_length_def:
  bounded_case16594_object_cv_list_length (Num nil) = 0 /\
  bounded_case16594_object_cv_list_length (Pair item items) =
    SUC (bounded_case16594_object_cv_list_length items)
End

Theorem bounded_case16594_object_dispatch_program_trace_sound:
  !codes sources certificates stack final_state clock refs.
    bounded_case16594_object_dispatch_program_trace step_floor
      center_boxes outer_boxes radii codes sources certificates stack
      final_state /\
    step_floor + 2 * bounded_case16594_object_cv_list_length codes + 2 <
      clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_program»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv codes;from_cv sources;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    (M_success (from_cv final_state),refs)
Proof
  Induct_on `codes`
  >- (rpt gen_tac
      >> Cases_on `sources`
      >> simp
           [bounded_case16594_object_dispatch_program_trace_def,
            bounded_case16594_object_cv_list_length_def]
      >> strip_tac
      >> qpat_x_assum `final_state = Pair _ _` kall_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_case16594_object_dispatch_program_empty_eval)
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> Cases_on `sources`
  >- simp [bounded_case16594_object_dispatch_program_trace_def]
  >> simp
       [bounded_case16594_object_dispatch_program_trace_def,
        bounded_case16594_object_cv_list_length_def]
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_dispatch_program_cons_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_certificates`
  >> qexists_tac `next_stack`
  >> conj_tac
  >- (qpat_x_assum
        `bounded_case16594_object_dispatch_step_eval_above step_floor
           center_boxes outer_boxes radii codes sources certificates stack
           next_stack next_certificates`
        mp_tac
      >> rw [bounded_case16594_object_dispatch_step_eval_above_def]
      >> first_x_assum match_mp_tac
      >> intLib.ARITH_TAC)
  >> first_x_assum match_mp_tac
  >> conj_tac >- asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
