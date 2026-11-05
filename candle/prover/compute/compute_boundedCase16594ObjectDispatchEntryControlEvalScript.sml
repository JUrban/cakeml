(*****************************************************************************
 * Structural evaluator semantics for the packed-object dispatcher entry.
 *
 * The expensive 167-action numerical program is an explicit premise here.
 * This theory proves only the entry wrapper: singleton-stack and exhausted-
 * certificate guards, state projections, and the already-proved accept6
 * suffix.  It can therefore be reused for every authenticated cell result.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchEntryControlEval
Ancestors
  compute_boundedCase16594Cell0AuthenticatedObjectAcceptance
  compute_boundedCase16594ObjectDispatchCell0Shape
  compute_boundedCase16594ObjectStateControlEval
  compute_boundedCase16594ObjectPolyTraceEval
  compute_boundedPackedObjectEntryRefinement
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_accept6_eval_clock:
  bounded_packed_object_source_accept6 radii center_value center_gradient
      packed_hessian /\
  205 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_accept6»
      [from_cv (Num 1);from_cv (bounded_object_q_cv_list radii);
       from_cv center_value;
       from_cv (bounded_object_q_cv_list center_gradient);
       from_cv (bounded_object_q_cv_list packed_hessian)])
    (refs:hol_refs) =
      (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App «candle_cv_q_packed_object_accept6»
          [from_cv (Num 1);from_cv (bounded_object_q_cv_list radii);
           from_cv center_value;
           from_cv (bounded_object_q_cv_list center_gradient);
           from_cv (bounded_object_q_cv_list packed_hessian)]) refs =
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_accept6»
          [from_cv (Num 1);from_cv (bounded_object_q_cv_list radii);
           from_cv center_value;
           from_cv (bounded_object_q_cv_list center_gradient);
           from_cv (bounded_object_q_cv_list packed_hessian)]) refs` by
       (irule
          compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_eval_cong
        >> simp
             [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
              compute_boundedCase16594ObjectCoreCongruenceTheory.bounded_case16594_object_core_def,
              compute_boundedPackedObjectEntryDataTheory.bounded_packed_object_entry_ceqs_def,
              compute_evalRestrictedCongruenceTheory.cexp_value_compute_exp_uses_only,
              compute_execProofTheory.cexp_value_from_cv])
  >> qpat_x_assum
       `compute_eval clock bounded_packed_object_entry_ceqs _ _ = _`
       (fn th => REWRITE_TAC [GSYM th])
  >> fs
       [compute_boundedPackedObjectEntryRefinementTheory.bounded_packed_object_source_accept6_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_boundedPackedObjectFinishEvalTheory.bounded_packed_q_accept6_eval)
  >> simp []
QED

Theorem bounded_case16594_object_state_accept6_eval:
  bounded_packed_object_source_accept6 radii center_value center_gradient
      packed_hessian /\
  207 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_state_accept6»
      [from_cv (bounded_object_q_cv_list radii);
       from_cv
         (bounded_case16594_object_state_cv (Num 1) center_value
           (bounded_object_q_cv_list center_gradient) value_bound
           gradient_bounds (bounded_object_q_cv_list packed_hessian))])
    (refs:hol_refs) =
      (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«radii»,from_cv (bounded_object_q_cv_list radii));
             («state»,from_cv
               (bounded_case16594_object_state_cv (Num 1) center_value
                 (bounded_object_q_cv_list center_gradient) value_bound
                 gradient_bounds
                 (bounded_object_q_cv_list packed_hessian)))]
            bounded_case16594_object_state_accept6_body) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
      >> simp
           [compute_boundedCase16594ObjectDispatchCell0ShapeTheory.bounded_case16594_object_state_accept6_lookup])
  >> simp
       [compute_boundedCase16594ObjectDispatchCell0ShapeTheory.bounded_case16594_object_state_accept6_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_accept6»
            [from_cv (Num 1);
             from_cv (bounded_object_q_cv_list radii);
             from_cv center_value;
             from_cv (bounded_object_q_cv_list center_gradient);
             from_cv (bounded_object_q_cv_list packed_hessian)]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app5_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> simp
           [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_domain_eval,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_gradient_eval,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_packed_hessian_eval,
            compute_execProofTheory.compute_eval_from_cv])
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 1`]
         bounded_case16594_object_accept6_eval_clock)
  >> simp [compute_execTheory.from_cv_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_entry_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_dispatch_entry»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;from_cv codes;
       from_cv sources;from_cv certificates]) (refs:hol_refs) =
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);
       («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
       («codes»,from_cv codes);(«sources»,from_cv sources);
       («certificates»,from_cv certificates)]
      bounded_case16594_object_dispatch_entry_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> simp
       [compute_boundedCase16594ObjectDispatchCell0ShapeTheory.bounded_case16594_object_dispatch_entry_lookup]
QED

Theorem bounded_case16594_object_dispatch_entry_from_program_eval:
  bounded_packed_object_source_accept6 radii center_value center_gradient
      packed_hessian /\
  212 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_dispatch_program»
      [from_cv center_boxes;from_cv outer_boxes;
       from_cv (bounded_object_q_cv_list radii);from_cv codes;
       from_cv sources;from_cv certificates;from_cv (Num 0)])
    (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair
              (bounded_object_q_cv_list
                [bounded_case16594_object_state_cv (Num 1) center_value
                  (bounded_object_q_cv_list center_gradient) value_bound
                  gradient_bounds (bounded_object_q_cv_list packed_hessian)])
              (Num 0)))),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_dispatch_entry»
      [from_cv center_boxes;from_cv outer_boxes;
       from_cv (bounded_object_q_cv_list radii);from_cv codes;
       from_cv sources;from_cv certificates]) refs =
    (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_dispatch_entry_unfold]
  >> rw
       [compute_boundedCase16594ObjectDispatchCell0ShapeTheory.bounded_case16594_object_dispatch_entry_body_def]
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `Pair (Num 1)
          (Pair
            (bounded_object_q_cv_list
              [bounded_case16594_object_state_cv (Num 1) center_value
                (bounded_object_q_cv_list center_gradient) value_bound
                gradient_bounds (bounded_object_q_cv_list packed_hessian)])
            (Num 0))`
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_cv_list
          [bounded_case16594_object_state_cv (Num 1) center_value
            (bounded_object_q_cv_list center_gradient) value_bound
            gradient_bounds (bounded_object_q_cv_list packed_hessian)]`
  >> conj_tac
  >- simp
       [compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `Num 0`
  >> conj_tac
  >- simp
       [compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 4)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_accept6»
            [from_cv (bounded_object_q_cv_list radii);
             from_cv
               (bounded_case16594_object_state_cv (Num 1) center_value
                 (bounded_object_q_cv_list center_gradient) value_bound
                 gradient_bounds
                 (bounded_object_q_cv_list packed_hessian))]) refs`
  >> conj_tac
  >- simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 4`]
         bounded_case16594_object_state_accept6_eval)
  >> simp
       [compute_execTheory.from_cv_def]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
