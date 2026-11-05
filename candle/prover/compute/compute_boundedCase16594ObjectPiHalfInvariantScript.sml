(*****************************************************************************
 * Production evaluator and semantic invariant for the ordinary pi/2 source.
 *
 * The generated constant is authenticated against the exact case-16594
 * equation environment.  Its runtime state is the canonical object-q
 * encoding of the shared semantic pi/2 Taylor constant, so this instruction
 * preserves the full outer-stack refinement invariant without arithmetic.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPiHalfInvariant
Ancestors
  compute_boundedCase16594ObjectOrdinaryPolyInvariant
  compute_boundedCase16594ObjectStateControlEval
  compute_boundedCase16594ObjectSpecializedStepControlEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_pi_half_semantic_def:
  bounded_case16594_object_pi_half_semantic =
    bounded_object_q_taylor_interval_constant bounded_atan_pi_half
End

Definition bounded_case16594_object_pi_half_runtime_cv_def:
  bounded_case16594_object_pi_half_runtime_cv =
    bounded_object_q_taylor_state_encoded_cv
      bounded_case16594_object_pi_half_semantic
End

Definition bounded_case16594_object_pi_half_state_body_def:
  bounded_case16594_object_pi_half_state_body =
    App «candle_cv_q_packed_object_state_make»
      [from_cv (Num 1);
       from_cv (bounded_interval64_object_q_cv bounded_atan_pi_half);
       from_cv
         (bounded_object_q_cv_list
           (REPLICATE 6 (bounded_analytic_source_q_interval_cv 0 0 0)));
       from_cv (bounded_interval64_object_q_cv bounded_atan_pi_half);
       from_cv
         (bounded_object_q_cv_list
           (REPLICATE 6 (bounded_analytic_source_q_interval_cv 0 0 0)));
       from_cv
         (bounded_object_q_cv_list
           (REPLICATE 21 (bounded_analytic_source_q_interval_cv 0 0 0)))]
End

Theorem bounded_case16594_object_pi_half_state_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_pi_half_state» =
    SOME ([],bounded_case16594_object_pi_half_state_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_pi_half_state_eval:
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_pi_half_state» [])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_pi_half_runtime_cv),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          bounded_case16594_object_pi_half_state_body refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_app0_unfold
      >> simp [bounded_case16594_object_pi_half_state_lookup]
      >> intLib.ARITH_TAC)
  >> rewrite_tac
       [bounded_case16594_object_pi_half_state_body_def,
        bounded_case16594_object_pi_half_runtime_cv_def,
        bounded_case16594_object_pi_half_semantic_def,
        compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_interval_constant_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_encoded_cv_def,
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def]
  >> simp
       [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_make_eval,
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_pi_half_semantic_valid:
  bounded_object_q_taylor_semantic_valid
    bounded_case16594_object_pi_half_semantic
Proof
  rewrite_tac
    [bounded_case16594_object_pi_half_semantic_def,
     compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_interval_constant_def,
     compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def]
  >> simp
       [compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_zero]
  >> irule
       compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_covers_packed_q_interval_valid_cv
  >> qexists_tac `bounded_atan_pi_half`
  >> irule
       compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q
  >> ACCEPT_TAC
       compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_atan_pi_half_valid
QED

Theorem bounded_case16594_object_pi_half_runtime_refines:
  bounded_object_q_taylor_runtime_refines
    bounded_case16594_object_pi_half_runtime_cv
    bounded_case16594_object_pi_half_semantic
Proof
  rewrite_tac
    [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def,
     bounded_case16594_object_pi_half_runtime_cv_def]
  >> conj_tac
  >- (rewrite_tac
        [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_def,
         bounded_case16594_object_pi_half_semantic_def,
         compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_interval_constant_def,
         compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_encoded_cv_def,
            compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_cv_equiv_def,
            compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_cv_equiv_encoded]
      >> mp_tac bounded_case16594_object_pi_half_semantic_valid
      >> simp
           [bounded_case16594_object_pi_half_semantic_def,
            compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_interval_constant_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def]
      >> strip_tac
      >> `bounded_object_q_interval_encoded
            (bounded_interval64_object_q_cv bounded_atan_pi_half)` by
           fs
             [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
              compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
      >> `bounded_object_q_interval_encoded
            (bounded_analytic_source_q_interval_cv 0 0 0)` by
           fs
             [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
              compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
      >> imp_res_tac
           compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
      >> simp [rich_listTheory.LIST_REL_REPLICATE_same])
  >> ACCEPT_TAC bounded_case16594_object_pi_half_semantic_valid
QED

Definition bounded_case16594_object_nonpoly_step_body_def:
  bounded_case16594_object_nonpoly_step_body =
    If (Uop Ispair (Var «source»))
      (If (Binop Eq (Uop Fst (Var «source»)) (Num 1))
        (App «candle_cv_q_packed_object_sqrt_step»
          [Var «radii»;Var «certificates»;Var «stack»])
        (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
      (If (Binop Eq (Var «source») (Num 2))
        (Pair
          (Uop Fst
            (App «candle_cv_q_packed_object_poly_step»
              [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
               Var «source»;Var «stack»]))
          (Pair
            (Uop Snd
              (App «candle_cv_q_packed_object_poly_step»
                [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
                 Var «source»;Var «stack»]))
            (Var «certificates»)))
        (If (Binop Eq (Var «source») (Num 3))
          (Pair
            (Uop Fst
              (App «candle_cv_q_packed_object_poly_step»
                [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
                 Var «source»;Var «stack»]))
            (Pair
              (Uop Snd
                (App «candle_cv_q_packed_object_poly_step»
                  [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
                   Var «source»;Var «stack»]))
              (Var «certificates»)))
          (If (Binop Eq (Var «source») (Num 4))
            (Pair
              (Uop Fst
                (App «candle_cv_q_packed_object_poly_step»
                  [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
                   Var «source»;Var «stack»]))
              (Pair
                (Uop Snd
                  (App «candle_cv_q_packed_object_poly_step»
                    [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
                     Var «source»;Var «stack»]))
                (Var «certificates»)))
            (If (Binop Eq (Var «source») (Num 5))
              (Pair
                (Uop Fst
                  (App «candle_cv_q_packed_object_poly_step»
                    [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
                     Var «source»;Var «stack»]))
                (Pair
                  (Uop Snd
                    (App «candle_cv_q_packed_object_poly_step»
                      [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
                       Var «source»;Var «stack»]))
                  (Var «certificates»)))
              (If (Binop Eq (Var «source») (Num 6))
                (App «candle_cv_q_packed_object_inv_step»
                  [Var «radii»;Var «certificates»;Var «stack»])
                (If (Binop Eq (Var «source») (Num 7))
                  (App «candle_cv_q_packed_object_atn_step»
                    [Var «radii»;Var «certificates»;Var «stack»])
                  (If (Binop Eq (Var «source») (Num 8))
                    (Pair (Num 1)
                      (Pair
                        (Pair
                          (App «candle_cv_q_packed_object_pi_half_state» [])
                          (Var «stack»))
                        (Var «certificates»)))
                    (Pair (Num 0)
                      (Pair (Var «stack»)
                        (Var «certificates»))))))))))
End

Theorem bounded_case16594_object_nonpoly_step_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_nonpoly_step» =
    SOME
      ([«center_boxes»;«outer_boxes»;«radii»;«source»;«certificates»;
        «stack»],bounded_case16594_object_nonpoly_step_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_nonpoly_step_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_nonpoly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv source;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («source»,from_cv source);(«certificates»,from_cv certificates);
         («stack»,from_cv stack)]
        bounded_case16594_object_nonpoly_step_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> simp [bounded_case16594_object_nonpoly_step_lookup]
QED

Theorem bounded_case16594_object_nonpoly_pi_half_eval:
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_nonpoly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 8);from_cv certificates;
         from_cv (bounded_object_q_cv_list runtime_stack)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (bounded_object_q_cv_list
              (bounded_case16594_object_pi_half_runtime_cv::runtime_stack))
            certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_nonpoly_step_unfold]
  >> simp
       [bounded_case16594_object_nonpoly_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_execTheory.from_cv_def]
  >> simp
       [compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_compute_eval_if_ispair_num,
        compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_compute_eval_if_num_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_compute_eval_success_state)
  >> irule bounded_case16594_object_pi_half_state_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_pi_half_eval_runtime_refines:
  bounded_object_q_taylor_stack_runtime_refines
      runtime_stack semantic_stack /\
  4 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 0);from_cv (Num 8);from_cv certificates;
         from_cv (bounded_object_q_cv_list runtime_stack)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (bounded_object_q_cv_list
              (bounded_case16594_object_pi_half_runtime_cv::runtime_stack))
            certificates))),refs) /\
  bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticPiHalf
      (semantic_stack,semantic_certificates)
      (bounded_case16594_object_pi_half_semantic::semantic_stack,
       semantic_certificates) /\
  bounded_object_q_taylor_stack_runtime_refines
      (bounded_case16594_object_pi_half_runtime_cv::runtime_stack)
      (bounded_case16594_object_pi_half_semantic::semantic_stack)
Proof
  strip_tac
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_nonpair_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule bounded_case16594_object_nonpoly_pi_half_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def,
        bounded_case16594_object_pi_half_semantic_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def,bounded_case16594_object_pi_half_runtime_refines]
QED

val _ = export_theory ();
