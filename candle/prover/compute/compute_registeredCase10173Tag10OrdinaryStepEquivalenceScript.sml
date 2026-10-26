(*****************************************************************************
 * Exact old/tag-10 evaluator equivalence for the four ordinary instruction
 * shapes occurring in the authenticated case-10173 source templates.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10OrdinaryStepEquivalence
Ancestors
  compute_registeredCase10173Tag10OrdinaryStepCongruence
Libs
  bossLib preamble

Theorem registered_case10173_old_fso_program_step_poly_uop_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,
        from_cv (Pair (Num 0) (center_program:cv) : cv));
       («box_instruction»,
        from_cv (Pair (Num 0) (box_program:cv) : cv));
       («stack»,from_cv stack)]
      registered_case10173_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (Pair
      (App «candle_cv_fsa_item_fixed»
        [App «candle_cv_fs_poly_program»
          [from_cv center_boxes;from_cv radii;
           Uop Snd (Pair (Num 0) (from_cv center_program))]])
      (from_cv stack)) refs
Proof
  simp
    [compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def]
  >> PURE_REWRITE_TAC
       [compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_pair0_ispair,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_pair_first_zero]
  >> REFL_TAC
QED

Theorem registered_case10173_old_fso_program_step_sqrt_uop_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,
        from_cv (Pair (Num 1) (center_certificate:cv) : cv));
       («box_instruction»,
        from_cv (Pair (Num 1) (box_certificate:cv) : cv));
       («stack»,from_cv stack)]
      registered_case10173_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (Pair
      (App «candle_cv_fsn_item_sqrt»
        [from_cv radii;
         Uop Snd (Pair (Num 1) (from_cv center_certificate));
         Uop Snd (Pair (Num 1) (from_cv box_certificate));
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            from_cv stack]])
      (App «candle_cv_fsa_item_tail»
        [from_cv stack])) refs
Proof
  simp
    [compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_pair_num_ispair,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_pair_first_num_eq]
QED

Theorem registered_case10173_old_fso_program_step_mul_general_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);(«center_instruction»,from_cv (Num 4));
       («box_instruction»,from_cv (Num 4));(«stack»,from_cv stack)]
      registered_case10173_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (Pair
      (App «candle_cv_fso_item_mul»
        [from_cv radii;
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            App «candle_cv_fsa_item_tail» [from_cv stack]];
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;from_cv stack]])
      (App «candle_cv_fsa_item_tail»
        [App «candle_cv_fsa_item_tail» [from_cv stack]])) refs
Proof
  simp
    [compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_num_not_pair,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_num_eq]
QED

Theorem registered_case10173_tag10_fso_program_step_mul_general_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);(«center_instruction»,from_cv (Num 4));
       («box_instruction»,from_cv (Num 4));(«stack»,from_cv stack)]
      registered_case10173_tag10_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (Pair
      (App «candle_cv_fso_item_mul»
        [from_cv radii;
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            App «candle_cv_fsa_item_tail» [from_cv stack]];
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;from_cv stack]])
      (App «candle_cv_fsa_item_tail»
        [App «candle_cv_fsa_item_tail» [from_cv stack]])) refs
Proof
  simp
    [compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_num_not_pair,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_num_eq]
QED

Theorem registered_case10173_old_fso_program_step_add_general_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);(«center_instruction»,from_cv (Num 3));
       («box_instruction»,from_cv (Num 3));(«stack»,from_cv stack)]
      registered_case10173_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (Pair
      (App «candle_cv_fsa_item_add»
        [Num 1;from_cv radii;
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            App «candle_cv_fsa_item_tail» [from_cv stack]];
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;from_cv stack]])
      (App «candle_cv_fsa_item_tail»
        [App «candle_cv_fsa_item_tail» [from_cv stack]])) refs
Proof
  simp
    [compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_num_not_pair,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_num_eq]
QED

Theorem registered_case10173_tag10_fso_program_step_add_general_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);(«center_instruction»,from_cv (Num 3));
       («box_instruction»,from_cv (Num 3));(«stack»,from_cv stack)]
      registered_case10173_tag10_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (Pair
      (App «candle_cv_fsa_item_add»
        [Num 1;from_cv radii;
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            App «candle_cv_fsa_item_tail» [from_cv stack]];
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;from_cv stack]])
      (App «candle_cv_fsa_item_tail»
        [App «candle_cv_fsa_item_tail» [from_cv stack]])) refs
Proof
  simp
    [compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_num_not_pair,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_num_eq]
QED

Theorem registered_case10173_tag10_fso_program_step_sqrt_general_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,
        from_cv (Pair (Num 1) (center_certificate:cv) : cv));
       («box_instruction»,
        from_cv (Pair (Num 1) (box_certificate:cv) : cv));
       («stack»,from_cv stack)]
      registered_case10173_tag10_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (Pair
      (App «candle_cv_fsn_item_sqrt»
        [from_cv radii;
         Uop Snd (Pair (Num 1) (from_cv center_certificate));
         Uop Snd (Pair (Num 1) (from_cv box_certificate));
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;from_cv stack]])
      (App «candle_cv_fsa_item_tail» [from_cv stack])) refs
Proof
  simp
    [compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_pair_num_ispair,
     compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_eval_if_pair_first_num_eq]
QED

Theorem registered_case10173_tag10_fso_program_step_eval_cong_from_bodies:
  0 < clock /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
         («radii»,from_cv radii);
         («center_instruction»,from_cv center_instruction);
         («box_instruction»,from_cv box_instruction);
         («stack»,from_cv stack)]
        registered_case10173_fso_program_step_body) (refs:hol_refs) =
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
         («radii»,from_cv radii);
         («center_instruction»,from_cv center_instruction);
         («box_instruction»,from_cv box_instruction);
         («stack»,from_cv stack)]
        registered_case10173_tag10_fso_program_step_body) refs ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv center_instruction;from_cv box_instruction;from_cv stack])
      refs =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv center_instruction;from_cv box_instruction;from_cv stack]) refs
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_program_step_fixed_nonlinear»
          [from_cv center_boxes;from_cv boxes;from_cv radii;
           from_cv center_instruction;from_cv box_instruction;from_cv stack])
        refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (subst
          [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
           («radii»,from_cv radii);
           («center_instruction»,from_cv center_instruction);
           («box_instruction»,from_cv box_instruction);
           («stack»,from_cv stack)]
          registered_case10173_fso_program_step_body) refs` by
       (irule
          compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fso_program_step_unfold
        >> asm_rewrite_tac [])
  >> `compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_fso_program_step_fixed_nonlinear»
          [from_cv center_boxes;from_cv boxes;from_cv radii;
           from_cv center_instruction;from_cv box_instruction;from_cv stack])
        refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (subst
          [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
           («radii»,from_cv radii);
           («center_instruction»,from_cv center_instruction);
           («box_instruction»,from_cv box_instruction);
           («stack»,from_cv stack)]
          registered_case10173_tag10_fso_program_step_body) refs` by
       (irule
          compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_fso_program_step_unfold
        >> asm_rewrite_tac [])
  >> metis_tac []
QED

Theorem registered_case10173_tag10_fso_program_step_poly_eval_cong:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Pair (Num 0) (center_program:cv) : cv);
         from_cv (Pair (Num 0) (box_program:cv) : cv);
         from_cv stack]) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Pair (Num 0) (center_program:cv) : cv);
         from_cv (Pair (Num 0) (box_program:cv) : cv);
         from_cv stack]) refs
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
             («radii»,from_cv radii);
             («center_instruction»,
              from_cv (Pair (Num 0) (center_program:cv) : cv));
             («box_instruction»,
              from_cv (Pair (Num 0) (box_program:cv) : cv));
             («stack»,from_cv stack)]
            registered_case10173_fso_program_step_body) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fso_program_step_unfold
      >> asm_rewrite_tac [])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_tag10_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
             («radii»,from_cv radii);
             («center_instruction»,
              from_cv (Pair (Num 0) (center_program:cv) : cv));
             («box_instruction»,
              from_cv (Pair (Num 0) (box_program:cv) : cv));
             («stack»,from_cv stack)]
            registered_case10173_tag10_fso_program_step_body) refs`
  >> conj_tac
  >- (PURE_REWRITE_TAC
        [registered_case10173_old_fso_program_step_poly_uop_control_eval,
         compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_fso_program_step_poly_control_eval]
      >> irule
           compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_eval_cong
      >> simp
           [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
            compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_reachable_def,
            compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv])
  >> once_rewrite_tac [EQ_SYM_EQ]
  >> irule
       compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_fso_program_step_unfold
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_tag10_fso_program_step_mul_eval_cong:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Num 4);from_cv (Num 4);from_cv stack]) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Num 4);from_cv (Num 4);from_cv stack]) refs
Proof
  strip_tac
  >> irule registered_case10173_tag10_fso_program_step_eval_cong_from_bodies
  >> conj_tac >- asm_rewrite_tac []
  >> PURE_REWRITE_TAC
       [registered_case10173_old_fso_program_step_mul_general_control_eval,
        registered_case10173_tag10_fso_program_step_mul_general_control_eval]
  >> irule
       compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_fso_program_step_add_eval_cong:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Num 3);from_cv (Num 3);from_cv stack]) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Num 3);from_cv (Num 3);from_cv stack]) refs
Proof
  strip_tac
  >> irule registered_case10173_tag10_fso_program_step_eval_cong_from_bodies
  >> conj_tac >- asm_rewrite_tac []
  >> PURE_REWRITE_TAC
       [registered_case10173_old_fso_program_step_add_general_control_eval,
        registered_case10173_tag10_fso_program_step_add_general_control_eval]
  >> irule
       compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_fso_program_step_sqrt_eval_cong:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Pair (Num 1) (center_certificate:cv) : cv);
         from_cv (Pair (Num 1) (box_certificate:cv) : cv);
         from_cv stack]) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Pair (Num 1) (center_certificate:cv) : cv);
         from_cv (Pair (Num 1) (box_certificate:cv) : cv);
         from_cv stack]) refs
Proof
  strip_tac
  >> irule registered_case10173_tag10_fso_program_step_eval_cong_from_bodies
  >> conj_tac >- asm_rewrite_tac []
  >> PURE_REWRITE_TAC
       [registered_case10173_old_fso_program_step_sqrt_uop_control_eval,
        registered_case10173_tag10_fso_program_step_sqrt_general_control_eval]
  >> irule
       compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Definition registered_case10173_tag10_supported_instruction_pair_def:
  registered_case10173_tag10_supported_instruction_pair center box <=>
    (?center_program box_program.
       center = Pair (Num 0) center_program /\
       box = Pair (Num 0) box_program) \/
    (?center_certificate box_certificate.
       center = Pair (Num 1) center_certificate /\
       box = Pair (Num 1) box_certificate) \/
    (center = Num 3 /\ box = Num 3) \/
    (center = Num 4 /\ box = Num 4)
End

Theorem registered_case10173_tag10_supported_step_eval_cong:
  registered_case10173_tag10_supported_instruction_pair
      center_instruction box_instruction /\
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv center_instruction;from_cv box_instruction;from_cv stack])
      (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv center_instruction;from_cv box_instruction;from_cv stack]) refs
Proof
  rw [registered_case10173_tag10_supported_instruction_pair_def]
  >> FIRST
       [irule registered_case10173_tag10_fso_program_step_poly_eval_cong,
        irule registered_case10173_tag10_fso_program_step_sqrt_eval_cong,
        irule registered_case10173_tag10_fso_program_step_add_eval_cong,
        irule registered_case10173_tag10_fso_program_step_mul_eval_cong]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
