(*****************************************************************************
 * Packet-parametric execution of a prepared literal case-10173 program.
 *
 * The two prepared programs are related to the exact literal 47-instruction
 * templates by explicit splice equalities.  The numerical work is supplied
 * by the authenticated literal-source contract; this layer evaluates only
 * the historical wrapper, source-derived center/radius preparation, splice
 * calls, stack-head selection, and fixed-to-rational handoff.
 *****************************************************************************)
Theory compute_registeredCase10173AuthenticatedFastProgramEval
Ancestors
  compute_registeredCase10173LiteralSourcePacketEval
  compute_registeredCase10173ProgramSpliceEval
  compute_registeredCase10173HistProgramEval
  compute_registeredCase10173CenterEnvironmentStructuralEval
  compute_registeredCase10173RadiusGeneralEval
  compute_registeredCase10173AuthenticatedLiteralHandoffEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fast_packet_hist_program_eval:
  LENGTH radii = 6 /\
  bounded_packed_chars_case10173_decimal_packet_ok
    (BoundedCase10173Packet radii
      [x0;x1;x2;x3;x4;x5] [y0;y1;y2;y3;y4;y5]
      [certificate0;certificate1;certificate2;
       certificate3;certificate4;certificate5]
      center_root_delta center_root_four_x0
      [center_root_derivative;center_root_four_reciprocal;
       center_u_reciprocal;center_special_root_reciprocal;
       center_b_reciprocal]
      box_root_delta box_root_four_x0
      [box_root_derivative;box_root_logarithmic;
       box_root_four_reciprocal;box_diagonal_reciprocal;
       box_u_reciprocal;box_special_root_reciprocal;
       box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal]) /\
  registered_case10173_q_center_environment_positive boxes =
    SOME center_boxes /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
    SOME [x0;x1;x2;x3;x4;x5] /\
  bounded_object_positive_q_interval64_decimal_list boxes =
    SOME [y0;y1;y2;y3;y4;y5] /\
  bounded_case10173_source_radii64_positive_q boxes = SOME radii /\
  bounded_case10173_actual_sqrt_source_prefix_exact 6 0 radii
    [x0;x1;x2;x3;x4;x5]
    (Pair center0
      (Pair center1
        (Pair center2
          (Pair center3 (Pair center4 (Pair center5 (Num 0)))))))
    (Pair box0
      (Pair box1
        (Pair box2
          (Pair box3 (Pair box4 (Pair box5 (Num 0)))))))
    [certificate0;certificate1;certificate2;
     certificate3;certificate4;certificate5] /\
  bounded_case10173_literal_source_decimal
    (BoundedCase10173Packet radii
      [x0;x1;x2;x3;x4;x5] [y0;y1;y2;y3;y4;y5]
      [certificate0;certificate1;certificate2;
       certificate3;certificate4;certificate5]
      center_root_delta center_root_four_x0
      [center_root_derivative;center_root_four_reciprocal;
       center_u_reciprocal;center_special_root_reciprocal;
       center_b_reciprocal]
      box_root_delta box_root_four_x0
      [box_root_derivative;box_root_logarithmic;
       box_root_four_reciprocal;box_diagonal_reciprocal;
       box_u_reciprocal;box_special_root_reciprocal;
       box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal]) =
    SOME
      (BoundedTaylor64 T center_value center_gradient value_bound
        gradient_bounds hessian) /\
  registered_case10173_hist_splice_cv 31 box_program =
    registered_case10173_cv_append
      (registered_case10173_source_prefix_template
        box0 box1 box2 box3 box4 box5)
      (Pair (Num 9) registered_case10173_source_suffix_template) /\
  registered_case10173_hist_splice_cv 31 center_program =
    registered_case10173_cv_append
      (registered_case10173_source_prefix_template
        center0 center1 center2 center3 center4 center5)
      (Pair (Num 9) registered_case10173_source_suffix_template) /\
  registered_case10173_cv_list_length box_program = 54 /\
  registered_case10173_cv_list_length center_program = 54 /\
  roots = bounded_interval64_object_cv_list
    [center_root_delta;center_root_four_x0;
     box_root_delta;box_root_four_x0] /\
  40000 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program»
        [from_cv center_program;from_cv box_program;
         from_cv boxes;from_cv roots])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_fixed_q_taylor_object_cv
          (BoundedTaylor64 T center_value center_gradient value_bound
            gradient_bounds hessian)
          (registered_case10173_taylor_rows
            (BoundedTaylor64 T center_value center_gradient value_bound
              gradient_bounds hessian)))),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_registeredCase10173AuthenticatedLiteralHandoffEvalTheory.bounded_case10173_literal_source_decimal_well_formed
  >> imp_res_tac
       compute_registeredCase10173CenterEnvironmentStructuralEvalTheory.registered_case10173_center_list_length_positive_decode
  >> irule
       compute_registeredCase10173HistProgramEvalTheory.registered_case10173_hist_program_eval_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `center_boxes`
  >> qexists_tac
       `Pair (Num 1)
          (registered_case10173_taylor_object
            (BoundedTaylor64 T center_value center_gradient value_bound
              gradient_bounds hessian))`
  >> qexists_tac
       `registered_case10173_q_cv_list
          (MAP
            (\value.
              (bounded_word64_object_cv value,Num 999999999999))
            radii)`
  >> qexists_tac
       `Pair
          (Pair (Num 1)
            (registered_case10173_taylor_object
              (BoundedTaylor64 T center_value center_gradient value_bound
                gradient_bounds hessian)))
          (Num 0)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CenterEnvironmentStructuralEvalTheory.registered_case10173_q_center_environment_positive_eval_structural
      >> simp []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (`compute_eval (clock - 3)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_case10173_hist_program_run»
            [from_cv center_boxes;from_cv boxes;
             from_cv
               (registered_case10173_q_cv_list
                 (MAP
                   (\value.
                     (bounded_word64_object_cv value,Num 999999999999))
                   radii));
             from_cv roots;
             App «candle_cv_case10173_hist_splice_aux»
               [Num 31;from_cv center_program];
             App «candle_cv_case10173_hist_splice_aux»
               [Num 31;from_cv box_program];
             Num 0]) refs =
        compute_eval (clock - 3)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_case10173_hist_program_run»
            [from_cv center_boxes;from_cv boxes;
             from_cv
               (registered_case10173_q_cv_list
                 (MAP
                   (\value.
                     (bounded_word64_object_cv value,Num 999999999999))
                   radii));
             from_cv roots;
             from_cv
               (registered_case10173_hist_splice_cv 31 center_program);
             from_cv
               (registered_case10173_hist_splice_cv 31 box_program);
             from_cv (Num 0)]) refs` by
         (irule
            compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_compute_eval_app7_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> rpt conj_tac
          >> FIRST
               [irule
                  compute_registeredCase10173ProgramSpliceEvalTheory.registered_case10173_prepared_program_splice_eval
                >> asm_rewrite_tac []
                >> intLib.ARITH_TAC,
                simp
                  [compute_execProofTheory.compute_eval_from_cv,
                   compute_execTheory.from_cv_def,
                   compute_evalTheory.compute_eval_def,
                   ml_monadBaseTheory.st_ex_return_def]])
      >> pop_assum SUBST1_TAC
      >> asm_rewrite_tac []
      >> irule
           (SIMP_RULE std_ss
             [compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_result_push_def]
             compute_registeredCase10173LiteralSourcePacketEvalTheory.registered_case10173_literal_source_packet_eval)
      >> `38266 < clock - 3` by intLib.ARITH_TAC
      >> metis_tac [])
  >> conj_tac
  >- (irule
        compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_head_cons_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule
        compute_registeredCase10173AuthenticatedLiteralHandoffEvalTheory.registered_case10173_literal_result_item_to_q_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173RadiusGeneralEvalTheory.registered_case10173_source_radii_complete_eval
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
