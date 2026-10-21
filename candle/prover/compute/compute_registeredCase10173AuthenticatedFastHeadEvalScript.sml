(*****************************************************************************
 * One packet-parametric fast head for the authenticated case-10173 stream.
 *
 * This composes the authenticated object/source bindings, structural root
 * and production guards, exact source-program preparation, the literal
 * fixed-width evaluator, and the certified rational handoff.  The result is
 * the local head contract consumed by the already-proved 4,173-job stream
 * recursion; no packet-specific closed evaluation occurs here.
 *****************************************************************************)
Theory compute_registeredCase10173AuthenticatedFastHeadEval
Ancestors
  compute_registeredCase10173AuthenticatedEval
  compute_registeredCase10173HistoricalItemAuthenticatedEval
  compute_registeredCase10173ProgramPreparationPacketEval
  compute_registeredCase10173ProgramTemplateExactEval
  compute_registeredCase10173AuthenticatedFastProgramEval
  compute_registeredCase10173RootRecordAuthenticatedEval
  compute_registeredCase10173ProductionGuardPacketEval
  compute_registeredCase10173CertifiedCheckEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_actual_sqrt_prefix_six_ignores_tail:
  bounded_case10173_actual_sqrt_source_prefix_exact 6 index radii environment
      (registered_case10173_cv_of_list
        [center0;center1;center2;center3;center4;center5;center_tail])
      (registered_case10173_cv_of_list
        [box0;box1;box2;box3;box4;box5;box_tail])
      [certificate0;certificate1;certificate2;
       certificate3;certificate4;certificate5] =
  bounded_case10173_actual_sqrt_source_prefix_exact 6 index radii environment
      (registered_case10173_cv_of_list
        [center0;center1;center2;center3;center4;center5])
      (registered_case10173_cv_of_list
        [box0;box1;box2;box3;box4;box5])
      [certificate0;certificate1;certificate2;
       certificate3;certificate4;certificate5]
Proof
  PURE_REWRITE_TAC
    [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def]
  >> Cases_on `certificate0`
  >> Cases_on `certificate1`
  >> Cases_on `certificate2`
  >> Cases_on `certificate3`
  >> Cases_on `certificate4`
  >> Cases_on `certificate5`
  >> PURE_REWRITE_TAC [DECIDE ``6 = SUC 5``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> PURE_REWRITE_TAC [DECIDE ``5 = SUC 4``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> PURE_REWRITE_TAC [DECIDE ``4 = SUC 3``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> PURE_REWRITE_TAC [DECIDE ``3 = SUC 2``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> PURE_REWRITE_TAC [DECIDE ``2 = SUC 1``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> PURE_REWRITE_TAC [DECIDE ``1 = SUC 0``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> simp []
QED

Theorem registered_case10173_decimal_authenticated_fast_head_refines:
  registered_case10173_decimal_authenticated_head_refines
    20000000 registered_case10173_genuine_source_program
Proof
  rw
    [compute_registeredCase10173AuthenticatedEvalTheory.registered_case10173_decimal_authenticated_head_refines_def]
  >> drule
       compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_authenticated_source_program_preparation
  >> disch_then (qspecl_then [`root_record`,`object_job`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> drule
       compute_registeredCase10173ProgramTemplateExactEvalTheory.registered_case10173_authenticated_source_programs_exact
  >> disch_then (qspecl_then [`root_record`,`object_job`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> gvs []
  >> drule
       compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_source_actual_sqrt_contract_components
  >> strip_tac
  >> gvs []
  >> fs
       [compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_root_inputs_exact_def]
  >> drule
       compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_center_exact_components
  >> strip_tac
  >> gvs
       [compute_boundedCase10173JobBindingTheory.bounded_case10173_object_job_boxes_def]
  >> drule
       compute_boundedCase10173HistoricalCellDecimalBoundaryTheory.bounded_case10173_decimal_packet_box_binds_object_job_components
  >> strip_tac
  >> gvs
       [compute_boundedCase10173JobBindingTheory.bounded_case10173_object_job_boxes_def]
  >> drule
       compute_registeredCase10173RadiusBindingTheory.bounded_case10173_decimal_packet_source_radii_exact_components
  >> strip_tac
  >> gvs
       [compute_boundedCase10173JobBindingTheory.bounded_case10173_object_job_boxes_def]
  >> drule
       compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_source_accepts_contract
  >> strip_tac
  >> qpat_x_assum `bounded_packed_chars_case10173_decimal_packet_ok _`
       (fn th =>
         mp_tac th
         >> simp
              [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def])
  >> every_case_tac
  >> gvs []
  >> strip_tac
  >> drule
       compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell_accepts_decimal_contract
  >> strip_tac
  >> drule
       compute_boundedObjectCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_registeredCase10173RootRecordAuthenticatedEvalTheory.registered_case10173_root_geometry_ok_lengths
  >> fs
       [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_input_binding_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_auxiliary_binding_def]
  >> imp_res_tac
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_root_binding_exact_cv
  >> imp_res_tac
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_box_exact_components
  >> imp_res_tac
       compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_add_coordinate_sqrts_decimal_lengths
  >> fs
       [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_root_coefficients_decimal_def]
  >> gvs [listTheory.LENGTH_EQ_NUM_compute]
  >> qexists_tac `Num 0`
  >> qexists_tac `box_program`
  >> qexists_tac `Num 0`
  >> qexists_tac `center_program`
  >> rpt gen_tac
  >> strip_tac
  >> fs
       [compute_registeredCase10173CheckedJobsEvalTheory.registered_case10173_hist_checked_job_head_eval_ok_def]
  >> conj_tac
  >- (irule
        compute_registeredCase10173RootRecordAuthenticatedEvalTheory.registered_case10173_hist_root_record_packet_accessor_eval
      >> imp_res_tac
           compute_registeredCase10173CenterEnvironmentStructuralEvalTheory.registered_case10173_center_list_length_positive_decode
      >> simp
           [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def,
            compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
            compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
            compute_boundedCase10173RootBindingTheory.bounded_case10173_packet_root_intervals_def]
      >> metis_tac [arithmeticTheory.LESS_TRANS])
  >> conj_tac
  >- (irule
        compute_registeredCase10173ProductionGuardPacketEvalTheory.registered_case10173_hist_production_guard_packet_accessor_eval
      >> imp_res_tac
           compute_registeredCase10173CenterEnvironmentStructuralEvalTheory.registered_case10173_center_list_length_positive_decode
      >> simp
           [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def,
            compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
            compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
            compute_boundedCase10173RootBindingTheory.bounded_case10173_packet_root_intervals_def]
      >> metis_tac [arithmeticTheory.LESS_TRANS])
  >> Cases_on `value_bound`
  >> gvs []
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_hist_certified_check_fst_accept
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `registered_case10173_fixed_q_endpoint_cv b0`
  >> qexists_tac
       `registered_case10173_fixed_q_taylor_object_cv
          (BoundedTaylor64 T center_value center_gradient
            (BoundedInterval64 b b0) gradient_bounds hessian)
          (registered_case10173_taylor_rows
            (BoundedTaylor64 T center_value center_gradient
              (BoundedInterval64 b b0) gradient_bounds hessian))`
  >> conj_tac
  >- (irule
        compute_registeredCase10173AuthenticatedFastProgramEvalTheory.registered_case10173_fast_packet_hist_program_eval
      >> simp
           [compute_boundedCase10173RootBindingTheory.bounded_case10173_packet_root_intervals_def]
      >> (fn (asms,goal) =>
         let
           fun head_name term =
             fst (dest_const (fst (strip_comb term))) handle _ => ""
           val literal =
             valOf
               (List.find
                 (fn term =>
                   is_eq term andalso
                   head_name (lhs term) =
                     "bounded_case10173_literal_source_decimal") asms)
           val (_,literal_args) = strip_comb (lhs literal)
           val packet = hd literal_args
           val (_,packet_args) = strip_comb packet
           val sqrt_exact =
             valOf
               (List.find
                 (fn term =>
                   head_name term =
                     "bounded_case10173_actual_sqrt_source_prefix_exact")
                 asms)
           val (_,sqrt_args) = strip_comb sqrt_exact
           val (_,center_args) = strip_comb (List.nth (sqrt_args,4))
           val (_,box_args) = strip_comb (List.nth (sqrt_args,5))
           val (centers,_) = listSyntax.dest_list (hd center_args)
           val (boxes_for_sqrt,_) = listSyntax.dest_list (hd box_args)
           val (certificates,_) =
             listSyntax.dest_list (List.nth (packet_args,3))
           val (xs,_) = listSyntax.dest_list (List.nth (packet_args,1))
           val (ys,_) = listSyntax.dest_list (List.nth (packet_args,2))
           val (center_reciprocals,_) =
             listSyntax.dest_list (List.nth (packet_args,6))
           val (box_reciprocals,_) =
             listSyntax.dest_list (List.nth (packet_args,9))
           val center_values = List.take (centers,6)
           val box_values = List.take (boxes_for_sqrt,6)
           val witnesses =
             box_values @
             [List.nth (box_reciprocals,6),
              List.nth (box_reciprocals,3),
              List.nth (packet_args,7),
              List.nth (box_reciprocals,0),
              List.nth (box_reciprocals,2),
              List.nth (packet_args,8),
              List.nth (box_reciprocals,1),
              List.nth (box_reciprocals,5),
              List.nth (box_reciprocals,7),
              List.nth (box_reciprocals,8),
              List.nth (box_reciprocals,4)] @
             center_values @
             [List.nth (center_reciprocals,4),
              List.nth (packet_args,4),
              List.nth (center_reciprocals,0),
              List.nth (center_reciprocals,1),
              List.nth (packet_args,5),
              List.nth (center_reciprocals,3),
              List.nth (center_reciprocals,2)] @
             certificates @ xs @ ys
         in
           (MAP_EVERY exists_tac witnesses
            >> fs
                 [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
                  compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def,
                  compute_registeredCase10173RadiusBindingTheory.bounded_case10173_packet_radii_def,
                  compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
                  compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def])
             (asms,goal)
         end)
      >> (fn (asms,goal) =>
         let
           fun head_name term =
             fst (dest_const (fst (strip_comb term))) handle _ => ""
           fun numeric_first term =
             let val (_,args) = strip_comb term
             in numSyntax.is_numeral (hd args) end
             handle _ => false
           val tail_exact =
             valOf
               (List.find
                 (fn term =>
                   head_name term =
                     "bounded_case10173_actual_sqrt_source_prefix_exact" andalso
                   numeric_first term) asms)
           val helper =
             REWRITE_RULE
               [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def]
               registered_case10173_actual_sqrt_prefix_six_ignores_tail
           val instantiated = PART_MATCH lhs helper tail_exact
         in
           ACCEPT_TAC (EQ_MP instantiated (ASSUME tail_exact)) (asms,goal)
         end))
  >> irule
       compute_registeredCase10173AuthenticatedLiteralHandoffEvalTheory.registered_case10173_q_certified_finish_fixed_taylor_from_decimal_coverage_eval
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> qpat_x_assum `bounded_interval64_list_covers_object_q_decimal _ boxes`
       (fn th =>
         let val (_,args) = strip_comb (concl th)
         in exists_tac (hd args) >> assume_tac th end)
  >> fs
       [compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
