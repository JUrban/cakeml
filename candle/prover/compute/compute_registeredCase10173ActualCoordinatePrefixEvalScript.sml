(*****************************************************************************
 * Clock-uniform evaluation of the six actual coordinate/sqrt source pairs.
 *
 * The authenticated actual-operand contract is recursive.  This layer turns
 * every one of its entries into the two literal numerical contracts consumed
 * by the ordinary source prefix: the coordinate polynomial program and the
 * following square-root result operation.  No numerical operation is replayed
 * here; both results come from the already checked decimal witnesses.
 *****************************************************************************)
Theory compute_registeredCase10173ActualCoordinatePrefixEval
Ancestors
  compute_registeredCase10173ActualVariableProgramEval
  compute_registeredCase10173ActualSqrtSourcePrefixEval
  compute_registeredCase10173OrdinaryStepAboveEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_zero_hessian_rows:
  bounded_hessian64_rows (bounded_interval64_zeros 21) =
    SOME (REPLICATE 6 (REPLICATE 6 bounded_interval64_zero))
Proof
  EVAL_TAC
QED

Theorem bounded_case10173_actual_variable_decimal_hessian:
  bounded_case10173_actual_variable_decimal radii dimensions variable =
    SOME
      (BoundedTaylor64 domain_flag center_value center_gradient value_bound
        gradient_bounds hessian) ==>
  hessian = bounded_interval64_zeros 21
Proof
  rw
    [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_variable_decimal_def]
  >> every_case_tac
  >> gvs
       [compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_def]
  >> every_case_tac
  >> gvs
       [compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
        LET_THM]
QED

Theorem registered_case10173_actual_variable_poly_program_eval_above:
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME dimensions /\
  LENGTH radii = 6 /\
  LENGTH dimensions = 6 /\
  variable < 6 /\
  zero_rows = REPLICATE 6 (REPLICATE 6 bounded_interval64_zero) /\
  bounded_hessian64_rows (bounded_interval64_zeros 21) = SOME zero_rows /\
  bounded_case10173_actual_variable_decimal radii dimensions variable =
      SOME result /\
  registered_case10173_eval_above 8208
      (App «candle_cv_fs_list_of_q» [from_cv source_radii])
      (registered_case10173_word64_object_cv_list radii) ==>
  registered_case10173_eval_above 8209
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv (Pair (Pair (Num 1) (Num variable)) (Num 0))])
      (bounded_taylor64_rows_object_cv result zero_rows)
Proof
  strip_tac
  >> rw
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_actual_variable_poly_program_eval)
  >> asm_rewrite_tac []
  >> conj_tac
  >- (qexists_tac `dimensions`
      >> qexists_tac `radii`
      >> asm_rewrite_tac []
      >> fs
           [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def])
  >> qexists_tac `REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)`
  >> simp []
QED

Definition registered_case10173_actual_coordinate_eval_prefix_def:
  registered_case10173_actual_coordinate_eval_prefix
      0 index center_boxes source_radii fixed_radii center_roots box_roots
      certificates = T /\
  registered_case10173_actual_coordinate_eval_prefix
      (SUC remaining) index center_boxes source_radii fixed_radii
      (Pair center_root center_roots) (Pair box_root box_roots)
      (certificate::certificates) =
    (?variable_result root_result.
       registered_case10173_eval_above 8209
         (App «candle_cv_fs_poly_program»
           [from_cv center_boxes;from_cv source_radii;
            from_cv (Pair (Pair (Num 1) (Num index)) (Num 0))])
         variable_result /\
       registered_case10173_eval_above 8209
         (App «candle_cv_fsn_result_sqrt»
           [from_cv fixed_radii;from_cv center_root;from_cv box_root;
            from_cv variable_result])
         root_result /\
       registered_case10173_actual_coordinate_eval_prefix
         remaining (SUC index) center_boxes source_radii fixed_radii
         center_roots box_roots certificates) /\
  registered_case10173_actual_coordinate_eval_prefix
      (SUC remaining) index center_boxes source_radii fixed_radii
      center_roots box_roots certificates = F
End

Theorem registered_case10173_actual_coordinate_eval_prefix_sound:
  !remaining index center_roots box_roots certificates.
    LENGTH radii = 6 /\
    LENGTH center_environment = 6 /\
    index + remaining <= 6 /\
    bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME center_environment /\
    registered_case10173_eval_above 8208
      (App «candle_cv_fs_list_of_q» [from_cv source_radii])
      (registered_case10173_word64_object_cv_list radii) /\
    bounded_case10173_actual_sqrt_source_prefix_exact remaining index radii
      center_environment center_roots box_roots certificates ==>
    registered_case10173_actual_coordinate_eval_prefix remaining index
      center_boxes source_radii
      (registered_case10173_word64_object_cv_list radii)
      center_roots box_roots certificates
Proof
  Induct_on `remaining`
  >- simp [registered_case10173_actual_coordinate_eval_prefix_def]
  >> rpt gen_tac
  >> Cases_on `center_roots`
  >- simp
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> Cases_on `box_roots`
  >- simp
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> Cases_on `certificates`
  >- simp
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> Cases_on `h`
  >> strip_tac
  >> imp_res_tac
       compute_registeredCase10173ActualSqrtSourcePrefixEvalTheory.registered_case10173_actual_sqrt_source_prefix_head_uniform_eval
  >> imp_res_tac bounded_case10173_actual_variable_decimal_hessian
  >> `source_hessian_rows =
        REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)` by
       fs [registered_case10173_zero_hessian_rows]
  >> simp [registered_case10173_actual_coordinate_eval_prefix_def]
  >> qexists_tac
       `bounded_taylor64_rows_object_cv
          (BoundedTaylor64 T center_value center_gradient value_bound
            gradient_bounds source_hessian) source_hessian_rows`
  >> qexists_tac `bounded_taylor64_rows_object_cv result result_rows`
  >> conj_tac
  >- (gvs []
      >> irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_actual_variable_poly_program_eval_above)
      >> conj_tac
      >- intLib.ARITH_TAC
      >> conj_tac
      >- (qexists_tac
            `REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)`
          >> simp [registered_case10173_zero_hessian_rows])
      >> qexists_tac `center_environment`
      >> qexists_tac `radii`
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_weaken
  >> qexists_tac `8192`
  >> conj_tac >- intLib.ARITH_TAC
  >> PURE_REWRITE_TAC
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def,
        COND_CLAUSES]
  >> fs
           [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def,
            compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_actual_six_coordinate_eval_prefix:
  LENGTH radii = 6 /\
  LENGTH center_environment = 6 /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
    SOME center_environment /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_list_of_q» [from_cv source_radii])
    (registered_case10173_word64_object_cv_list radii) /\
  bounded_case10173_actual_sqrt_source_prefix_exact 6 0 radii
    center_environment center_roots box_roots certificates ==>
  registered_case10173_actual_coordinate_eval_prefix 6 0 center_boxes
    source_radii (registered_case10173_word64_object_cv_list radii)
    center_roots box_roots certificates
Proof
  strip_tac
  >> irule registered_case10173_actual_coordinate_eval_prefix_sound
  >> simp []
  >> qexists_tac `center_environment`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
