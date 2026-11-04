(*****************************************************************************
 * Stack-level semantic adapters for the certificate-free ordinary branches.
 *
 * The numerical dispatch invariants return one related Taylor item.  Program
 * induction needs the stronger statement that the complete runtime stack is
 * related to the complete object stack and that the matching object-q
 * analytic step was taken.  These adapters provide that interface without
 * re-evaluating any numerical expression or naming a genuine instruction
 * index.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectOrdinaryDispatchStepInvariant
Ancestors
  compute_boundedCase16594ObjectCertifiedAtanDispatchInvariant
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_neg_dispatch_stack_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) /\
  4106 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 2);from_cv certificates;
         from_cv
           (bounded_object_q_cv_list (runtime_state::runtime_rest))])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair
              (bounded_object_q_cv_list (runtime_result::runtime_rest))
              certificates))),refs) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticNeg
      (semantic_state::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_neg semantic_radii weights semantic_state::
         semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_neg semantic_radii weights semantic_state::
         semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_state` |-> `runtime_state`,
          `semantic_state` |-> `semantic_state`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_neg_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> asm_rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_add_dispatch_stack_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_right::runtime_left::runtime_rest)
    (semantic_right::semantic_left::semantic_rest) /\
  4106 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 3);from_cv certificates;
         from_cv
           (bounded_object_q_cv_list
             (runtime_right::runtime_left::runtime_rest))])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair
              (bounded_object_q_cv_list (runtime_result::runtime_rest))
              certificates))),refs) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticAdd
      (semantic_right::semantic_left::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_add semantic_radii weights
         semantic_left semantic_right::semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_add semantic_radii weights
         semantic_left semantic_right::semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_left_state` |-> `runtime_left`,
          `semantic_left_state` |-> `semantic_left`,
          `runtime_right_state` |-> `runtime_right`,
          `semantic_right_state` |-> `semantic_right`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_add_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> asm_rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_mul_dispatch_stack_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_right::runtime_left::runtime_rest)
    (semantic_right::semantic_left::semantic_rest) /\
  4106 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 4);from_cv certificates;
         from_cv
           (bounded_object_q_cv_list
             (runtime_right::runtime_left::runtime_rest))])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair
              (bounded_object_q_cv_list (runtime_result::runtime_rest))
              certificates))),refs) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticMul
      (semantic_right::semantic_left::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_mul semantic_radii weights
         semantic_left semantic_right::semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_mul semantic_radii weights
         semantic_left semantic_right::semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_left_state` |-> `runtime_left`,
          `semantic_left_state` |-> `semantic_left`,
          `runtime_right_state` |-> `runtime_right`,
          `semantic_right_state` |-> `semantic_right`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_mul_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> asm_rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_square_dispatch_stack_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) /\
  4106 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Num 5);from_cv certificates;
         from_cv
           (bounded_object_q_cv_list (runtime_state::runtime_rest))])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair
              (bounded_object_q_cv_list (runtime_result::runtime_rest))
              certificates))),refs) /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticSquare
      (semantic_state::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_mul semantic_radii weights semantic_state
         semantic_state::semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_mul semantic_radii weights semantic_state
         semantic_state::semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_state` |-> `runtime_state`,
          `semantic_state` |-> `semantic_state`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_square_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> asm_rewrite_tac
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

val _ = export_theory ();
