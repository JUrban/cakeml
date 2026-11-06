(*****************************************************************************
 * Clock-parametric form of the authenticated genuine cell-0 entry theorem. *
 *                                                                            *
 * The whole-call wrapper consumes a small amount of evaluator clock before  *
 * invoking the production dispatcher.  Preserve the existing structural     *
 * bound instead of specializing the entry theorem to compute_default_clock.  *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0FastHolLightEntryClock
Ancestors
  compute_boundedCase16594Cell0FastHolLightEntryIdentity
Libs
  bossLib preamble intLib

Theorem bounded_case16594_cell0_authenticated_fast_object_entry_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_runtime_cell0_codes_cv + 3 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    bounded_case16594_cell0_authenticated_fast_object_entry_cexp
    (refs:hol_refs) =
      (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 1`]
         compute_boundedCase16594Cell0AuthenticatedFastObjectEntryTheory.bounded_case16594_cell0_authenticated_object_accepted_program_eval_clock)
  >> impl_tac
  >- intLib.ARITH_TAC
  >> disch_then
       (qx_choose_then `runtime_state`
         (qx_choose_then `runtime_center`
           (qx_choose_then `runtime_center_gradient`
             (qx_choose_then `runtime_value_bound`
               (qx_choose_then `runtime_gradient_bounds`
                 (qx_choose_then `runtime_hessian` strip_assume_tac))))))
  >> rw
       [compute_boundedCase16594Cell0AuthenticatedFastObjectEntryTheory.bounded_case16594_cell0_authenticated_fast_object_entry_cexp_def]
  >> irule EQ_TRANS
  >> qexists_tac `(M_success (from_cv (Num 1)),refs)`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchEntryControlEvalTheory.bounded_case16594_object_dispatch_entry_from_program_eval
      >> conj_tac
      >- intLib.ARITH_TAC
      >> qexists_tac `runtime_center_gradient`
      >> qexists_tac `runtime_center`
      >> qexists_tac `bounded_object_q_cv_list runtime_gradient_bounds`
      >> qexists_tac `runtime_hessian`
      >> qexists_tac `runtime_value_bound`
      >> simp
           [compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_payload_identity]
      >> fs [compute_execTheory.from_cv_def])
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_cell0_fast_hol_light_entry_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_runtime_cell0_codes_cv + 3 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    bounded_case16594_cell0_fast_hol_light_entry (refs:hol_refs) =
      (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> once_rewrite_tac
       [compute_boundedCase16594Cell0FastHolLightEntryIdentityTheory.bounded_case16594_cell0_fast_hol_light_entry_authenticated_identity]
  >> irule bounded_case16594_cell0_authenticated_fast_object_entry_eval_clock
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
