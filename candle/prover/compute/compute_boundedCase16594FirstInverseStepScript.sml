(*****************************************************************************
 * Genuine case-16594 instruction-7 inverse vertical slice.
 *
 * These values were extracted from the complete top Taylor state immediately
 * before and after the first inverse in the 167-instruction native trace
 * (SHA-256 1a9f761060ad6cb6d05b45affb160c450d21b2ac423bfe3d96714b52d82f1173)
 * and certificate stream
 * (SHA-256 a320e38824920816c44ff961c42fb3007369781bc2bc55521f1907aa7dbe1a86).
 * They remain untrusted development fixtures: this theory proves the whole
 * fixed-word inverse operation and its ordinary-object refinement, but not
 * yet the fixture's position in the authenticated full-program topology.
 *****************************************************************************)
Theory compute_boundedCase16594FirstInverseStep
Ancestors
  compute_boundedAnalyticObjectProgramStepRefinement
Libs
  bossLib wordsLib

Definition bounded_case16594_first_inverse_input_def:
  bounded_case16594_first_inverse_input =
    BoundedInterval64
      (BoundedSigned64 F 1036597572434w)
      (BoundedSigned64 F 1036652548017w)
End

Definition bounded_case16594_first_inverse_reciprocal64_def:
  bounded_case16594_first_inverse_reciprocal64 =
    BoundedInterval64
      (BoundedSigned64 F 1166182268038w)
      (BoundedSigned64 F 1166244116100w)
End

Definition bounded_case16594_first_inverse_radii_def:
  bounded_case16594_first_inverse_radii =
    [161518258122w; 161518258122w; 161518258122w;
     323036516242w; 211308954991w; 323036516242w]
End

Definition bounded_case16594_first_inverse_weights_def:
  bounded_case16594_first_inverse_weights =
    [(161518258122w,161518258122w,F);
     (161518258122w,161518258122w,T);
     (161518258122w,161518258122w,T);
     (161518258122w,323036516242w,T);
     (161518258122w,211308954991w,T);
     (161518258122w,323036516242w,T);
     (161518258122w,161518258122w,F);
     (161518258122w,161518258122w,T);
     (161518258122w,323036516242w,T);
     (161518258122w,211308954991w,T);
     (161518258122w,323036516242w,T);
     (161518258122w,161518258122w,F);
     (161518258122w,323036516242w,T);
     (161518258122w,211308954991w,T);
     (161518258122w,323036516242w,T);
     (323036516242w,323036516242w,F);
     (323036516242w,211308954991w,T);
     (323036516242w,323036516242w,T);
     (211308954991w,211308954991w,F);
     (211308954991w,323036516242w,T);
     (323036516242w,323036516242w,F)]
End

Definition bounded_case16594_first_inverse_source_def:
  bounded_case16594_first_inverse_source =
    BoundedTaylor64 T
      bounded_case16594_first_inverse_input
      (REPLICATE 6 bounded_interval64_zero)
      bounded_case16594_first_inverse_input
      (REPLICATE 6 bounded_interval64_zero)
      (REPLICATE 21 bounded_interval64_zero)
End

Definition bounded_case16594_first_inverse_result_def:
  bounded_case16594_first_inverse_result =
    BoundedTaylor64 T
      bounded_case16594_first_inverse_reciprocal64
      (REPLICATE 6 bounded_interval64_zero)
      bounded_case16594_first_inverse_reciprocal64
      (REPLICATE 6 bounded_interval64_zero)
      (REPLICATE 21 bounded_interval64_zero)
End

Definition bounded_case16594_first_inverse_certificate_def:
  bounded_case16594_first_inverse_certificate =
    BoundedAnalytic64InverseCertificate
      bounded_case16594_first_inverse_reciprocal64
      bounded_case16594_first_inverse_reciprocal64
End

Definition bounded_case16594_first_inverse_object_source_def:
  bounded_case16594_first_inverse_object_source =
    BoundedObjectQTaylor T
      (bounded_interval64_object_q_cv
        bounded_case16594_first_inverse_input)
      (REPLICATE 6
        (bounded_interval64_object_q_cv bounded_interval64_zero))
      (bounded_interval64_object_q_cv
        bounded_case16594_first_inverse_input)
      (REPLICATE 6
        (bounded_interval64_object_q_cv bounded_interval64_zero))
      (REPLICATE 21
        (bounded_interval64_object_q_cv bounded_interval64_zero))
End

Theorem bounded_case16594_first_inverse_complete:
  bounded_taylor64_inverse
      bounded_case16594_first_inverse_radii
      bounded_case16594_first_inverse_reciprocal64
      bounded_case16594_first_inverse_reciprocal64
      bounded_case16594_first_inverse_source =
    SOME bounded_case16594_first_inverse_result
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_first_inverse_program_step:
  bounded_analytic64_program_step
      bounded_case16594_first_inverse_radii [] []
      BoundedAnalytic64Inverse
      ([bounded_case16594_first_inverse_source],
       [bounded_case16594_first_inverse_certificate]) =
    SOME ([bounded_case16594_first_inverse_result],[])
Proof
  simp
    [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
     bounded_case16594_first_inverse_complete,
     bounded_case16594_first_inverse_certificate_def]
QED

Theorem bounded_case16594_first_inverse_program_step_compositional:
  !word_rest certificate_rest center_environment box_environment.
    bounded_analytic64_program_step
        bounded_case16594_first_inverse_radii
        center_environment box_environment
        BoundedAnalytic64Inverse
        (bounded_case16594_first_inverse_source::word_rest,
         bounded_case16594_first_inverse_certificate::certificate_rest) =
      SOME
        (bounded_case16594_first_inverse_result::word_rest,
         certificate_rest)
Proof
  simp
    [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def,
     bounded_case16594_first_inverse_complete,
     bounded_case16594_first_inverse_certificate_def]
QED

Theorem bounded_case16594_first_inverse_source_covers_object:
  bounded_taylor64_stack_covers_object_q
    [bounded_case16594_first_inverse_source]
    [bounded_case16594_first_inverse_object_source]
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_first_inverse_radius_pairs:
  bounded_taylor_radius_pairs bounded_case16594_first_inverse_radii =
    SOME bounded_case16594_first_inverse_weights
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_first_inverse_refinement_premises:
  bounded_analytic64_state_covers_object_q
    ([bounded_case16594_first_inverse_source],
     [bounded_case16594_first_inverse_certificate])
    ([bounded_case16594_first_inverse_object_source],
     [bounded_case16594_first_inverse_certificate]) /\
  bounded_taylor_radius_pairs bounded_case16594_first_inverse_radii =
    SOME bounded_case16594_first_inverse_weights /\
  bounded_analytic64_program_step
    bounded_case16594_first_inverse_radii [] []
    BoundedAnalytic64Inverse
    ([bounded_case16594_first_inverse_source],
     [bounded_case16594_first_inverse_certificate]) =
    SOME ([bounded_case16594_first_inverse_result],[])
Proof
  simp
    [bounded_analytic64_state_covers_object_q_def,
     bounded_case16594_first_inverse_source_covers_object,
     bounded_case16594_first_inverse_radius_pairs,
     bounded_case16594_first_inverse_program_step]
QED

Theorem bounded_case16594_first_inverse_refines_ordinary_object_step:
  ?weights object_next.
    bounded_taylor_radius_pairs
        bounded_case16594_first_inverse_radii = SOME weights /\
    bounded_object_q_analytic_ordinary_step
      bounded_case16594_first_inverse_radii weights [] []
      BoundedAnalyticInverse
      ([bounded_case16594_first_inverse_object_source],
       [bounded_case16594_first_inverse_certificate])
      object_next /\
    bounded_analytic64_state_covers_object_q
      ([bounded_case16594_first_inverse_result],[]) object_next
Proof
  qexists_tac `bounded_case16594_first_inverse_weights`
  >> rewrite_tac
       [bounded_case16594_first_inverse_radius_pairs,
        bounded_case16594_first_inverse_certificate_def]
  >> irule
       (Q.INST
         [`word_value` |-> `bounded_case16594_first_inverse_source`,
          `word_rest` |-> `[]`,
          `center_reciprocal` |->
            `bounded_case16594_first_inverse_reciprocal64`,
          `box_reciprocal` |->
            `bounded_case16594_first_inverse_reciprocal64`,
          `certificate_rest` |-> `[]`,
          `object_value` |->
            `bounded_case16594_first_inverse_object_source`,
          `object_rest` |-> `[]`,
          `radii` |-> `bounded_case16594_first_inverse_radii`,
          `weights` |-> `bounded_case16594_first_inverse_weights`,
          `center_environment` |-> `[]`,
          `box_environment` |-> `[]`,
          `object_center_environment` |-> `[]`,
          `object_box_environment` |-> `[]`,
          `word_next` |->
            `([bounded_case16594_first_inverse_result],[])`]
         compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_inverse_step_refines_object_q)
  >> metis_tac
       [REWRITE_RULE
          [bounded_case16594_first_inverse_certificate_def]
          bounded_case16594_first_inverse_refinement_premises]
QED

val _ = export_theory ();
