(*****************************************************************************
 * Genuine four-leaf topology discriminator for case 16594.                 *
 *                                                                           *
 * The seven-token stream and four exact source boxes were exported from     *
 * the sealed HOL Light prefix-4 fixture checkpoint                          *
 * 9ea29f9b0291dc193982b403197dd964cfbd78bfccd908040843141556fab474.         *
 * The fresh export receipt is                                               *
 * cv-case16594-prefix4-export-probe-v5-dev-001/input-probe.receipt.          *
 *                                                                           *
 * This is deliberately a small production-shape gate.  It exercises four   *
 * leaves and three genuine joins before any 875-cell fixture is generated.  *
 *****************************************************************************)
Theory compute_boundedCase16594Prefix4WholeTopologyProbe
Ancestors
  compute_boundedCase16594Prefix2WordWholeJobsProbe
  compute_boundedCase16594Cell0WordEntryProducer
  compute_boundedCase16594Cell0WholeCompactRunEval
Libs
  bossLib preamble cv_transLib

Definition bounded_case16594_prefix4_source_q_def:
  bounded_case16594_prefix4_source_q numerator denominator_minus_one =
    Pair (Pair (Num numerator) (Num 0)) (Num denominator_minus_one)
End

Definition bounded_case16594_prefix4_source_interval_def:
  bounded_case16594_prefix4_source_interval
      lower_numerator lower_denominator_minus_one
      upper_numerator upper_denominator_minus_one =
    Pair
      (bounded_case16594_prefix4_source_q
        lower_numerator lower_denominator_minus_one)
      (bounded_case16594_prefix4_source_q
        upper_numerator upper_denominator_minus_one)
End

Definition bounded_case16594_prefix4_source_box0_def:
  bounded_case16594_prefix4_source_box0 =
    Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3500160000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        4 0 2748032000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3500160000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        4 0 2936064000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        423903 39999 7028444000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3688192000001 639999999999)
      (Num 0))))))
End

Definition bounded_case16594_prefix4_source_box1_def:
  bounded_case16594_prefix4_source_box1 =
    Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3500160000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        4 0 2748032000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        3500160000001 639999999999 3688192000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        4 0 2936064000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        423903 39999 7028444000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3688192000001 639999999999)
      (Num 0))))))
End

Definition bounded_case16594_prefix4_source_box2_def:
  bounded_case16594_prefix4_source_box2 =
    Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3500160000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        2748032000001 639999999999 2936064000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3500160000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        4 0 2936064000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        423903 39999 7028444000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3688192000001 639999999999)
      (Num 0))))))
End

Definition bounded_case16594_prefix4_source_box3_def:
  bounded_case16594_prefix4_source_box3 =
    Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3500160000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        2748032000001 639999999999 2936064000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        3500160000001 639999999999 3688192000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        4 0 2936064000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        423903 39999 7028444000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3688192000001 639999999999)
      (Num 0))))))
End

Definition bounded_case16594_prefix4_whole_tokens_def:
  bounded_case16594_prefix4_whole_tokens =
    Pair (Num 0)
      (Pair (Num 0)
        (Pair (Pair (Num 3) (Num 0))
          (Pair (Num 0)
            (Pair (Num 0)
              (Pair (Pair (Num 3) (Num 0))
                (Pair (Pair (Num 2) (Num 0)) (Num 0)))))))
End

Definition bounded_case16594_prefix4_whole_jobs_def:
  bounded_case16594_prefix4_whole_jobs =
    Pair
      (bounded_case16594_word_whole_job
        bounded_case16594_cell0_source_word_center_environment
        bounded_case16594_cell0_authenticated_word_box_environment
        bounded_case16594_prefix4_source_box0)
    (Pair
      (bounded_case16594_word_whole_job
        bounded_case16594_prefix4_cell1_word_center_boxes
        bounded_case16594_prefix4_cell1_word_outer_boxes
        bounded_case16594_prefix4_source_box1)
    (Pair
      (bounded_case16594_word_whole_job
        bounded_case16594_prefix4_cell2_word_center_boxes
        bounded_case16594_prefix4_cell2_word_outer_boxes
        bounded_case16594_prefix4_source_box2)
    (Pair
      (bounded_case16594_word_whole_job
        bounded_case16594_prefix4_cell3_word_center_boxes
        bounded_case16594_prefix4_cell3_word_outer_boxes
        bounded_case16594_prefix4_source_box3)
      (Num 0))))
End

(* The compact topology transition reads only the third field of each job.
   Keep this closed literal separate so the small topology computation does
   not depend on translations for the word-level numerical payloads. *)
Definition bounded_case16594_prefix4_topology_jobs_def:
  bounded_case16594_prefix4_topology_jobs =
    Pair
      (Pair (Num 0)
        (Pair (Num 0) bounded_case16594_prefix4_source_box0))
    (Pair
      (Pair (Num 0)
        (Pair (Num 0) bounded_case16594_prefix4_source_box1))
    (Pair
      (Pair (Num 0)
        (Pair (Num 0) bounded_case16594_prefix4_source_box2))
    (Pair
      (Pair (Num 0)
        (Pair (Num 0) bounded_case16594_prefix4_source_box3))
      (Num 0))))
End

Definition bounded_case16594_prefix4_root_box_def:
  bounded_case16594_prefix4_root_box =
    Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3500160000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        4 0 2936064000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3688192000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        4 0 2936064000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        423903 39999 7028444000001 639999999999)
    (Pair
      (bounded_case16594_prefix4_source_interval
        6469 1249 3688192000001 639999999999)
      (Num 0))))))
End

Theorem bounded_case16594_prefix4_source_box0_identity:
  bounded_case16594_prefix4_source_box0 =
    bounded_case16594_cell0_whole_job_metadata
Proof
  rw
    [bounded_case16594_prefix4_source_box0_def,
     bounded_case16594_prefix4_source_interval_def,
     bounded_case16594_prefix4_source_q_def,
     compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_job_metadata_def]
QED

val _ = cv_trans
  compute_boundedCase16594Cell0WholeHolLightDataTheory.bounded_case16594_cell0_whole_hol_light_ceqs_def;
val _ = cv_trans
  compute_boundedCase16594Cell0WholeCombinedEntryTheory.bounded_case16594_cell0_whole_combined_ceqs_def;

val bounded_case16594_prefix4_whole_tokens_literal =
  REWRITE_CONV
    [bounded_case16594_prefix4_whole_tokens_def]
    ``bounded_case16594_prefix4_whole_tokens``;

val bounded_case16594_prefix4_topology_jobs_literal =
  REWRITE_CONV
    [bounded_case16594_prefix4_topology_jobs_def,
     bounded_case16594_prefix4_source_box0_def,
     bounded_case16594_prefix4_source_box1_def,
     bounded_case16594_prefix4_source_box2_def,
     bounded_case16594_prefix4_source_box3_def,
     bounded_case16594_prefix4_source_interval_def,
     bounded_case16594_prefix4_source_q_def]
    ``bounded_case16594_prefix4_topology_jobs``;

val bounded_case16594_prefix4_topology_call =
  ``compute_eval_pure 4096 bounded_case16594_cell0_whole_combined_ceqs
      (App
        «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
        [from_cv (Num 6);
         from_cv bounded_case16594_prefix4_whole_tokens;
         from_cv bounded_case16594_prefix4_topology_jobs;
         from_cv (Num 0)])``;

val bounded_case16594_prefix4_topology_literal_call =
  rhs
    (concl
      (REWRITE_CONV
        [bounded_case16594_prefix4_whole_tokens_literal,
         bounded_case16594_prefix4_topology_jobs_literal]
        bounded_case16594_prefix4_topology_call));

val bounded_case16594_prefix4_topology_pure_eval =
  time cv_eval bounded_case16594_prefix4_topology_literal_call;

val _ = save_thm
  ("bounded_case16594_prefix4_topology_pure_eval",
   bounded_case16594_prefix4_topology_pure_eval);

Theorem bounded_case16594_prefix4_topology_pure_eval_value:
  compute_eval_pure 4096 bounded_case16594_cell0_whole_combined_ceqs
      (App
        «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
        [from_cv (Num 6);
         from_cv bounded_case16594_prefix4_whole_tokens;
         from_cv bounded_case16594_prefix4_topology_jobs;
         from_cv (Num 0)]) =
    SOME
      (from_cv
        (Pair (Num 1)
          (Pair (Num 0)
            (Pair bounded_case16594_prefix4_root_box (Num 0)))))
Proof
  PURE_REWRITE_TAC
    [bounded_case16594_prefix4_whole_tokens_def,
     bounded_case16594_prefix4_topology_jobs_def,
     bounded_case16594_prefix4_source_box0_def,
     bounded_case16594_prefix4_source_box1_def,
     bounded_case16594_prefix4_source_box2_def,
     bounded_case16594_prefix4_source_box3_def,
     bounded_case16594_prefix4_root_box_def,
     bounded_case16594_prefix4_source_interval_def,
     bounded_case16594_prefix4_source_q_def]
  >> simp [bounded_case16594_prefix4_topology_pure_eval]
QED

Theorem bounded_case16594_prefix4_topology_eval:
  4096 <= clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App
        «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
        [from_cv (Num 6);
         from_cv bounded_case16594_prefix4_whole_tokens;
         from_cv bounded_case16594_prefix4_topology_jobs;
         from_cv (Num 0)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Num 0)
            (Pair bounded_case16594_prefix4_root_box (Num 0))))),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> simp [bounded_case16594_prefix4_topology_pure_eval_value]
QED

val _ = export_theory ();
