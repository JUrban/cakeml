(*****************************************************************************
 * Proof-producing evaluation of the genuine case-16594 center q-atan
 * certificate.
 *
 * The closed pure evaluation is intentionally kept as a reusable theorem.
 * Its refinement theorem then lifts the result to the stateful production
 * evaluator without repeating the transcendental certificate computation.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanCertificateEval
Ancestors
  compute_boundedCase16594ObjectAtanCertificateContract
  compute_boundedCase16594ObjectFirstNegEval
  compute_evalPure
Libs
  bossLib preamble cv_transLib

val _ = cv_trans
  compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_input_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_result_cv_def;

val bounded_case16594_object_atan_center_inner_certificate_pure_eval =
  time cv_eval
    ``compute_eval_pure 4096 bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_interval_atn_certificate»
          [from_cv bounded_case16594_object_cell0_atan_center_input_cv;
           from_cv bounded_case16594_object_cell0_atan_center_result_cv])``;

val _ = save_thm
  ("bounded_case16594_object_atan_center_inner_certificate_pure_eval",
   bounded_case16594_object_atan_center_inner_certificate_pure_eval);

Theorem bounded_case16594_object_atan_center_inner_certificate_eval:
  4096 <= clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_atn_certificate»
        [from_cv bounded_case16594_object_cell0_atan_center_input_cv;
         from_cv bounded_case16594_object_cell0_atan_center_result_cv])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `4096`
  >> asm_rewrite_tac
       [bounded_case16594_object_atan_center_inner_certificate_pure_eval]
QED

val _ = export_theory ();
