(*****************************************************************************
 * Production-evaluator acceptance of all five authenticated certificates for
 * the first genuine case-16594 square-root instruction.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSqrtCertificateRuntimeEval
Ancestors
  compute_boundedCase16594ObjectInverseCertificateExactEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_sqrt_center_root_certificate_eval:
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [from_cv
          (bounded_object_q_taylor_center
            bounded_case16594_object_source5_result);
         from_cv bounded_case16594_object_cell0_sqrt_center_root_cv])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectSqrtCertificateExactEvalTheory.bounded_case16594_object_q_interval_sqrt_certificate_exact_eval
  >> simp
       [compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_center_root_exact]
QED

Theorem bounded_case16594_object_sqrt_center_derivative_certificate_eval:
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [from_cv
          (bounded_object_q_interval_add_cv
            bounded_case16594_object_cell0_sqrt_center_root_cv
            bounded_case16594_object_cell0_sqrt_center_root_cv);
         from_cv
           bounded_case16594_object_cell0_sqrt_center_derivative_cv])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectInverseCertificateExactEvalTheory.bounded_case16594_object_q_interval_inv_certificate_exact_eval
  >> simp
       [compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_center_derivative_exact]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_sqrt_box_root_certificate_eval:
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [from_cv
          (bounded_object_q_taylor_value_bound
            bounded_case16594_object_source5_result);
         from_cv bounded_case16594_object_cell0_sqrt_box_root_cv])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectSqrtCertificateExactEvalTheory.bounded_case16594_object_q_interval_sqrt_certificate_exact_eval
  >> simp
       [compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_box_root_exact]
QED

Theorem bounded_case16594_object_sqrt_box_derivative_certificate_eval:
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [from_cv
          (bounded_object_q_interval_add_cv
            bounded_case16594_object_cell0_sqrt_box_root_cv
            bounded_case16594_object_cell0_sqrt_box_root_cv);
         from_cv bounded_case16594_object_cell0_sqrt_box_derivative_cv])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectInverseCertificateExactEvalTheory.bounded_case16594_object_q_interval_inv_certificate_exact_eval
  >> simp
       [compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_box_derivative_exact]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_sqrt_box_second_certificate_eval:
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [from_cv
          (bounded_object_q_interval_mul_cv
            (bounded_object_q_interval_add_cv
              bounded_case16594_object_cell0_sqrt_box_root_cv
              bounded_case16594_object_cell0_sqrt_box_root_cv)
            (bounded_object_q_interval_add_cv
              (bounded_object_q_taylor_value_bound
                bounded_case16594_object_source5_result)
              (bounded_object_q_taylor_value_bound
                bounded_case16594_object_source5_result)));
         from_cv
           bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectInverseCertificateExactEvalTheory.bounded_case16594_object_q_interval_inv_certificate_exact_eval
  >> simp
       [compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_box_second_reciprocal_exact]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_sqrt_certificate_packet_eval:
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [from_cv
          (bounded_object_q_taylor_center
            bounded_case16594_object_source5_result);
         from_cv bounded_case16594_object_cell0_sqrt_center_root_cv])
      (refs:hol_refs) = (M_success (Num 1),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [from_cv
          (bounded_object_q_interval_add_cv
            bounded_case16594_object_cell0_sqrt_center_root_cv
            bounded_case16594_object_cell0_sqrt_center_root_cv);
         from_cv
           bounded_case16594_object_cell0_sqrt_center_derivative_cv])
      refs = (M_success (Num 1),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [from_cv
          (bounded_object_q_taylor_value_bound
            bounded_case16594_object_source5_result);
         from_cv bounded_case16594_object_cell0_sqrt_box_root_cv])
      refs = (M_success (Num 1),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [from_cv
          (bounded_object_q_interval_add_cv
            bounded_case16594_object_cell0_sqrt_box_root_cv
            bounded_case16594_object_cell0_sqrt_box_root_cv);
         from_cv bounded_case16594_object_cell0_sqrt_box_derivative_cv])
      refs = (M_success (Num 1),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [from_cv
          (bounded_object_q_interval_mul_cv
            (bounded_object_q_interval_add_cv
              bounded_case16594_object_cell0_sqrt_box_root_cv
              bounded_case16594_object_cell0_sqrt_box_root_cv)
            (bounded_object_q_interval_add_cv
              (bounded_object_q_taylor_value_bound
                bounded_case16594_object_source5_result)
              (bounded_object_q_taylor_value_bound
                bounded_case16594_object_source5_result)));
         from_cv
           bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv])
      refs = (M_success (Num 1),refs)
Proof
  simp
    [bounded_case16594_object_sqrt_center_root_certificate_eval,
     bounded_case16594_object_sqrt_center_derivative_certificate_eval,
     bounded_case16594_object_sqrt_box_root_certificate_eval,
     bounded_case16594_object_sqrt_box_derivative_certificate_eval,
     bounded_case16594_object_sqrt_box_second_certificate_eval]
QED

val _ = export_theory ();
