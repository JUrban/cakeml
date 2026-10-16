(*****************************************************************************
 * Canonical raw-job consequence of the authenticated decimal stream.
 *
 * The historical raw wrapper first checks that every rational job is in the
 * canonical cval image.  The authenticated decimal checker already accepts
 * only the stricter positive-rational representation.  This theory records
 * the resulting canonicality explicitly, so the fast-evaluator refinement
 * does not need to assume or re-check it outside the authenticated stream.
 *****************************************************************************)
Theory compute_boundedCase10173ObjectJobCanonical
Ancestors
  compute_boundedCase10173PackedDecimalAuthenticated
Libs
  bossLib preamble

Definition bounded_object_lc_num_canonical_def:
  bounded_object_lc_num_canonical (Num n : cv) = Num n /\
  bounded_object_lc_num_canonical (Pair x y) = Num 0
End

Definition bounded_object_lc_z_canonical_def:
  bounded_object_lc_z_canonical (Num n : cv) = Pair (Num 0) (Num 0) /\
  bounded_object_lc_z_canonical (Pair x y) =
    Pair (bounded_object_lc_num_canonical x)
      (bounded_object_lc_num_canonical y)
End

Definition bounded_object_q_canonical_def:
  bounded_object_q_canonical (Num n : cv) =
    Pair (Pair (Num 0) (Num 0)) (Num 0) /\
  bounded_object_q_canonical (Pair z d) =
    Pair (bounded_object_lc_z_canonical z)
      (bounded_object_lc_num_canonical d)
End

Definition bounded_object_q_interval_canonical_def:
  bounded_object_q_interval_canonical (Num n : cv) =
    Pair (Pair (Pair (Num 0) (Num 0)) (Num 0))
      (Pair (Pair (Num 0) (Num 0)) (Num 0)) /\
  bounded_object_q_interval_canonical (Pair lower upper) =
    Pair (bounded_object_q_canonical lower)
      (bounded_object_q_canonical upper)
End

Definition bounded_object_q_interval_list_canonical_def:
  bounded_object_q_interval_list_canonical (Num n : cv) = Num 0 /\
  bounded_object_q_interval_list_canonical (Pair interval intervals) =
    Pair (bounded_object_q_interval_canonical interval)
      (bounded_object_q_interval_list_canonical intervals)
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Definition bounded_object_cv_fst_def:
  bounded_object_cv_fst (Pair x y : cv) = x /\
  bounded_object_cv_fst (Num n) = Num 0
End

Definition bounded_object_cv_snd_def:
  bounded_object_cv_snd (Pair x y : cv) = y /\
  bounded_object_cv_snd (Num n) = Num 0
End

Definition bounded_object_fso_variable_job_canonical_def:
  bounded_object_fso_variable_job_canonical encoded =
    Pair
      (bounded_object_q_interval_list_canonical
        (bounded_object_cv_fst encoded))
      (Pair
        (bounded_object_q_interval_list_canonical
          (bounded_object_cv_fst (bounded_object_cv_snd encoded)))
        (bounded_object_q_interval_list_canonical
          (bounded_object_cv_snd (bounded_object_cv_snd encoded))))
End

Definition bounded_object_fso_variable_jobs_canonical_def:
  bounded_object_fso_variable_jobs_canonical (Num n : cv) = Num 0 /\
  bounded_object_fso_variable_jobs_canonical (Pair object_job object_jobs) =
    Pair (bounded_object_fso_variable_job_canonical object_job)
      (bounded_object_fso_variable_jobs_canonical object_jobs)
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Theorem bounded_object_positive_q_floor64_decimal_canonical:
  bounded_object_positive_q_floor64_decimal encoded = SOME result ==>
  bounded_object_q_canonical encoded = encoded
Proof
  Cases_on `encoded`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c0'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `n'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c0`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def,
        bounded_object_q_canonical_def,
        bounded_object_lc_z_canonical_def,
        bounded_object_lc_num_canonical_def]
QED

Theorem bounded_object_positive_q_ceil64_decimal_canonical:
  bounded_object_positive_q_ceil64_decimal encoded = SOME result ==>
  bounded_object_q_canonical encoded = encoded
Proof
  Cases_on `encoded`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c0'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `n'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c0`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def,
        bounded_object_q_canonical_def,
        bounded_object_lc_z_canonical_def,
        bounded_object_lc_num_canonical_def]
QED

Theorem bounded_object_positive_q_interval64_decimal_canonical:
  bounded_object_positive_q_interval64_decimal encoded = SOME interval ==>
  bounded_object_q_interval_canonical encoded = encoded
Proof
  Cases_on `encoded`
  >> rw
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_positive_q_floor64_decimal_canonical
  >> imp_res_tac bounded_object_positive_q_ceil64_decimal_canonical
  >> gvs [bounded_object_q_interval_canonical_def]
QED

Theorem bounded_object_positive_q_interval64_decimal_list_canonical:
  !encoded intervals.
    bounded_object_positive_q_interval64_decimal_list encoded =
      SOME intervals ==>
    bounded_object_q_interval_list_canonical encoded = encoded
Proof
  ho_match_mp_tac
    compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_ind
  >> rw
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_def,
        bounded_object_q_interval_list_canonical_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_positive_q_interval64_decimal_canonical
  >> res_tac
  >> gvs []
QED

Theorem bounded_case10173_decimal_packet_exact_input_job_canonical:
  bounded_case10173_decimal_packet_exact_input_binding packet object_job
      root_record ==>
  bounded_object_fso_variable_job_canonical object_job = object_job
Proof
  rw
    [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_input_binding_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_auxiliary_binding_def]
  >> drule
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_box_exact_components
  >> strip_tac
  >> drule
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_binding_components
  >> strip_tac
  >> imp_res_tac
       bounded_object_positive_q_interval64_decimal_list_canonical
  >> gvs
       [bounded_object_fso_variable_job_canonical_def,
        bounded_object_cv_fst_def,
        bounded_object_cv_snd_def]
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_jobs_canonical:
  !remaining bytes encoded_jobs encoded_roots count result.
    bounded_packed_chars_case10173_decimal_authenticated_packets
      remaining bytes encoded_jobs encoded_roots count = SOME result ==>
    bounded_object_fso_variable_jobs_canonical encoded_jobs = encoded_jobs
Proof
  Induct
  >- (Cases_on `encoded_jobs`
      >> Cases_on `encoded_roots`
      >> rw
           [compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_packets_def,
            bounded_object_fso_variable_jobs_canonical_def]
      >> gvs [])
  >> Cases_on `encoded_jobs`
  >> Cases_on `encoded_roots`
  >> rw
       [compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_packets_def,
        bounded_object_fso_variable_jobs_canonical_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_case10173_decimal_packet_exact_input_job_canonical
  >> res_tac
  >> gvs []
QED

Theorem bounded_packed_chars_case10173_decimal_authenticated_full_jobs_canonical:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs encoded_roots ==>
  bounded_object_fso_variable_jobs_canonical encoded_jobs = encoded_jobs
Proof
  rw
    [compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_full_check_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_packed_chars_case10173_decimal_authenticated_jobs_canonical
QED

val _ = export_theory ();
