(*****************************************************************************
 * Canonical compact packet for the complete case-10173 word checker.
 *
 * This is the fail-closed data boundary for the specialized kernel route.
 * Lists use the ordinary cv Pair/Num-0 encoding, booleans are exactly 0/1,
 * and word payloads must be strictly below 2^64.  The packet decoder also
 * enforces every checker-specific list width and rejects trailing fields.
 *****************************************************************************)
Theory compute_boundedCase10173Packet
Ancestors
  compute_boundedCase10173HistoricalCell0Data compute_exec
Libs
  bossLib preamble wordsLib

val _ = numLib.temp_prefer_num ();
val _ = monadsyntax.temp_enable_monad "option";

Datatype:
  bounded_case10173_packet =
    BoundedCase10173Packet
      (word64 list)
      (bounded_interval64 list)
      (bounded_interval64 list)
      (bounded_case10173_sqrt64_certificate list)
      bounded_interval64
      bounded_interval64
      (bounded_interval64 list)
      bounded_interval64
      bounded_interval64
      (bounded_interval64 list)
End

Definition bounded_cv_encode_word64_def:
  bounded_cv_encode_word64 (word:word64) : cv = Num (w2n word)
End

Definition bounded_cv_decode_word64_def:
  bounded_cv_decode_word64 (Num n : cv) =
    (if n < bounded_word_base then SOME ((n2w n):word64) else NONE) /\
  bounded_cv_decode_word64 _ = NONE
End

Definition bounded_cv_encode_bool_def:
  bounded_cv_encode_bool value : cv = Num (if value then 1 else 0)
End

Definition bounded_cv_decode_bool_def:
  bounded_cv_decode_bool (Num 0 : cv) = SOME F /\
  bounded_cv_decode_bool (Num 1 : cv) = SOME T /\
  bounded_cv_decode_bool _ = NONE
End

Definition bounded_cv_encode_signed64_def:
  bounded_cv_encode_signed64 (BoundedSigned64 negative magnitude) : cv =
    Pair (bounded_cv_encode_bool negative)
      (bounded_cv_encode_word64 magnitude)
End

Definition bounded_cv_decode_signed64_def:
  bounded_cv_decode_signed64 (Pair negative magnitude : cv) =
    do
      negative' <- bounded_cv_decode_bool negative;
      magnitude' <- bounded_cv_decode_word64 magnitude;
      return (BoundedSigned64 negative' magnitude')
    od /\
  bounded_cv_decode_signed64 _ = NONE
End

Definition bounded_cv_encode_interval64_def:
  bounded_cv_encode_interval64 (BoundedInterval64 lower upper) : cv =
    Pair (bounded_cv_encode_signed64 lower)
      (bounded_cv_encode_signed64 upper)
End

Definition bounded_cv_decode_interval64_def:
  bounded_cv_decode_interval64 (Pair lower upper : cv) =
    do
      lower' <- bounded_cv_decode_signed64 lower;
      upper' <- bounded_cv_decode_signed64 upper;
      return (BoundedInterval64 lower' upper')
    od /\
  bounded_cv_decode_interval64 _ = NONE
End

Definition bounded_cv_encode_word64_list_def:
  bounded_cv_encode_word64_list [] = (Num 0 : cv) /\
  bounded_cv_encode_word64_list (word::words) =
    Pair (bounded_cv_encode_word64 word)
      (bounded_cv_encode_word64_list words)
End

Definition bounded_cv_decode_word64_list_def:
  bounded_cv_decode_word64_list (Num 0 : cv) = SOME [] /\
  bounded_cv_decode_word64_list (Pair word words) =
    do
      word' <- bounded_cv_decode_word64 word;
      words' <- bounded_cv_decode_word64_list words;
      return (word'::words')
    od /\
  bounded_cv_decode_word64_list _ = NONE
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Definition bounded_cv_encode_interval64_list_def:
  bounded_cv_encode_interval64_list [] = (Num 0 : cv) /\
  bounded_cv_encode_interval64_list (interval::intervals) =
    Pair (bounded_cv_encode_interval64 interval)
      (bounded_cv_encode_interval64_list intervals)
End

Definition bounded_cv_decode_interval64_list_def:
  bounded_cv_decode_interval64_list (Num 0 : cv) = SOME [] /\
  bounded_cv_decode_interval64_list (Pair interval intervals) =
    do
      interval' <- bounded_cv_decode_interval64 interval;
      intervals' <- bounded_cv_decode_interval64_list intervals;
      return (interval'::intervals')
    od /\
  bounded_cv_decode_interval64_list _ = NONE
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Definition bounded_cv_encode_sqrt64_certificate_def:
  bounded_cv_encode_sqrt64_certificate
      (BoundedCase10173Sqrt64Certificate center_root box_root
        center_derivative box_derivative second_derivative) : cv =
    Pair (bounded_cv_encode_interval64 center_root)
      (Pair (bounded_cv_encode_interval64 box_root)
        (Pair (bounded_cv_encode_interval64 center_derivative)
          (Pair (bounded_cv_encode_interval64 box_derivative)
            (Pair (bounded_cv_encode_interval64 second_derivative)
              (Num 0)))))
End

Definition bounded_cv_decode_sqrt64_certificate_def:
  bounded_cv_decode_sqrt64_certificate
      (Pair center_root
        (Pair box_root
          (Pair center_derivative
            (Pair box_derivative
              (Pair second_derivative (Num 0))))) : cv) =
    do
      center_root' <- bounded_cv_decode_interval64 center_root;
      box_root' <- bounded_cv_decode_interval64 box_root;
      center_derivative' <- bounded_cv_decode_interval64 center_derivative;
      box_derivative' <- bounded_cv_decode_interval64 box_derivative;
      second_derivative' <- bounded_cv_decode_interval64 second_derivative;
      return (BoundedCase10173Sqrt64Certificate
        center_root' box_root' center_derivative' box_derivative'
        second_derivative')
    od /\
  bounded_cv_decode_sqrt64_certificate _ = NONE
End

Definition bounded_cv_encode_sqrt64_certificate_list_def:
  bounded_cv_encode_sqrt64_certificate_list [] = (Num 0 : cv) /\
  bounded_cv_encode_sqrt64_certificate_list (certificate::certificates) =
    Pair (bounded_cv_encode_sqrt64_certificate certificate)
      (bounded_cv_encode_sqrt64_certificate_list certificates)
End

Definition bounded_cv_decode_sqrt64_certificate_list_def:
  bounded_cv_decode_sqrt64_certificate_list (Num 0 : cv) = SOME [] /\
  bounded_cv_decode_sqrt64_certificate_list (Pair certificate certificates) =
    do
      certificate' <- bounded_cv_decode_sqrt64_certificate certificate;
      certificates' <- bounded_cv_decode_sqrt64_certificate_list certificates;
      return (certificate'::certificates')
    od /\
  bounded_cv_decode_sqrt64_certificate_list _ = NONE
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Definition bounded_case10173_packet_well_shaped_def:
  bounded_case10173_packet_well_shaped
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) <=>
    LENGTH radii = 6 /\
    LENGTH center_environment = 6 /\
    LENGTH box_environment = 6 /\
    LENGTH coordinate_sqrt_certificates = 6 /\
    LENGTH center_reciprocals = 5 /\
    LENGTH box_reciprocals = 9
End

Definition bounded_cv_encode_case10173_packet_def:
  bounded_cv_encode_case10173_packet
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) : cv =
    Pair (bounded_cv_encode_word64_list radii)
      (Pair (bounded_cv_encode_interval64_list center_environment)
        (Pair (bounded_cv_encode_interval64_list box_environment)
          (Pair (bounded_cv_encode_sqrt64_certificate_list
                   coordinate_sqrt_certificates)
            (Pair (bounded_cv_encode_interval64 center_root_delta)
              (Pair (bounded_cv_encode_interval64 center_root_four_x0)
                (Pair (bounded_cv_encode_interval64_list center_reciprocals)
                  (Pair (bounded_cv_encode_interval64 box_root_delta)
                    (Pair (bounded_cv_encode_interval64 box_root_four_x0)
                      (Pair (bounded_cv_encode_interval64_list box_reciprocals)
                        (Num 0))))))))))
End

Definition bounded_cv_decode_case10173_packet_def:
  bounded_cv_decode_case10173_packet
      (Pair radii
        (Pair center_environment
          (Pair box_environment
            (Pair coordinate_sqrt_certificates
              (Pair center_root_delta
                (Pair center_root_four_x0
                  (Pair center_reciprocals
                    (Pair box_root_delta
                      (Pair box_root_four_x0
                        (Pair box_reciprocals (Num 0)))))))))) : cv) =
    do
      radii' <- bounded_cv_decode_word64_list radii;
      center_environment' <-
        bounded_cv_decode_interval64_list center_environment;
      box_environment' <- bounded_cv_decode_interval64_list box_environment;
      coordinate_sqrt_certificates' <-
        bounded_cv_decode_sqrt64_certificate_list
          coordinate_sqrt_certificates;
      center_root_delta' <-
        bounded_cv_decode_interval64 center_root_delta;
      center_root_four_x0' <-
        bounded_cv_decode_interval64 center_root_four_x0;
      center_reciprocals' <-
        bounded_cv_decode_interval64_list center_reciprocals;
      box_root_delta' <- bounded_cv_decode_interval64 box_root_delta;
      box_root_four_x0' <- bounded_cv_decode_interval64 box_root_four_x0;
      box_reciprocals' <-
        bounded_cv_decode_interval64_list box_reciprocals;
      let packet = BoundedCase10173Packet radii' center_environment'
        box_environment' coordinate_sqrt_certificates' center_root_delta'
        center_root_four_x0' center_reciprocals' box_root_delta'
        box_root_four_x0' box_reciprocals' in
      if bounded_case10173_packet_well_shaped packet
      then return packet
      else NONE
    od /\
  bounded_cv_decode_case10173_packet _ = NONE
End

Definition bounded_case10173_packet_accepts_def:
  bounded_case10173_packet_accepts
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) <=>
    bounded_case10173_checked_cell_accepts radii center_environment
      box_environment coordinate_sqrt_certificates center_root_delta
      center_root_four_x0 center_reciprocals box_root_delta box_root_four_x0
      box_reciprocals
End

(*
 * Executable production boundary: reject a malformed packet before any
 * numerical work, otherwise return one canonical cv boolean for the complete
 * checker verdict.  The generic theorem bridge can consume this result
 * without re-running the numerical evaluator.
 *)
Definition bounded_case10173_packet_check_cv_def:
  bounded_case10173_packet_check_cv payload =
    case bounded_cv_decode_case10173_packet payload of
    | NONE => NONE
    | SOME packet =>
        SOME (bounded_cv_encode_bool
          (bounded_case10173_packet_accepts packet))
End

Definition bounded_case10173_cell0_packet_def:
  bounded_case10173_cell0_packet =
    BoundedCase10173Packet
      bounded_case10173_cell0_radii
      bounded_case10173_cell0_center_environment
      bounded_case10173_cell0_box_environment
      bounded_case10173_cell0_sqrt_certificates
      bounded_case10173_cell0_center_root_delta
      bounded_case10173_cell0_center_root_four_x0
      bounded_case10173_cell0_center_reciprocals
      bounded_case10173_cell0_box_root_delta
      bounded_case10173_cell0_box_root_four_x0
      bounded_case10173_cell0_box_reciprocals
End

Theorem bounded_cv_decode_word64_encode[simp]:
  bounded_cv_decode_word64 (bounded_cv_encode_word64 word) = SOME word
Proof
  rw [bounded_cv_decode_word64_def, bounded_cv_encode_word64_def]
  >> qspec_then `word` assume_tac wordsTheory.w2n_lt
  >> fs [compute_boundedTheory.bounded_word_base_def,
         wordsTheory.dimword_64, wordsTheory.n2w_w2n]
QED

Theorem bounded_cv_decode_bool_encode[simp]:
  bounded_cv_decode_bool (bounded_cv_encode_bool value) = SOME value
Proof
  Cases_on `value` >> simp [bounded_cv_decode_bool_def,
                            bounded_cv_encode_bool_def]
QED

Theorem bounded_cv_decode_signed64_encode[simp]:
  bounded_cv_decode_signed64 (bounded_cv_encode_signed64 value) = SOME value
Proof
  Cases_on `value`
  >> simp [bounded_cv_decode_signed64_def, bounded_cv_encode_signed64_def]
QED

Theorem bounded_cv_decode_interval64_encode[simp]:
  bounded_cv_decode_interval64 (bounded_cv_encode_interval64 value) =
    SOME value
Proof
  Cases_on `value`
  >> simp [bounded_cv_decode_interval64_def,
           bounded_cv_encode_interval64_def]
QED

Theorem bounded_cv_decode_word64_list_encode[simp]:
  !words.
    bounded_cv_decode_word64_list (bounded_cv_encode_word64_list words) =
      SOME words
Proof
  Induct >> simp [bounded_cv_decode_word64_list_def,
                   bounded_cv_encode_word64_list_def]
QED

Theorem bounded_cv_decode_interval64_list_encode[simp]:
  !intervals.
    bounded_cv_decode_interval64_list
      (bounded_cv_encode_interval64_list intervals) = SOME intervals
Proof
  Induct >> simp [bounded_cv_decode_interval64_list_def,
                   bounded_cv_encode_interval64_list_def]
QED

Theorem bounded_cv_decode_sqrt64_certificate_encode[simp]:
  bounded_cv_decode_sqrt64_certificate
      (bounded_cv_encode_sqrt64_certificate certificate) = SOME certificate
Proof
  Cases_on `certificate`
  >> simp [bounded_cv_decode_sqrt64_certificate_def,
           bounded_cv_encode_sqrt64_certificate_def]
QED

Theorem bounded_cv_decode_sqrt64_certificate_list_encode[simp]:
  !certificates.
    bounded_cv_decode_sqrt64_certificate_list
      (bounded_cv_encode_sqrt64_certificate_list certificates) =
        SOME certificates
Proof
  Induct
  >> simp [bounded_cv_decode_sqrt64_certificate_list_def,
           bounded_cv_encode_sqrt64_certificate_list_def]
QED

Theorem bounded_cv_decode_case10173_packet_encode:
  bounded_case10173_packet_well_shaped packet ==>
  bounded_cv_decode_case10173_packet
      (bounded_cv_encode_case10173_packet packet) = SOME packet
Proof
  Cases_on `packet`
  >> simp [bounded_cv_decode_case10173_packet_def,
           bounded_cv_encode_case10173_packet_def,
           bounded_case10173_packet_well_shaped_def]
QED

Theorem bounded_cv_decode_case10173_packet_encode_exact:
  bounded_cv_decode_case10173_packet
      (bounded_cv_encode_case10173_packet packet) =
    if bounded_case10173_packet_well_shaped packet
    then SOME packet
    else NONE
Proof
  Cases_on `packet`
  >> simp [bounded_cv_decode_case10173_packet_def,
           bounded_cv_encode_case10173_packet_def,
           bounded_case10173_packet_well_shaped_def]
QED

Theorem bounded_cv_decode_case10173_packet_rejects_bad_widths:
  ~bounded_case10173_packet_well_shaped packet ==>
  bounded_cv_decode_case10173_packet
      (bounded_cv_encode_case10173_packet packet) = NONE
Proof
  simp [bounded_cv_decode_case10173_packet_encode_exact]
QED

Theorem bounded_cv_decode_word64_rejects_overflow:
  bounded_word_base <= n ==>
  bounded_cv_decode_word64 (Num n) = NONE
Proof
  simp [bounded_cv_decode_word64_def]
QED

Theorem bounded_cv_decode_bool_rejects_noncanonical:
  n <> 0 /\ n <> 1 ==>
  bounded_cv_decode_bool (Num n) = NONE
Proof
  Cases_on `n` >> simp [bounded_cv_decode_bool_def]
  >> Cases_on `n` >> simp [bounded_cv_decode_bool_def]
QED

Theorem bounded_cv_decode_case10173_packet_rejects_outer_trailing:
  bounded_cv_decode_case10173_packet
      (Pair (bounded_cv_encode_case10173_packet packet) (Num 0)) = NONE
Proof
  Cases_on `packet`
  >> simp [bounded_cv_decode_case10173_packet_def,
           bounded_cv_encode_case10173_packet_def]
QED

Theorem bounded_cv_decode_case10173_packet_rejects_nonpacket:
  bounded_cv_decode_case10173_packet (Num n) = NONE
Proof
  simp [bounded_cv_decode_case10173_packet_def]
QED

Theorem bounded_case10173_packet_check_cv_rejects_bad_widths:
  ~bounded_case10173_packet_well_shaped packet ==>
  bounded_case10173_packet_check_cv
      (bounded_cv_encode_case10173_packet packet) = NONE
Proof
  simp [bounded_case10173_packet_check_cv_def,
        bounded_cv_decode_case10173_packet_encode_exact]
QED

Theorem bounded_case10173_packet_check_cv_rejects_outer_trailing:
  bounded_case10173_packet_check_cv
      (Pair (bounded_cv_encode_case10173_packet packet) (Num 0)) = NONE
Proof
  simp [bounded_case10173_packet_check_cv_def,
        bounded_cv_decode_case10173_packet_rejects_outer_trailing]
QED

Theorem bounded_case10173_packet_check_cv_rejects_nonpacket:
  bounded_case10173_packet_check_cv (Num n) = NONE
Proof
  simp [bounded_case10173_packet_check_cv_def,
        bounded_cv_decode_case10173_packet_rejects_nonpacket]
QED

Theorem bounded_case10173_cell0_packet_well_shaped:
  bounded_case10173_packet_well_shaped bounded_case10173_cell0_packet
Proof
  simp [bounded_case10173_cell0_packet_def,
        bounded_case10173_packet_well_shaped_def,
        bounded_case10173_cell0_radii_def,
        bounded_case10173_cell0_center_environment_def,
        bounded_case10173_cell0_box_environment_def,
        bounded_case10173_cell0_sqrt_certificates_def,
        bounded_case10173_cell0_center_reciprocals_def,
        bounded_case10173_cell0_box_reciprocals_def]
QED

Theorem bounded_case10173_cell0_packet_decode:
  bounded_cv_decode_case10173_packet
      (bounded_cv_encode_case10173_packet bounded_case10173_cell0_packet) =
    SOME bounded_case10173_cell0_packet
Proof
  irule bounded_cv_decode_case10173_packet_encode
  >> simp [bounded_case10173_cell0_packet_well_shaped]
QED

Theorem bounded_case10173_cell0_packet_accepts:
  bounded_case10173_packet_accepts bounded_case10173_cell0_packet
Proof
  rw [bounded_case10173_packet_accepts_def,
      bounded_case10173_cell0_packet_def]
  >> mp_tac
       compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_check_value
  >> simp [compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_check_def]
QED

Theorem bounded_case10173_cell0_packet_check_cv:
  bounded_case10173_packet_check_cv
      (bounded_cv_encode_case10173_packet bounded_case10173_cell0_packet) =
    SOME (Num 1)
Proof
  simp [bounded_case10173_packet_check_cv_def,
        bounded_case10173_cell0_packet_decode,
        bounded_case10173_cell0_packet_accepts,
        bounded_cv_encode_bool_def]
QED

val _ = export_theory ();
