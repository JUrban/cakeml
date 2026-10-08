(*****************************************************************************
 * Total parser primitives for compact external nonlinear checker data.
 *
 * External packing is untrusted.  These functions read a byte-addressed
 * mlstring with explicit cursors, fail on truncation or malformed flags, and
 * construct only the current checked-word value.  They are independent of a
 * particular Flyspeck expression or certificate verdict.
 *****************************************************************************)
Theory compute_boundedPackedInput
Ancestors
  compute_boundedAnalyticProgram
  compute_boundedCase16594StreamingInputData
  mlstring
Libs
  bossLib preamble wordsLib

Definition bounded_packed_byte_def:
  bounded_packed_byte payload cursor =
    if cursor < strlen payload then
      SOME ((n2w (ORD (strsub payload cursor))):word8)
    else NONE
End

Definition bounded_packed_word64_aux_def:
  bounded_packed_word64_aux payload 0 cursor = (0w,cursor) ∧
  bounded_packed_word64_aux payload (SUC remaining) cursor =
    let byte = (n2w (ORD (strsub payload cursor))):word64;
        suffix = bounded_packed_word64_aux payload remaining (SUC cursor)
    in
      (byte + ((FST suffix) << 8),SND suffix)
End

Definition bounded_packed_word64_def:
  bounded_packed_word64 payload cursor =
    if cursor + 8 ≤ strlen payload then
      SOME (bounded_packed_word64_aux payload 8 cursor)
    else NONE
End

Definition bounded_packed_signed64_value_def:
  bounded_packed_signed64_value payload cursor =
    let sign = ORD (strsub payload cursor);
        magnitude = FST
          (bounded_packed_word64_aux payload 8 (SUC cursor))
    in
      (BoundedSigned64 (sign = 1) magnitude,cursor + 9)
End

Definition bounded_packed_signed64_def:
  bounded_packed_signed64 payload cursor =
    if cursor + 9 ≤ strlen payload ∧ ORD (strsub payload cursor) < 2 then
      SOME (bounded_packed_signed64_value payload cursor)
    else NONE
End

Definition bounded_packed_interval64_def:
  bounded_packed_interval64 payload cursor =
    if cursor + 18 ≤ strlen payload ∧
       ORD (strsub payload cursor) < 2 ∧
       ORD (strsub payload (cursor + 9)) < 2
    then
      let lower = FST (bounded_packed_signed64_value payload cursor);
          upper = FST (bounded_packed_signed64_value payload (cursor + 9))
      in SOME (BoundedInterval64 lower upper,cursor + 18)
    else NONE
End

Definition bounded_packed_interval64_at_def:
  bounded_packed_interval64_at payload cursor =
    BoundedInterval64
      (FST (bounded_packed_signed64_value payload cursor))
      (FST (bounded_packed_signed64_value payload (cursor + 9)))
End

Definition bounded_packed_interval64_zero_def:
  bounded_packed_interval64_zero
      (BoundedInterval64
        (BoundedSigned64 lower_negative lower_magnitude)
        (BoundedSigned64 upper_negative upper_magnitude)) ⇔
    ¬lower_negative ∧ lower_magnitude = 0w ∧
    ¬upper_negative ∧ upper_magnitude = 0w
End

Definition bounded_packed_signs_valid_def:
  (bounded_packed_signs_valid payload 0 cursor = T) ∧
  (bounded_packed_signs_valid payload (SUC remaining) cursor =
    (ORD (strsub payload cursor) < 2 ∧
     bounded_packed_signs_valid payload remaining (cursor + 9)))
End

Definition bounded_packed_analytic64_certificate_def:
  bounded_packed_analytic64_certificate payload cursor =
    if cursor + 92 ≤ strlen payload ∧
       ORD (strsub payload cursor) < 3 ∧
       ORD (strsub payload (cursor + 1)) < 4 ∧
       bounded_packed_signs_valid payload 10 (cursor + 2)
    then
      let tag = ORD (strsub payload cursor);
          flags = ORD (strsub payload (cursor + 1));
          a = bounded_packed_interval64_at payload (cursor + 2);
          b = bounded_packed_interval64_at payload (cursor + 20);
          c = bounded_packed_interval64_at payload (cursor + 38);
          d = bounded_packed_interval64_at payload (cursor + 56);
          e = bounded_packed_interval64_at payload (cursor + 74)
      in
        if tag = 0 then
          if flags = 0 then
            SOME (BoundedAnalytic64SqrtCertificate a b c d e,cursor + 92)
          else NONE
        else if tag = 1 then
          if flags = 0 ∧ bounded_packed_interval64_zero c ∧
             bounded_packed_interval64_zero d ∧
             bounded_packed_interval64_zero e
          then SOME (BoundedAnalytic64InverseCertificate a b,cursor + 92)
          else NONE
        else if bounded_packed_interval64_zero e then
          let lower = if flags = 1 ∨ flags = 3 then SOME a else NONE;
              upper = if flags = 2 ∨ flags = 3 then SOME b else NONE
          in
            if (flags = 1 ∨ flags = 3 ∨ bounded_packed_interval64_zero a) ∧
               (flags = 2 ∨ flags = 3 ∨ bounded_packed_interval64_zero b)
            then SOME (BoundedAnalytic64AtanCertificate lower upper c d,
                       cursor + 92)
            else NONE
        else NONE
    else NONE
End

Definition bounded_packed_analytic64_certificate_list_def:
  bounded_packed_analytic64_certificate_list payload 0 cursor =
      SOME ([],cursor) ∧
  bounded_packed_analytic64_certificate_list payload (SUC remaining) cursor =
    case bounded_packed_analytic64_certificate payload cursor of
    | NONE => NONE
    | SOME (certificate,next) =>
      case bounded_packed_analytic64_certificate_list payload remaining next of
      | NONE => NONE
      | SOME (rest,finish) => SOME (certificate::rest,finish)
End

Definition bounded_packed_positive_interval64_value_def:
  bounded_packed_positive_interval64_value payload cursor =
    let lower = FST (bounded_packed_word64_aux payload 8 cursor);
        upper = FST
          (bounded_packed_word64_aux payload 8 (cursor + 8))
    in
      (BoundedInterval64 (BoundedSigned64 F lower)
        (BoundedSigned64 F upper),cursor + 16)
End

Definition bounded_packed_positive_interval64_def:
  bounded_packed_positive_interval64 payload cursor =
    if cursor + 16 ≤ strlen payload then
      SOME (bounded_packed_positive_interval64_value payload cursor)
    else NONE
End

Definition bounded_packed_positive_interval64_list_aux_def:
  bounded_packed_positive_interval64_list_aux payload 0 cursor =
      ([],cursor) ∧
  bounded_packed_positive_interval64_list_aux payload (SUC remaining) cursor =
    let value = FST
          (bounded_packed_positive_interval64_value payload cursor);
        suffix = bounded_packed_positive_interval64_list_aux payload
          remaining (cursor + 16)
    in
      (value::(FST suffix),SND suffix)
End

Definition bounded_packed_positive_interval64_list_def:
  bounded_packed_positive_interval64_list payload count cursor =
    if cursor + 16 * count ≤ strlen payload then
      SOME (bounded_packed_positive_interval64_list_aux payload count cursor)
    else NONE
End

Definition bounded_packed_word64_list_aux_def:
  bounded_packed_word64_list_aux payload 0 cursor = ([],cursor) ∧
  bounded_packed_word64_list_aux payload (SUC remaining) cursor =
    let value = FST (bounded_packed_word64_aux payload 8 cursor);
        suffix = bounded_packed_word64_list_aux payload remaining (cursor + 8)
    in
      (value::(FST suffix),SND suffix)
End

Definition bounded_packed_word64_list_def:
  bounded_packed_word64_list payload count cursor =
    if cursor + 8 * count ≤ strlen payload then
      SOME (bounded_packed_word64_list_aux payload count cursor)
    else NONE
End

Definition bounded_packed_case16594_input_def:
  bounded_packed_case16594_input payload cursor =
    if cursor + 240 ≤ strlen payload then
      let box_result = bounded_packed_positive_interval64_list_aux payload
            6 cursor;
          center_result = bounded_packed_positive_interval64_list_aux payload
            6 (cursor + 96);
          radius_result = bounded_packed_word64_list_aux payload
            6 (cursor + 192)
      in
        SOME ((FST box_result,FST center_result,FST radius_result),cursor + 240)
    else NONE
End

Definition bounded_packed_case16594_cell_def:
  bounded_packed_case16594_cell payload cursor =
    case bounded_packed_case16594_input payload cursor of
    | NONE => NONE
    | SOME (input,next) =>
      case bounded_packed_analytic64_certificate_list payload 31 next of
      | NONE => NONE
      | SOME (certificates,finish) =>
          SOME ((input,certificates),finish)
End

Definition bounded_packed_case16594_header_def:
  bounded_packed_case16594_header payload =
    if strlen payload < 16 ∨ substring payload 0 8 ≠ «CNLCKR01» then NONE
    else
      let cells = FST (bounded_packed_word64_aux payload 4 8);
          records = FST (bounded_packed_word64_aux payload 4 12)
      in
        if cells = 875w ∧ records = 31w then SOME (16:num) else NONE
End

Theorem bounded_packed_byte_closed_tests:
  bounded_packed_byte (strlit [CHR 7]) 0 = SOME 7w ∧
  bounded_packed_byte (strlit [CHR 7]) 1 = NONE
Proof
  EVAL_TAC
QED

Theorem bounded_packed_word64_little_endian_test:
  bounded_packed_word64
    (strlit [CHR 1;CHR 2;CHR 3;CHR 4;CHR 5;CHR 6;CHR 7;CHR 8]) 0 =
      SOME (578437695752307201w,8)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_packed_header_closed_tests:
  bounded_packed_case16594_header
    («CNLCKR01» ^ strlit [CHR 107;CHR 3;CHR 0;CHR 0;
                          CHR 31;CHR 0;CHR 0;CHR 0]) = SOME 16 ∧
  bounded_packed_case16594_header «CNLCKR01» = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_packed_analytic64_certificate_truncated:
  bounded_packed_analytic64_certificate «» 0 = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
