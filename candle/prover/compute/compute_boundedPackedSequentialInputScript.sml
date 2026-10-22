(*****************************************************************************
 * Sequential parser for compact external nonlinear checker data.
 *
 * The cursor/mlstring parser is a simple specification path, but repeated
 * strsub is linear in the cursor because mlstring is backed by a character
 * list.  These functions consume that list once, left to right.
 *****************************************************************************)
Theory compute_boundedPackedSequentialInput
Ancestors
  compute_boundedPackedInput
Libs
  bossLib preamble wordsLib

Definition bounded_packed_chars_word64_aux_def:
  bounded_packed_chars_word64_aux 0 bytes = SOME (0w,bytes) ∧
  bounded_packed_chars_word64_aux (SUC remaining) bytes =
    case bytes of
    | [] => NONE
    | byte::rest =>
      case bounded_packed_chars_word64_aux remaining rest of
      | NONE => NONE
      | SOME (suffix,finish) =>
          SOME (((n2w (ORD byte)):word64) + (suffix << 8),finish)
End

Definition bounded_packed_chars_signed64_def:
  bounded_packed_chars_signed64 bytes =
    case bytes of
    | [] => NONE
    | sign::rest =>
      if ORD sign < 2 then
        case bounded_packed_chars_word64_aux 8 rest of
        | NONE => NONE
        | SOME (magnitude,finish) =>
            SOME (BoundedSigned64 (ORD sign = 1) magnitude,finish)
      else NONE
End

Definition bounded_packed_chars_interval64_def:
  bounded_packed_chars_interval64 bytes =
    case bounded_packed_chars_signed64 bytes of
    | NONE => NONE
    | SOME (lower,rest) =>
      case bounded_packed_chars_signed64 rest of
      | NONE => NONE
      | SOME (upper,finish) =>
          SOME (BoundedInterval64 lower upper,finish)
End

Definition bounded_packed_chars_positive_interval64_def:
  bounded_packed_chars_positive_interval64 bytes =
    case bounded_packed_chars_word64_aux 8 bytes of
    | NONE => NONE
    | SOME (lower,rest) =>
      case bounded_packed_chars_word64_aux 8 rest of
      | NONE => NONE
      | SOME (upper,finish) =>
          SOME (BoundedInterval64 (BoundedSigned64 F lower)
            (BoundedSigned64 F upper),finish)
End

Definition bounded_packed_chars_positive_interval64_list_def:
  bounded_packed_chars_positive_interval64_list 0 bytes = SOME ([],bytes) ∧
  bounded_packed_chars_positive_interval64_list (SUC remaining) bytes =
    case bounded_packed_chars_positive_interval64 bytes of
    | NONE => NONE
    | SOME (value,rest) =>
      case bounded_packed_chars_positive_interval64_list remaining rest of
      | NONE => NONE
      | SOME (suffix,finish) => SOME (value::suffix,finish)
End

Definition bounded_packed_chars_word64_list_def:
  bounded_packed_chars_word64_list 0 bytes = SOME ([],bytes) ∧
  bounded_packed_chars_word64_list (SUC remaining) bytes =
    case bounded_packed_chars_word64_aux 8 bytes of
    | NONE => NONE
    | SOME (value,rest) =>
      case bounded_packed_chars_word64_list remaining rest of
      | NONE => NONE
      | SOME (suffix,finish) => SOME (value::suffix,finish)
End

Definition bounded_packed_chars_signed64_list_def:
  bounded_packed_chars_signed64_list 0 bytes = SOME ([],bytes) ∧
  bounded_packed_chars_signed64_list (SUC remaining) bytes =
    case bounded_packed_chars_signed64 bytes of
    | NONE => NONE
    | SOME (value,rest) =>
      case bounded_packed_chars_signed64_list remaining rest of
      | NONE => NONE
      | SOME (suffix,finish) => SOME (value::suffix,finish)
End

Definition bounded_packed_chars_case16594_input_def:
  bounded_packed_chars_case16594_input bytes =
    case bounded_packed_chars_positive_interval64_list 6 bytes of
    | NONE => NONE
    | SOME (box,rest1) =>
      case bounded_packed_chars_positive_interval64_list 6 rest1 of
      | NONE => NONE
      | SOME (center,rest2) =>
        case bounded_packed_chars_word64_list 6 rest2 of
        | NONE => NONE
        | SOME (radii,finish) => SOME ((box,center,radii),finish)
End

Definition bounded_packed_chars_analytic64_certificate_def:
  bounded_packed_chars_analytic64_certificate bytes =
    case bytes of
    | tag_char::flags_char::rest =>
      let tag = ORD tag_char;
          flags = ORD flags_char
      in
        if tag < 3 ∧ flags < 4 then
          case bounded_packed_chars_signed64_list 10 rest of
          | SOME ([a0;a1;b0;b1;c0;c1;d0;d1;e0;e1],finish) =>
            let a = BoundedInterval64 a0 a1;
                b = BoundedInterval64 b0 b1;
                c = BoundedInterval64 c0 c1;
                d = BoundedInterval64 d0 d1;
                e = BoundedInterval64 e0 e1
            in
              if tag = 0 then
                if flags = 0 then
                  SOME (BoundedAnalytic64SqrtCertificate a b c d e,finish)
                else NONE
              else if tag = 1 then
                if flags = 0 ∧ bounded_packed_interval64_zero c ∧
                   bounded_packed_interval64_zero d ∧
                   bounded_packed_interval64_zero e
                then SOME (BoundedAnalytic64InverseCertificate a b,finish)
                else NONE
              else if bounded_packed_interval64_zero e then
                let lower = if flags = 1 ∨ flags = 3 then SOME a else NONE;
                    upper = if flags = 2 ∨ flags = 3 then SOME b else NONE
                in
                  if (flags = 1 ∨ flags = 3 ∨
                        bounded_packed_interval64_zero a) ∧
                     (flags = 2 ∨ flags = 3 ∨
                        bounded_packed_interval64_zero b)
                  then SOME (BoundedAnalytic64AtanCertificate
                    lower upper c d,finish)
                  else NONE
              else NONE
          | _ => NONE
        else NONE
    | _ => NONE
End

Definition bounded_packed_chars_analytic64_certificate_list_def:
  bounded_packed_chars_analytic64_certificate_list 0 bytes =
      SOME ([],bytes) ∧
  bounded_packed_chars_analytic64_certificate_list (SUC remaining) bytes =
    case bounded_packed_chars_analytic64_certificate bytes of
    | NONE => NONE
    | SOME (certificate,rest) =>
      case bounded_packed_chars_analytic64_certificate_list remaining rest of
      | NONE => NONE
      | SOME (suffix,finish) => SOME (certificate::suffix,finish)
End

Definition bounded_packed_chars_case16594_cell_def:
  bounded_packed_chars_case16594_cell bytes =
    case bounded_packed_chars_case16594_input bytes of
    | NONE => NONE
    | SOME (input,rest) =>
      case bounded_packed_chars_analytic64_certificate_list 31 rest of
      | NONE => NONE
      | SOME (certificates,finish) => SOME ((input,certificates),finish)
End

Definition bounded_packed_chars_case16594_cells_def:
  bounded_packed_chars_case16594_cells 0 bytes = SOME bytes ∧
  bounded_packed_chars_case16594_cells (SUC remaining) bytes =
    case bounded_packed_chars_case16594_cell bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
        bounded_packed_chars_case16594_cells remaining rest
End

Definition bounded_packed_chars_prefix_def:
  bounded_packed_chars_prefix [] bytes = SOME bytes ∧
  bounded_packed_chars_prefix (expected::expected_rest) bytes =
    case bytes of
    | [] => NONE
    | actual::rest =>
        if actual = expected then
          bounded_packed_chars_prefix expected_rest rest
        else NONE
End

Definition bounded_packed_chars_case16594_header_def:
  bounded_packed_chars_case16594_header bytes =
    case bounded_packed_chars_prefix
      [#"C";#"N";#"L";#"C";#"K";#"R";#"0";#"1"] bytes of
    | NONE => NONE
    | SOME rest =>
      case bounded_packed_chars_word64_aux 4 rest of
      | NONE => NONE
      | SOME (cells,rest1) =>
        case bounded_packed_chars_word64_aux 4 rest1 of
        | NONE => NONE
        | SOME (records,finish) =>
          if cells = 875w ∧ records = 31w then SOME finish else NONE
End

Definition bounded_packed_chars_case16594_payload_ok_def:
  bounded_packed_chars_case16594_payload_ok bytes ⇔
    case bounded_packed_chars_case16594_header bytes of
    | NONE => F
    | SOME rest =>
      case bounded_packed_chars_case16594_cells 875 rest of
      | SOME [] => T
      | _ => F
End

Definition bounded_packed_sequential_case16594_payload_ok_def:
  bounded_packed_sequential_case16594_payload_ok (strlit bytes) ⇔
    bounded_packed_chars_case16594_payload_ok bytes
End

Theorem bounded_packed_chars_word64_little_endian_test:
  bounded_packed_chars_word64_aux 8
    [CHR 1;CHR 2;CHR 3;CHR 4;CHR 5;CHR 6;CHR 7;CHR 8] =
      SOME (578437695752307201w,[])
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_packed_sequential_case16594_payload_truncated:
  ¬bounded_packed_sequential_case16594_payload_ok «»
Proof
  simp [bounded_packed_sequential_case16594_payload_ok_def,
        bounded_packed_chars_case16594_payload_ok_def,
        bounded_packed_chars_case16594_header_def,
        bounded_packed_chars_prefix_def]
QED

val _ = export_theory ();
