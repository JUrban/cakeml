(*****************************************************************************
 * Parser for the compact native cv syntax emitted by the earlier Flyspeck
 * source capture (`n42` and `p(left,right)`).  Parsed values are still
 * authenticated by the logical source decoder and checker; textual spelling
 * is not an artifact identity or a family-selection mechanism.
 *****************************************************************************)
Theory compute_cvNativeRuntime
Ancestors
  compute_cvPackedBytesRuntime
Libs
  bossLib preamble

Definition cv_native_parse_term_def:
  (cv_native_parse_term (fuel:num) (input:char list) :
      (cv # char list) option) =
    case fuel of
    | 0 => NONE
    | SUC smaller =>
        case input of
        | [] => NONE
        | marker::rest =>
            if marker = #"n" then
              cv_flat_num_result (cv_flat_parse_digits rest F 0)
            else if marker = #"p" then
              case rest of
              | [] => NONE
              | open_marker::after_open =>
                  if open_marker <> #"(" then NONE else
                  case cv_native_parse_term smaller after_open of
                  | NONE => NONE
                  | SOME (left,after_left) =>
                      case after_left of
                      | [] => NONE
                      | separator::after_separator =>
                          if separator <> #"," then NONE else
                          case cv_native_parse_term smaller after_separator of
                          | NONE => NONE
                          | SOME (right,after_right) =>
                              case after_right of
                              | [] => NONE
                              | close_marker::after_close =>
                                  if close_marker = #")" then
                                    SOME
                                      (compute_exec$Pair left right,
                                       after_close)
                                  else NONE
            else NONE
End

Definition cv_native_parse_one_def:
  cv_native_parse_one input =
    case cv_native_parse_term (LENGTH input) (cv_flat_skip_space input) of
    | NONE => NONE
    | SOME (value,rest) =>
        if cv_flat_skip_space rest = [] then SOME value else NONE
End

Definition cv_external_parse_one_def:
  cv_external_parse_one input =
    case cv_flat_parse_one input of
    | SOME value => SOME value
    | NONE => cv_native_parse_one input
End

Theorem cv_external_parse_one_examples:
  cv_external_parse_one (EXPLODE "P N 3 N 4\n") =
    SOME (compute_exec$Pair (compute_exec$Num 3) (compute_exec$Num 4)) /\
  cv_external_parse_one (EXPLODE "p(n3,n4)\n") =
    SOME (compute_exec$Pair (compute_exec$Num 3) (compute_exec$Num 4))
Proof
  EVAL_TAC
QED

Theorem cv_native_parse_one_rejects_malformed:
  cv_native_parse_one (EXPLODE "p(n3,n4") = NONE /\
  cv_native_parse_one (EXPLODE "p(n3,n4))") = NONE /\
  cv_native_parse_one (EXPLODE "p(n3,n)") = NONE /\
  cv_native_parse_one (EXPLODE "p(n3, n4)") = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
