(*****************************************************************************
 * Runtime construction of compact certificate values and a small canonical
 * external cv-data reader.
 *
 * These functions are for development executables and host-side theorem-term
 * construction.  The authenticated checker, not the external representation,
 * remains the authority for accepting certificate, source, job, and root data.
 *****************************************************************************)
Theory compute_cvPackedBytesRuntime
Ancestors
  compute_cvPackedBytes
Libs
  bossLib preamble

Definition cv_pack_byte_chunk_aux_def:
  cv_pack_byte_chunk_aux 0 bytes factor packed byte_count =
    (byte_count,packed,bytes) /\
  cv_pack_byte_chunk_aux (SUC fuel) [] factor packed byte_count =
    (byte_count,packed,[]) /\
  cv_pack_byte_chunk_aux (SUC fuel) (byte::bytes) factor packed byte_count =
    cv_pack_byte_chunk_aux fuel bytes (factor * 256)
      (packed + factor * ORD byte) (SUC byte_count)
End

Definition cv_packed_byte_leaf_def:
  cv_packed_byte_leaf byte_count packed =
    Pair (Num 0) (Pair (Num byte_count) (Num packed))
End

Definition cv_packed_byte_branch_def:
  cv_packed_byte_branch left right =
    Pair (Num 1) (Pair left right)
End

Definition cv_pack_byte_leaves_aux_def:
  cv_pack_byte_leaves_aux 0 bytes accumulator = REVERSE accumulator /\
  cv_pack_byte_leaves_aux (SUC fuel) [] accumulator = REVERSE accumulator /\
  cv_pack_byte_leaves_aux (SUC fuel) bytes accumulator =
    let (byte_count,packed,rest) =
      cv_pack_byte_chunk_aux cv_packed_bytes_chunk_limit bytes 1 0 0 in
    cv_pack_byte_leaves_aux fuel rest
      (cv_packed_byte_leaf byte_count packed::accumulator)
End

Definition cv_pack_byte_tree_round_def:
  cv_pack_byte_tree_round [] accumulator = REVERSE accumulator /\
  cv_pack_byte_tree_round [node] accumulator =
    REVERSE (node::accumulator) /\
  cv_pack_byte_tree_round (left::right::rest) accumulator =
    cv_pack_byte_tree_round rest
      (cv_packed_byte_branch left right::accumulator)
End

Definition cv_balance_byte_tree_def:
  cv_balance_byte_tree 0 nodes = NONE /\
  cv_balance_byte_tree (SUC fuel) [] = NONE /\
  cv_balance_byte_tree (SUC fuel) [node] = SOME node /\
  cv_balance_byte_tree (SUC fuel) nodes =
    cv_balance_byte_tree fuel (cv_pack_byte_tree_round nodes [])
End

Definition cv_pack_byte_tree_def:
  cv_pack_byte_tree bytes =
    cv_balance_byte_tree (LENGTH bytes)
      (cv_pack_byte_leaves_aux (LENGTH bytes) bytes [])
End

Definition cv_flat_space_def:
  cv_flat_space character <=>
    character = #" " \/ character = #"\t" \/
    character = #"\r" \/ character = #"\n"
End

Definition cv_flat_skip_space_def:
  cv_flat_skip_space [] = [] /\
  cv_flat_skip_space (character::rest) =
    if cv_flat_space character then cv_flat_skip_space rest
    else character::rest
End

Definition cv_flat_digit_value_def:
  cv_flat_digit_value character =
    if character = #"0" then SOME (0:num) else
    if character = #"1" then SOME 1 else
    if character = #"2" then SOME 2 else
    if character = #"3" then SOME 3 else
    if character = #"4" then SOME 4 else
    if character = #"5" then SOME 5 else
    if character = #"6" then SOME 6 else
    if character = #"7" then SOME 7 else
    if character = #"8" then SOME 8 else
    if character = #"9" then SOME 9 else NONE
End

Definition cv_flat_parse_digits_def:
  cv_flat_parse_digits ([]:char list) seen (value:num) =
    (if seen then SOME (value,[]) else NONE) /\
  cv_flat_parse_digits (character::rest) seen value =
    case cv_flat_digit_value character of
    | NONE => if seen then SOME (value,character::rest) else NONE
    | SOME digit => cv_flat_parse_digits rest T (10 * value + digit)
End

Definition cv_flat_num_result_def:
  cv_flat_num_result (NONE:(num # char list) option) =
    (NONE:(cv # char list) option) /\
  cv_flat_num_result (SOME (value,(remaining_characters:char list))) =
    SOME ((compute_exec$Num value):cv,remaining_characters)
End

Definition cv_flat_parse_term_def:
  (cv_flat_parse_term (fuel:num) (input:char list) :
      (cv # char list) option) =
    case fuel of
    | 0 => NONE
    | SUC smaller =>
        case cv_flat_skip_space input of
        | [] => NONE
        | marker::rest =>
            if marker = #"N" then
              cv_flat_num_result
                (cv_flat_parse_digits (cv_flat_skip_space rest) F 0)
            else if marker = #"P" then
              case cv_flat_parse_term smaller rest of
              | NONE => NONE
              | SOME (left,after_left) =>
                  case cv_flat_parse_term smaller after_left of
                  | NONE => NONE
                  | SOME (right,after_right) =>
                      SOME (compute_exec$Pair left right,after_right)
            else NONE
End

Definition cv_flat_parse_one_def:
  cv_flat_parse_one input =
    case cv_flat_parse_term (LENGTH input) input of
    | NONE => NONE
    | SOME (value,rest) =>
        if cv_flat_skip_space rest = [] then SOME value else NONE
End

Definition cv_flat_parse_list_aux_def:
  cv_flat_parse_list_aux 0 input =
    (if cv_flat_skip_space input = [] then
       SOME (compute_exec$Num 0) else NONE) /\
  cv_flat_parse_list_aux (SUC fuel) input =
    case cv_flat_skip_space input of
    | [] => SOME (compute_exec$Num 0)
    | normalized =>
        case cv_flat_parse_term (SUC fuel) normalized of
        | NONE => NONE
        | SOME (head,rest) =>
            case cv_flat_parse_list_aux fuel rest of
            | NONE => NONE
            | SOME parsed_tail_value =>
                SOME (compute_exec$Pair head parsed_tail_value)
End

Definition cv_flat_parse_list_def:
  cv_flat_parse_list input = cv_flat_parse_list_aux (LENGTH input) input
End

Theorem cv_pack_byte_tree_small_roundtrip:
  cv_pack_byte_tree [#"A";#"B";#"C"] =
    SOME (compute_exec$Pair (compute_exec$Num 0)
      (compute_exec$Pair (compute_exec$Num 3)
        (compute_exec$Num 4407873))) /\
  cv_unpack_byte_tree
    (compute_exec$Pair (compute_exec$Num 0)
      (compute_exec$Pair (compute_exec$Num 3)
        (compute_exec$Num 4407873))) =
    SOME [#"A";#"B";#"C"]
Proof
  EVAL_TAC
QED

Theorem cv_flat_parse_examples:
  cv_flat_parse_one (EXPLODE "P N 3 N 4\n") =
    SOME (compute_exec$Pair (compute_exec$Num 3) (compute_exec$Num 4)) /\
  cv_flat_parse_list (EXPLODE "N 7\nP N 8 N 9\n") =
    SOME (compute_exec$Pair (compute_exec$Num 7)
      (compute_exec$Pair
        (compute_exec$Pair (compute_exec$Num 8) (compute_exec$Num 9))
        (compute_exec$Num 0)))
Proof
  EVAL_TAC
QED

val _ = export_theory ();
