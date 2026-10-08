(*****************************************************************************
 * Development-only complete-batch failure localizer for case16594.
 *
 * The recursive bound remains a HOL natural, but every externally observed
 * field has an explicit word representation.  The three output bytes are the
 * little-endian number of accepted cells followed by a reason code:
 *   0 complete; 1 cell parse; 2 evaluation; 3 domain; 5 final bound;
 *   6 trailing bytes; 7 header.
 *****************************************************************************)
Theory compute_boundedCase16594BatchStatus
Ancestors
  compute_boundedPackedSequentialCase16594Check
Libs
  bossLib preamble

Definition bounded_packed_chars_case16594_batch_status_aux_def:
  bounded_packed_chars_case16594_batch_status_aux 0 bytes
      (accepted:word64) =
    (if bytes = [] then (accepted,(0w:word8)) else (accepted,6w)) ∧
  bounded_packed_chars_case16594_batch_status_aux (SUC remaining) bytes
      accepted =
    case bounded_packed_chars_case16594_cell bytes of
    | NONE => (accepted,(1w:word8))
    | SOME (cell,rest) =>
        if bounded_packed_chars_case16594_eval_cell cell then
          bounded_packed_chars_case16594_batch_status_aux remaining rest
            (accepted + 1w)
        else
          (accepted,bounded_packed_chars_case16594_cell_status8 cell)
End

Definition bounded_packed_chars_case16594_batch_status_def:
  bounded_packed_chars_case16594_batch_status bytes =
    case bounded_packed_chars_case16594_header bytes of
    | NONE => ((0w:word64),(7w:word8))
    | SOME rest =>
        bounded_packed_chars_case16594_batch_status_aux 875 rest 0w
End

Definition bounded_packed_chars_case16594_batch_status_select_def:
  bounded_packed_chars_case16594_batch_status_select bytes =
    case bytes of
    | [] => (255w:word8)
    | mode::payload =>
      case bounded_packed_chars_case16594_batch_status payload of
      | (accepted,reason) =>
        if ORD mode = 0 then ((w2w accepted):word8)
        else if ORD mode = 1 then ((w2w (accepted >>> 8)):word8)
        else if ORD mode = 2 then reason
        else 254w
End

Theorem bounded_packed_chars_case16594_batch_status_truncated:
  bounded_packed_chars_case16594_batch_status_select [] = (255w:word8)
Proof
  EVAL_TAC
QED

val _ = export_theory ();
