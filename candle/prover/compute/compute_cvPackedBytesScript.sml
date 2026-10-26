(*****************************************************************************
 * Compact byte strings represented as cv data.
 *
 * A value is a cv list of records Pair (Num length) (Num packed), terminated
 * by Num 0.  Bytes in each natural are little-endian base 256.  Each record
 * is bounded to 256 bytes and must be canonical (no unconsumed high digits).
 * This keeps large certificate evidence in the theorem term without one cv
 * list cell per character.
 *****************************************************************************)
Theory compute_cvPackedBytes
Ancestors
  compute_payload3Fast
Libs
  bossLib preamble

Definition cv_packed_bytes_chunk_limit_def:
  cv_packed_bytes_chunk_limit : num = 256
End

Definition cv_unpack_byte_chunk_def:
  cv_unpack_byte_chunk 0 packed =
    (if packed = 0 then SOME [] else NONE) /\
  cv_unpack_byte_chunk (SUC length) packed =
    case cv_unpack_byte_chunk length (packed DIV 256) of
    | NONE => NONE
    | SOME rest => SOME (CHR (packed MOD 256)::rest)
End

Definition cv_unpack_byte_chunks_def:
  cv_unpack_byte_chunks (Num value) =
    (if value = 0 then SOME [] else NONE) /\
  cv_unpack_byte_chunks (Pair chunk tail) =
    case chunk of
    | Num _ => NONE
    | Pair length_value packed_value =>
        case length_value of
        | Pair _ _ => NONE
        | Num byte_count =>
            case packed_value of
            | Pair _ _ => NONE
            | Num packed =>
                if byte_count = 0 \/
                   cv_packed_bytes_chunk_limit < byte_count then NONE
                else
                  case cv_unpack_byte_chunk byte_count packed of
                  | NONE => NONE
                  | SOME prefix =>
                      case cv_unpack_byte_chunks tail of
                      | NONE => NONE
                      | SOME suffix => SOME (prefix ++ suffix)
End

Theorem cv_unpack_byte_chunk_length:
  !byte_count packed bytes.
    cv_unpack_byte_chunk byte_count packed = SOME bytes ==>
    LENGTH bytes = byte_count
Proof
  Induct
  >- simp [cv_unpack_byte_chunk_def]
  >> rpt gen_tac
  >> simp [Once cv_unpack_byte_chunk_def]
  >> every_case_tac
  >> simp []
  >> strip_tac
  >> qpat_x_assum ‘∀packed bytes. _’
       (qspecl_then [‘packed DIV 256’,‘x’] mp_tac)
  >> asm_rewrite_tac []
  >> strip_tac
  >> gvs []
QED

Theorem cv_unpack_byte_chunks_rejects_nonzero_terminator[simp]:
  0 < value ==> cv_unpack_byte_chunks (Num value) = NONE
Proof
  simp [cv_unpack_byte_chunks_def]
QED

Theorem cv_unpack_byte_chunks_rejects_zero_length[simp]:
  cv_unpack_byte_chunks
    (Pair (Pair (Num 0) (Num packed)) (chunks_tail:cv)) = NONE
Proof
  simp [cv_unpack_byte_chunks_def]
QED

Theorem cv_unpack_byte_chunks_rejects_oversize[simp]:
  cv_packed_bytes_chunk_limit < byte_count ==>
  cv_unpack_byte_chunks
    (Pair (Pair (Num byte_count) (Num packed)) (chunks_tail:cv)) = NONE
Proof
  simp [cv_unpack_byte_chunks_def]
QED

(*
 * The linear chunk list above is convenient for small witnesses, but a
 * multi-megabyte certificate would make both its cv term and its decoder
 * tens of thousands of constructors deep.  The production input shape is a
 * balanced tree instead:
 *
 *   Pair (Num 0) (Pair (Num byte_count) (Num packed))   -- leaf
 *   Pair (Num 1) (Pair left right)                      -- branch
 *
 * The accumulator form visits the right subtree first and then prepends the
 * left subtree.  It therefore builds every output byte once rather than
 * repeatedly appending at every level of the balanced tree.
 *)
Definition cv_unpack_byte_tree_append_def:
  cv_unpack_byte_tree_append (Num value) suffix = NONE /\
  cv_unpack_byte_tree_append
      (Pair (Num 0) (Pair (Num byte_count) (Num packed))) suffix =
    (if byte_count = 0 \/
        cv_packed_bytes_chunk_limit < byte_count then NONE
     else
       case cv_unpack_byte_chunk byte_count packed of
       | NONE => NONE
       | SOME prefix => SOME (prefix ++ suffix)) /\
  cv_unpack_byte_tree_append (Pair (Num 1) (Pair left right)) suffix =
    (case cv_unpack_byte_tree_append right suffix of
     | NONE => NONE
     | SOME right_suffix =>
         cv_unpack_byte_tree_append left right_suffix) /\
  cv_unpack_byte_tree_append _ suffix = NONE
Termination
  wf_rel_tac `measure (compute_exec$cv_size o FST)` >> rw []
End

Definition cv_unpack_byte_tree_def:
  cv_unpack_byte_tree tree = cv_unpack_byte_tree_append tree []
End

Theorem cv_unpack_byte_tree_rejects_num[simp]:
  cv_unpack_byte_tree (Num value) = NONE
Proof
  simp [cv_unpack_byte_tree_def,cv_unpack_byte_tree_append_def]
QED

Theorem cv_unpack_byte_tree_rejects_zero_length[simp]:
  cv_unpack_byte_tree
    (Pair (Num 0) (Pair (Num 0) (Num packed))) = NONE
Proof
  simp [cv_unpack_byte_tree_def,cv_unpack_byte_tree_append_def]
QED

Theorem cv_unpack_byte_tree_rejects_oversize[simp]:
  cv_packed_bytes_chunk_limit < byte_count ==>
  cv_unpack_byte_tree
    (Pair (Num 0) (Pair (Num byte_count) (Num packed))) = NONE
Proof
  simp [cv_unpack_byte_tree_def,cv_unpack_byte_tree_append_def]
QED

Theorem cv_unpack_byte_tree_rejects_unknown_tag[simp]:
  1 < tag ==>
  cv_unpack_byte_tree (Pair (Num tag) payload) = NONE
Proof
  Cases_on `payload`
  >> simp [cv_unpack_byte_tree_def,cv_unpack_byte_tree_append_def]
QED

val _ = export_theory ();
