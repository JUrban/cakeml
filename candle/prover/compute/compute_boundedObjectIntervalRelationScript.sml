(*****************************************************************************
 * Representation boundary between the fixed-word NL checker and Candle's
 * object-level signed fixed-scale intervals.
 *
 * The specialized checker stores one canonical sign bit and a word64
 * magnitude at scale 2^40.  The existing object checker stores a signed
 * integer as [Pair (Num positive) (Num negative)] and currently uses scale
 * 10^12.  Keeping this conversion and the cross-scale enclosure relation
 * explicit prevents the fast path from silently treating the two encodings
 * (or their scales) as identical.
 *****************************************************************************)
Theory compute_boundedObjectIntervalRelation
Ancestors
  compute_boundedCase10173Packet
Libs
  bossLib preamble intLib

val _ = numLib.temp_prefer_num ();
val _ = monadsyntax.temp_enable_monad "option";

Definition bounded_word_scale_int_def:
  bounded_word_scale_int : int = 1099511627776
End

Definition bounded_object_fixed_scale_int_def:
  bounded_object_fixed_scale_int : int = 1000000000000
End

(* Decoder for the object checker's [positive,negative] signed representation.
 * It is deliberately total only on the exact two-number shape. *)
Definition bounded_object_signed_int_def:
  bounded_object_signed_int
      (Pair (Num positive) (Num negative) : cv) =
    SOME ((&positive:int) - &negative) /\
  bounded_object_signed_int _ = NONE
End

Definition bounded_object_interval_ints_def:
  bounded_object_interval_ints (Pair lower upper : cv) =
    do
      lower' <- bounded_object_signed_int lower;
      upper' <- bounded_object_signed_int upper;
      return (lower',upper')
    od /\
  bounded_object_interval_ints _ = NONE
End

(* The raw Flyspeck jobs use canonical rationals encoded as
 * [Pair signed (Num (denominator - 1))].  Decode the mathematical numerator
 * and the necessarily positive denominator without performing any rounded
 * conversion first. *)
Definition bounded_object_q_ints_def:
  bounded_object_q_ints
      (Pair signed (Num denominator_minus_one) : cv) =
    do
      numerator <- bounded_object_signed_int signed;
      return (numerator,&(SUC denominator_minus_one):int)
    od /\
  bounded_object_q_ints _ = NONE
End

Definition bounded_object_q_interval_ints_def:
  bounded_object_q_interval_ints (Pair lower upper : cv) =
    do
      lower' <- bounded_object_q_ints lower;
      upper' <- bounded_object_q_ints upper;
      return (lower',upper')
    od /\
  bounded_object_q_interval_ints _ = NONE
End

Definition bounded_object_q_interval_list_def:
  bounded_object_q_interval_list (Num 0 : cv) = SOME [] /\
  bounded_object_q_interval_list (Pair interval intervals) =
    do
      interval' <- bounded_object_q_interval_ints interval;
      intervals' <- bounded_object_q_interval_list intervals;
      return (interval'::intervals')
    od /\
  bounded_object_q_interval_list _ = NONE
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Definition bounded_signed64_object_cv_def:
  bounded_signed64_object_cv
      (BoundedSigned64 negative magnitude) : cv =
    if negative then Pair (Num 0) (Num (w2n magnitude))
    else Pair (Num (w2n magnitude)) (Num 0)
End

Definition bounded_interval64_object_cv_def:
  bounded_interval64_object_cv (BoundedInterval64 lower upper) : cv =
    Pair (bounded_signed64_object_cv lower)
      (bounded_signed64_object_cv upper)
End

(* [interval] encloses the object interval after accounting for distinct
 * positive scales.  Cross multiplication keeps the relation entirely in
 * exact integer arithmetic.  Object endpoint ordering is part of the
 * fail-closed boundary rather than an ambient assumption. *)
Definition bounded_interval64_covers_object_at_scale_def:
  bounded_interval64_covers_object_at_scale object_scale interval encoded <=>
    0 < object_scale /\
    case bounded_object_interval_ints encoded of
    | NONE => F
    | SOME (object_lower,object_upper) =>
        object_lower <= object_upper /\
        object_scale *
            bounded_signed64_to_int (bounded_interval64_lower interval) <=
          bounded_word_scale_int * object_lower /\
        bounded_word_scale_int * object_upper <=
          object_scale *
            bounded_signed64_to_int (bounded_interval64_upper interval)
End

Definition bounded_interval64_covers_object_fixed_def:
  bounded_interval64_covers_object_fixed interval encoded <=>
    bounded_interval64_covers_object_at_scale
      bounded_object_fixed_scale_int interval encoded
End

(* A representation-level diagnostic only: the word interval and object
 * interval have a nonempty intersection after exact cross multiplication.
 * Overlap is deliberately distinct from enclosure and is not sufficient to
 * authorize either interval as a replacement for the other. *)
Definition bounded_interval64_overlaps_object_at_scale_def:
  bounded_interval64_overlaps_object_at_scale object_scale interval encoded <=>
    0 < object_scale /\
    case bounded_object_interval_ints encoded of
    | NONE => F
    | SOME (object_lower,object_upper) =>
        object_lower <= object_upper /\
        object_scale *
            bounded_signed64_to_int (bounded_interval64_lower interval) <=
          bounded_word_scale_int * object_upper /\
        bounded_word_scale_int * object_lower <=
          object_scale *
            bounded_signed64_to_int (bounded_interval64_upper interval)
End

Definition bounded_interval64_overlaps_object_fixed_def:
  bounded_interval64_overlaps_object_fixed interval encoded <=>
    bounded_interval64_overlaps_object_at_scale
      bounded_object_fixed_scale_int interval encoded
End

(* Direct source binding for a rounded word interval.  This relates the word
 * endpoints to the original rational box endpoints, so the fast packet
 * cannot substitute a different box that merely happens to pass the same
 * numerical checker. *)
Definition bounded_interval64_covers_object_q_ints_def:
  bounded_interval64_covers_object_q_ints interval
      ((lower_numerator,lower_denominator),
       (upper_numerator,upper_denominator)) <=>
    0 < lower_denominator /\
    0 < upper_denominator /\
    lower_numerator * upper_denominator <=
      upper_numerator * lower_denominator /\
    lower_denominator *
        bounded_signed64_to_int (bounded_interval64_lower interval) <=
      bounded_word_scale_int * lower_numerator /\
    bounded_word_scale_int * upper_numerator <=
      upper_denominator *
        bounded_signed64_to_int (bounded_interval64_upper interval)
End

Definition bounded_interval64_covers_object_q_def:
  bounded_interval64_covers_object_q interval encoded <=>
    case bounded_object_q_interval_ints encoded of
    | NONE => F
    | SOME object_interval =>
        bounded_interval64_covers_object_q_ints interval object_interval
End

Definition bounded_interval64_list_covers_object_q_def:
  bounded_interval64_list_covers_object_q intervals encoded <=>
    case bounded_object_q_interval_list encoded of
    | NONE => F
    | SOME object_intervals =>
        LIST_REL bounded_interval64_covers_object_q_ints
          intervals object_intervals
End

Theorem bounded_object_signed_int_object_cv[simp]:
  bounded_object_signed_int (bounded_signed64_object_cv value) =
    SOME (bounded_signed64_to_int value)
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> simp [bounded_object_signed_int_def,
           bounded_signed64_object_cv_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
QED

Theorem bounded_object_interval_ints_object_cv[simp]:
  bounded_object_interval_ints (bounded_interval64_object_cv interval) =
    SOME
      (bounded_signed64_to_int (bounded_interval64_lower interval),
       bounded_signed64_to_int (bounded_interval64_upper interval))
Proof
  Cases_on `interval`
  >> simp [bounded_object_interval_ints_def,
           bounded_interval64_object_cv_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem bounded_object_signed_int_rejects_num[simp]:
  bounded_object_signed_int (Num n) = NONE
Proof
  simp [bounded_object_signed_int_def]
QED

Theorem bounded_object_signed_int_rejects_nested_left[simp]:
  bounded_object_signed_int (Pair (Pair left right) value) = NONE
Proof
  simp [bounded_object_signed_int_def]
QED

Theorem bounded_object_signed_int_rejects_nested_right[simp]:
  bounded_object_signed_int (Pair value (Pair left right)) = NONE
Proof
  Cases_on `value`
  >> simp [bounded_object_signed_int_def]
QED

Theorem bounded_object_interval_ints_rejects_num[simp]:
  bounded_object_interval_ints (Num n) = NONE
Proof
  simp [bounded_object_interval_ints_def]
QED

Theorem bounded_object_q_ints_denominator_positive:
  bounded_object_q_ints encoded = SOME (numerator,denominator) ==>
  0 < denominator
Proof
  qsuff_tac
    `!encoded numerator denominator.
       bounded_object_q_ints encoded = SOME (numerator,denominator) ==>
       0 < denominator`
  >- metis_tac []
  >> ho_match_mp_tac bounded_object_q_ints_ind
  >> rw [bounded_object_q_ints_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_interval64_covers_object_at_scale_components:
  bounded_interval64_covers_object_at_scale object_scale interval encoded /\
  bounded_object_interval_ints encoded = SOME (object_lower,object_upper) ==>
  0 < object_scale /\
  object_lower <= object_upper /\
  object_scale *
      bounded_signed64_to_int (bounded_interval64_lower interval) <=
    bounded_word_scale_int * object_lower /\
  bounded_word_scale_int * object_upper <=
    object_scale *
      bounded_signed64_to_int (bounded_interval64_upper interval)
Proof
  rw [bounded_interval64_covers_object_at_scale_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_interval64_overlaps_object_at_scale_components:
  bounded_interval64_overlaps_object_at_scale object_scale interval encoded /\
  bounded_object_interval_ints encoded = SOME (object_lower,object_upper) ==>
  0 < object_scale /\
  object_lower <= object_upper /\
  object_scale *
      bounded_signed64_to_int (bounded_interval64_lower interval) <=
    bounded_word_scale_int * object_upper /\
  bounded_word_scale_int * object_lower <=
    object_scale *
      bounded_signed64_to_int (bounded_interval64_upper interval)
Proof
  rw [bounded_interval64_overlaps_object_at_scale_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_interval64_covers_object_at_word_scale:
  bounded_interval64_valid interval ==>
  bounded_interval64_covers_object_at_scale bounded_word_scale_int interval
    (bounded_interval64_object_cv interval)
Proof
  Cases_on `interval`
  >> simp [bounded_interval64_covers_object_at_scale_def,
           bounded_word_scale_int_def,
           compute_boundedIntervalTheory.bounded_interval64_valid_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
QED

Theorem bounded_interval64_covers_object_fixed_decodes:
  bounded_interval64_covers_object_fixed interval encoded ==>
  ?object_lower object_upper.
    bounded_object_interval_ints encoded =
      SOME (object_lower,object_upper) /\
    object_lower <= object_upper
Proof
  rw [bounded_interval64_covers_object_fixed_def,
      bounded_interval64_covers_object_at_scale_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_interval64_covers_object_q_components:
  bounded_interval64_covers_object_q interval encoded /\
  bounded_object_q_interval_ints encoded =
    SOME ((lower_numerator,lower_denominator),
          (upper_numerator,upper_denominator)) ==>
  0 < lower_denominator /\
  0 < upper_denominator /\
  lower_numerator * upper_denominator <=
    upper_numerator * lower_denominator /\
  lower_denominator *
      bounded_signed64_to_int (bounded_interval64_lower interval) <=
    bounded_word_scale_int * lower_numerator /\
  bounded_word_scale_int * upper_numerator <=
    upper_denominator *
      bounded_signed64_to_int (bounded_interval64_upper interval)
Proof
  rw [bounded_interval64_covers_object_q_def]
  >> every_case_tac
  >> gvs [bounded_interval64_covers_object_q_ints_def]
QED

Theorem bounded_interval64_list_covers_object_q_decodes:
  bounded_interval64_list_covers_object_q intervals encoded ==>
  ?object_intervals.
    bounded_object_q_interval_list encoded = SOME object_intervals /\
    LIST_REL bounded_interval64_covers_object_q_ints intervals object_intervals /\
    LENGTH intervals = LENGTH object_intervals
Proof
  rw [bounded_interval64_list_covers_object_q_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [LIST_REL_LENGTH]
QED

Theorem bounded_interval64_list_covers_object_q_rejects_nonlist[simp]:
  ~bounded_interval64_list_covers_object_q intervals (Num (SUC n))
Proof
  simp [bounded_interval64_list_covers_object_q_def,
        bounded_object_q_interval_list_def]
QED

val _ = export_theory ();
