(*****************************************************************************
 * A reusable numerical enclosure for HOL4's pi/2.
 *
 * The executable arctangent reduction uses one fixed outward-rounded word
 * interval for pi/2.  HOL4's core transcendental theory supplies only the
 * coarse bound 0 < pi/2 < 2, so this theory derives the required precision
 * from Machin's identity and the already-proved alternating atan bounds.
 *****************************************************************************)
Theory compute_boundedAtanPiRefinement
Ancestors
  compute_boundedAtanRealRefinement compute_boundedWordRealRefinement
Libs
  bossLib preamble realLib Diff RealField

open realTheory transcTheory limTheory

Theorem bounded_atan_cos_nonzero:
  cos (atn x) <> &0
Proof
  irule REAL_POS_NZ
  >> irule COS_POS_PI
  >> simp [ATN_BOUNDS]
QED

Theorem bounded_cos_double_from_tan:
  cos x <> &0 ==>
  cos (&2 * x) = cos x pow 2 * (&1 - tan x pow 2)
Proof
  strip_tac
  >> rw [COS_DOUBLE, tan, real_div]
  >> REAL_ASM_FIELD_TAC
QED

Theorem bounded_cos_add_from_tan:
  cos x <> &0 /\ cos y <> &0 ==>
  cos (x + y) = cos x * cos y * (&1 - tan x * tan y)
Proof
  strip_tac
  >> rw [COS_ADD, tan, real_div]
  >> REAL_ASM_FIELD_TAC
QED

Theorem bounded_machin_linear_bounds:
  la <= (a:real) /\ a <= ua /\ lb <= b /\ b <= ub /\
  &0 <= &2 * (&4 * la - ub) /\
  &2 * (&4 * ua - lb) <= &2 ==>
  &0 <= &2 * (&4 * a - b) /\ &2 * (&4 * a - b) <= &2
Proof
  REAL_ARITH_TAC
QED

Theorem bounded_machin_expand:
  !a b:real. &2 * (&4 * a - b) = &8 * a - &2 * b
Proof
  REAL_ARITH_TAC
QED

Definition bounded_atan_lower15_real_def:
  bounded_atan_lower15_real (x:real) =
    bounded_atan_upper_real x - x pow 15 / &15
End

Theorem bounded_atan_lower15_real_diffl:
  ((\x:real. bounded_atan_lower15_real x) diffl
    (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10 +
      x pow 12 - x pow 14)) x
Proof
  rw [bounded_atan_lower15_real_def, bounded_atan_upper_real_def,
      bounded_atan_lower_real_def]
  >> mp_tac
       (Q.SPEC `x`
         (Diff.DIFF_CONV
           ``\x:real.
               x - x pow 3 / &3 + x pow 5 / &5 - x pow 7 / &7 +
                 x pow 9 / &9 - x pow 11 / &11 + x pow 13 / &13 -
                 x pow 15 / &15``))
  >> simp [bounded_atan_real_mul_div_cancel]
QED

Theorem bounded_atan_lower15_gap_diffl:
  ((\x:real. atn x - bounded_atan_lower15_real x) diffl
    (inv (&1 + x pow 2) -
      (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10 +
        x pow 12 - x pow 14))) x
Proof
  irule DIFF_SUB
  >> conj_tac
  >- MATCH_ACCEPT_TAC (Q.SPEC `x` DIFF_ATN)
  >> MATCH_ACCEPT_TAC
       (CONV_RULE (DEPTH_CONV ETA_CONV)
         bounded_atan_lower15_real_diffl)
QED

Theorem bounded_atan_lower15_gap_derivative_identity:
  inv (&1 + x pow 2) -
      (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10 +
        x pow 12 - x pow 14) =
    x pow 16 * inv (&1 + x pow 2)
Proof
  `&0 <= x pow 2` by simp [POW_2, REAL_LE_SQUARE]
  >> `&1 + x pow 2 <> 0` by REAL_ASM_ARITH_TAC
  >> REAL_ASM_FIELD_TAC
QED

Theorem bounded_atan_lower15_gap_derivative_positive:
  &0 < x ==>
  &0 < inv (&1 + x pow 2) -
    (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10 +
      x pow 12 - x pow 14)
Proof
  strip_tac
  >> rw [bounded_atan_lower15_gap_derivative_identity]
  >> irule REAL_LT_MUL
  >> conj_tac
  >- (mp_tac (Q.SPECL [`x`, `15`] POW_POS_LT) >> simp [])
  >> irule REAL_INV_POS
  >> `&0 <= x pow 2` by simp [POW_2, REAL_LE_SQUARE]
  >> REAL_ASM_ARITH_TAC
QED

Theorem bounded_atan_lower15_gap_contl_zero:
  (\x:real. atn x - bounded_atan_lower15_real x) contl &0
Proof
  irule DIFF_CONT
  >> qexists_tac
       `inv (&1 + (&0) pow 2) -
          (&1 - (&0) pow 2 + (&0) pow 4 - (&0) pow 6 +
            (&0) pow 8 - (&0) pow 10 + (&0) pow 12 - (&0) pow 14)`
  >> MATCH_ACCEPT_TAC
       (Q.INST [`x` |-> `&0`] bounded_atan_lower15_gap_diffl)
QED

Theorem bounded_atan_lower15_gap_has_positive_derivative:
  &0 < z ==>
  ?l. &0 < l /\
    ((\x:real. atn x - bounded_atan_lower15_real x) diffl l) z
Proof
  strip_tac
  >> qexists_tac
       `inv (&1 + z pow 2) -
          (&1 - z pow 2 + z pow 4 - z pow 6 + z pow 8 - z pow 10 +
            z pow 12 - z pow 14)`
  >> conj_tac
  >- (mp_tac
        (Q.INST [`x` |-> `z`]
          bounded_atan_lower15_gap_derivative_positive)
      >> asm_rewrite_tac [])
  >> MATCH_ACCEPT_TAC
       (Q.INST [`x` |-> `z`] bounded_atan_lower15_gap_diffl)
QED

Theorem bounded_atan_lower15_gap_mono_from_zero:
  &0 <= x /\ x < y ==>
  atn x - bounded_atan_lower15_real x <
    atn y - bounded_atan_lower15_real y
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL
         [`\x:real. atn x - bounded_atan_lower15_real x`, `&0`]
         DIFF_POS_MONO_LT_CU)
  >> impl_tac
  >- (conj_tac
      >- MATCH_ACCEPT_TAC bounded_atan_lower15_gap_contl_zero
      >> gen_tac
      >> strip_tac
      >> mp_tac
           (Q.INST [`z` |-> `z`]
             bounded_atan_lower15_gap_has_positive_derivative)
      >> asm_rewrite_tac [])
  >> disch_then (qspecl_then [`x`, `y`] mp_tac)
  >> simp []
QED

Theorem bounded_atan_lower15_nonnegative:
  &0 <= x ==> bounded_atan_lower15_real x <= atn x
Proof
  strip_tac
  >> Cases_on `x = &0`
  >- simp [bounded_atan_zero, bounded_atan_lower15_real_def,
           bounded_atan_upper_real_def, bounded_atan_lower_real_def]
  >> `&0 < x` by REAL_ASM_ARITH_TAC
  >> mp_tac
       (Q.INST [`x` |-> `&0`, `y` |-> `x`]
         bounded_atan_lower15_gap_mono_from_zero)
  >> impl_tac >- REAL_ASM_ARITH_TAC
  >> simp [bounded_atan_zero, bounded_atan_lower15_real_def,
           bounded_atan_upper_real_def, bounded_atan_lower_real_def]
  >> REAL_ARITH_TAC
QED

Theorem bounded_atan_pi_half_lower_real:
  bounded_signed64_real
    (bounded_interval64_lower bounded_atan_pi_half) =
  (&1727108826112:real) / &1099511627776
Proof
  rw [bounded_signed64_real_def, bounded_word_scale_real_def,
      compute_boundedAtanTheory.bounded_atan_pi_half_def,
      compute_boundedAtanTheory.bounded_atan_word64_def,
      compute_boundedIntervalTheory.bounded_interval64_lower_def,
      compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
      compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
QED

Theorem bounded_atan_pi_half_upper_real:
  bounded_signed64_real
    (bounded_interval64_upper bounded_atan_pi_half) =
  (&1727108826368:real) / &1099511627776
Proof
  rw [bounded_signed64_real_def, bounded_word_scale_real_def,
      compute_boundedAtanTheory.bounded_atan_pi_half_def,
      compute_boundedAtanTheory.bounded_atan_word64_def,
      compute_boundedIntervalTheory.bounded_interval64_upper_def,
      compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
      compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def]
QED

Theorem bounded_machin_interval_bounds:
  l5 <= (a:real) /\ a <= u5 /\ l239 <= b /\ b <= u239 /\
  lower <= &8 * l5 - &2 * u239 /\
  &8 * u5 - &2 * l239 <= upper ==>
  lower <= &8 * a - &2 * b /\ &8 * a - &2 * b <= upper
Proof
  REAL_ARITH_TAC
QED

Theorem bounded_atan_machin_identity:
  pi / &2 = &8 * atn (&1 / &5) - &2 * atn (&1 / &239)
Proof
  qabbrev_tac `a = atn (&1 / &5)`
  >> qabbrev_tac `b = atn (&1 / &239)`
  >> `tan a = &1 / &5` by simp [Abbr `a`, ATN_TAN]
  >> `tan b = &1 / &239` by simp [Abbr `b`, ATN_TAN]
  >> `cos a <> &0` by simp [Abbr `a`, bounded_atan_cos_nonzero]
  >> `cos b <> &0` by simp [Abbr `b`, bounded_atan_cos_nonzero]
  >> `cos (&2 * a) <> &0` by
       (rw [bounded_cos_double_from_tan]
        >> simp []
        >> REAL_ARITH_TAC)
  >> `tan (&2 * a) = &5 / &12` by
       (mp_tac (Q.SPEC `a` TAN_DOUBLE)
        >> asm_rewrite_tac []
        >> REAL_ASM_ARITH_TAC)
  >> `cos (&2 * (&2 * a)) =
        cos (&2 * a) pow 2 * (&1 - tan (&2 * a) pow 2)` by
       (irule bounded_cos_double_from_tan >> metis_tac [])
  >> `&4 * a = &2 * (&2 * a)` by REAL_ARITH_TAC
  >> `cos (&4 * a) =
        cos (&2 * a) pow 2 * (&1 - (&5 / &12) pow 2)` by
       metis_tac []
  >> `cos (&2 * a) pow 2 <> &0` by simp [POW_NZ]
  >> `(&1 - ((&5:real) / &12) pow 2) <> &0` by REAL_ARITH_TAC
  >> `cos (&4 * a) <> &0` by metis_tac [REAL_ENTIRE]
  >> `cos (&2 * (&2 * a)) <> &0` by metis_tac []
  >> `tan (&2 * (&2 * a)) =
        &2 * tan (&2 * a) / (&1 - tan (&2 * a) pow 2)` by
       (irule TAN_DOUBLE >> asm_rewrite_tac [])
  >> `tan (&4 * a) =
        &2 * (&5 / &12) / (&1 - (&5 / &12) pow 2)` by
       metis_tac []
  >> `&2 * ((&5:real) / &12) / (&1 - (&5 / &12) pow 2) =
        &120 / &119` by
       CONV_TAC REAL_RAT_REDUCE_CONV
  >> `tan (&4 * a) = &120 / &119` by
       metis_tac []
  >> `cos (-b) <> &0` by simp [COS_NEG]
  >> `tan (-b) = -(&1 / &239)` by simp [TAN_NEG]
  >> `cos (&4 * a + -b) =
        cos (&4 * a) * cos (-b) *
        (&1 - tan (&4 * a) * tan (-b))` by
       (irule bounded_cos_add_from_tan >> metis_tac [])
  >> `&4 * a - b = &4 * a + -b` by REAL_ARITH_TAC
  >> `cos (&4 * a - b) =
        cos (&4 * a) * cos b *
        (&1 - (&120 / &119) * -(&1 / &239))` by
       metis_tac [COS_NEG]
  >> `(&1 - ((&120:real) / &119) * -(&1 / &239)) <> &0` by
       CONV_TAC REAL_RAT_REDUCE_CONV
  >> `cos (&4 * a) * cos b <> &0` by metis_tac [REAL_ENTIRE]
  >> `cos (&4 * a - b) <> &0` by metis_tac [REAL_ENTIRE]
  >> `cos (&4 * a + -b) <> &0` by metis_tac []
  >> `tan (&4 * a + -b) =
        (tan (&4 * a) + tan (-b)) /
        (&1 - tan (&4 * a) * tan (-b))` by
       (irule TAN_ADD >> asm_rewrite_tac [])
  >> `tan (&4 * a - b) =
        ((&120 / &119) + -(&1 / &239)) /
        (&1 - (&120 / &119) * -(&1 / &239))` by
       metis_tac []
  >> `(((&120:real) / &119) + -(&1 / &239)) /
        (&1 - (&120 / &119) * -(&1 / &239)) = &1` by
       CONV_TAC REAL_RAT_REDUCE_CONV
  >> `tan (&4 * a - b) = &1` by metis_tac []
  >> `cos (&2 * (&4 * a - b)) =
        cos (&4 * a - b) pow 2 *
        (&1 - tan (&4 * a - b) pow 2)` by
       (irule bounded_cos_double_from_tan >> metis_tac [])
  >> `cos (&2 * (&4 * a - b)) =
        cos (&4 * a - b) pow 2 * (&1 - &1 pow 2)` by
       metis_tac []
  >> `(&1:real) - &1 pow 2 = &0` by
       CONV_TAC REAL_RAT_REDUCE_CONV
  >> `cos (&4 * a - b) pow 2 * (&1 - &1 pow 2) = &0` by
       metis_tac [REAL_MUL_RZERO]
  >> `cos (&2 * (&4 * a - b)) = &0` by
       metis_tac []
  >> mp_tac
       (Q.INST [`x` |-> `&1 / &5`]
         bounded_atan_alternating_bounds_nonnegative)
  >> impl_tac >- REAL_ARITH_TAC
  >> strip_tac
  >> mp_tac
       (Q.INST [`x` |-> `&1 / &239`]
         bounded_atan_alternating_bounds_nonnegative)
  >> impl_tac >- REAL_ARITH_TAC
  >> strip_tac
  >> `&0 <=
       &2 * (&4 * bounded_atan_lower_real (&1 / &5) -
             bounded_atan_upper_real (&1 / &239))` by
       (rw [bounded_atan_lower_real_def, bounded_atan_upper_real_def]
        >> CONV_TAC REAL_RAT_REDUCE_CONV)
  >> `&2 * (&4 * bounded_atan_upper_real (&1 / &5) -
             bounded_atan_lower_real (&1 / &239)) <= &2` by
       (rw [bounded_atan_lower_real_def, bounded_atan_upper_real_def]
        >> CONV_TAC REAL_RAT_REDUCE_CONV)
  >> qunabbrev_tac `a`
  >> qunabbrev_tac `b`
  >> `&0 <= &2 * (&4 * atn (&1 / &5) - atn (&1 / &239)) /\
      &2 * (&4 * atn (&1 / &5) - atn (&1 / &239)) <= &2` by
       (irule bounded_machin_linear_bounds >> metis_tac [])
  >> mp_tac (CONJUNCT2 (CONV_RULE EXISTS_UNIQUE_CONV COS_ISZERO))
  >> disch_then
       (qspecl_then
          [`&2 * (&4 * atn (&1 / &5) - atn (&1 / &239))`, `pi / &2`]
          mp_tac)
  >> disch_tac
  >> `&0 <= pi / &2 /\ pi / &2 <= &2 /\ cos (pi / &2) = &0` by
       metis_tac [PI2_BOUNDS, COS_PI2, REAL_LT_IMP_LE]
  >> `(&0 <= &2 * (&4 * atn (&1 / &5) - atn (&1 / &239)) /\
       &2 * (&4 * atn (&1 / &5) - atn (&1 / &239)) <= &2 /\
       cos (&2 * (&4 * atn (&1 / &5) - atn (&1 / &239))) = &0) /\
      &0 <= pi / &2 /\ pi / &2 <= &2 /\ cos (pi / &2) = &0` by
       metis_tac []
  >> `&2 * (&4 * atn (&1 / &5) - atn (&1 / &239)) = pi / &2` by
       metis_tac []
  >> metis_tac [bounded_machin_expand]
QED

Theorem bounded_atan_pi_half_rational_bounds:
  (&1727108826112:real) / &1099511627776 <= pi / &2 /\
  pi / &2 <= (&1727108826368:real) / &1099511627776
Proof
  mp_tac
    (Q.INST [`x` |-> `&1 / &5`]
      bounded_atan_alternating_bounds_nonnegative)
  >> impl_tac >- REAL_ARITH_TAC
  >> strip_tac
  >> mp_tac
    (Q.INST [`x` |-> `&1 / &239`]
      bounded_atan_alternating_bounds_nonnegative)
  >> impl_tac >- REAL_ARITH_TAC
  >> strip_tac
  >> `bounded_atan_lower15_real (&1 / &5) <= atn (&1 / &5)` by
       (irule bounded_atan_lower15_nonnegative >> REAL_ARITH_TAC)
  >> `(&1727108826112:real) / &1099511627776 <=
       &8 * bounded_atan_lower15_real (&1 / &5) -
       &2 * bounded_atan_upper_real (&1 / &239)` by
       (rw [bounded_atan_lower15_real_def, bounded_atan_lower_real_def,
            bounded_atan_upper_real_def]
        >> CONV_TAC REAL_RAT_REDUCE_CONV)
  >> `&8 * bounded_atan_upper_real (&1 / &5) -
       &2 * bounded_atan_lower_real (&1 / &239) <=
       (&1727108826368:real) / &1099511627776` by
       (rw [bounded_atan_lower_real_def, bounded_atan_upper_real_def]
        >> CONV_TAC REAL_RAT_REDUCE_CONV)
  >> `(&1727108826112:real) / &1099511627776 <=
       &8 * atn (&1 / &5) - &2 * atn (&1 / &239) /\
       &8 * atn (&1 / &5) - &2 * atn (&1 / &239) <=
       (&1727108826368:real) / &1099511627776` by
       (irule bounded_machin_interval_bounds >> metis_tac [])
  >> metis_tac [bounded_atan_machin_identity]
QED

Theorem bounded_atan_pi_half_contains_real:
  bounded_interval64_contains_real bounded_atan_pi_half (pi / &2)
Proof
  PURE_REWRITE_TAC [bounded_interval64_contains_real_def]
  >> metis_tac [bounded_atan_pi_half_lower_real,
                bounded_atan_pi_half_upper_real,
                bounded_atan_pi_half_rational_bounds]
QED

val _ = export_theory ();
