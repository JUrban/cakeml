(*****************************************************************************
 * Shared real-analytic refinement for the fixed-scale arctangent kernel.
 *
 * The executable kernel evaluates outward-rounded alternating polynomials on
 * (-1,1), then uses certified reciprocal reduction outside that range.  This
 * theory begins the reusable mathematical side of that contract: the exact
 * alternating polynomials bound HOL4's real arctangent on the positive unit
 * interval.  No source expression receives a bespoke calculus proof.
 *****************************************************************************)
Theory compute_boundedAtanRealRefinement
Ancestors
  compute_boundedAtan transc
Libs
  bossLib preamble realLib Diff RealField

open realTheory transcTheory limTheory

Definition bounded_atan_lower_real_def:
  bounded_atan_lower_real (x:real) =
    x - x pow 3 / &3 + x pow 5 / &5 - x pow 7 / &7 +
      x pow 9 / &9 - x pow 11 / &11
End

Definition bounded_atan_upper_real_def:
  bounded_atan_upper_real (x:real) =
    bounded_atan_lower_real x + x pow 13 / &13
End

Theorem bounded_atan_zero:
  atn (&0) = &0
Proof
  mp_tac (Q.SPEC `&0` TAN_ATN)
  >> simp [PI_POS, TAN_0]
QED

Theorem bounded_atan_div_pow_diffl:
  (n:num) <> 0 ==>
  ((\x:real. x pow n / &n) diffl (x pow (n - 1))) x
Proof
  strip_tac
  >> mp_tac
       (MATCH_MP
         (Q.SPECL
           [`\x:real. x pow n`, `inv (&n)`, `&n * x pow (n - 1)`, `x`]
           DIFF_CMUL)
         (Q.SPECL [`n`, `x`] DIFF_POW))
  >> rw [real_div]
  >> simp [GSYM REAL_MUL_ASSOC]
QED

Theorem bounded_atan_real_mul_div_cancel:
  (c:real) <> 0 ==> c * y / c = y
Proof
  strip_tac
  >> simp [REAL_DIV_RMUL_CANCEL, REAL_MUL_COMM]
QED

Theorem bounded_atan_lower_real_diffl:
  ((\x:real. bounded_atan_lower_real x) diffl
    (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10)) x
Proof
  rw [bounded_atan_lower_real_def]
  >> mp_tac
       (Q.SPEC `x`
         (Diff.DIFF_CONV
           ``\x:real.
               x - x pow 3 / &3 + x pow 5 / &5 - x pow 7 / &7 +
                 x pow 9 / &9 - x pow 11 / &11``))
  >> simp [bounded_atan_real_mul_div_cancel]
QED

Theorem bounded_atan_upper_real_diffl:
  ((\x:real. bounded_atan_upper_real x) diffl
    (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10 +
      x pow 12)) x
Proof
  rw [bounded_atan_upper_real_def, bounded_atan_lower_real_def]
  >> mp_tac
       (Q.SPEC `x`
         (Diff.DIFF_CONV
           ``\x:real.
               x - x pow 3 / &3 + x pow 5 / &5 - x pow 7 / &7 +
                 x pow 9 / &9 - x pow 11 / &11 + x pow 13 / &13``))
  >> simp [bounded_atan_real_mul_div_cancel]
QED

Theorem bounded_atan_lower_gap_diffl:
  ((\x:real. atn x - bounded_atan_lower_real x) diffl
    (inv (&1 + x pow 2) -
      (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10))) x
Proof
  irule DIFF_SUB
  >> conj_tac
  >- MATCH_ACCEPT_TAC (Q.SPEC `x` DIFF_ATN)
  >> MATCH_ACCEPT_TAC
       (CONV_RULE (DEPTH_CONV ETA_CONV)
         bounded_atan_lower_real_diffl)
QED

Theorem bounded_atan_upper_gap_diffl:
  ((\x:real. bounded_atan_upper_real x - atn x) diffl
    ((&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10 +
       x pow 12) - inv (&1 + x pow 2))) x
Proof
  irule DIFF_SUB
  >> conj_tac
  >- MATCH_ACCEPT_TAC
       (CONV_RULE (DEPTH_CONV ETA_CONV)
         bounded_atan_upper_real_diffl)
  >> MATCH_ACCEPT_TAC (Q.SPEC `x` DIFF_ATN)
QED

Theorem bounded_atan_lower_gap_derivative_identity:
  inv (&1 + x pow 2) -
      (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10) =
    x pow 12 * inv (&1 + x pow 2)
Proof
  `&0 <= x pow 2` by simp [POW_2, REAL_LE_SQUARE]
  >> `&1 + x pow 2 <> 0` by
    REAL_ASM_ARITH_TAC
  >> REAL_ASM_FIELD_TAC
QED

Theorem bounded_atan_upper_gap_derivative_identity:
  (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10 +
      x pow 12) - inv (&1 + x pow 2) =
    x pow 14 * inv (&1 + x pow 2)
Proof
  `&0 <= x pow 2` by simp [POW_2, REAL_LE_SQUARE]
  >> `&1 + x pow 2 <> 0` by
    REAL_ASM_ARITH_TAC
  >> REAL_ASM_FIELD_TAC
QED

Theorem bounded_atan_lower_gap_derivative_positive:
  &0 < x ==>
  &0 < inv (&1 + x pow 2) -
    (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10)
Proof
  strip_tac
  >> rw [bounded_atan_lower_gap_derivative_identity]
  >> irule REAL_LT_MUL
  >> conj_tac
  >- (mp_tac (Q.SPECL [`x`, `11`] POW_POS_LT)
      >> simp [])
  >> irule REAL_INV_POS
  >> `&0 <= x pow 2` by simp [POW_2, REAL_LE_SQUARE]
  >> REAL_ASM_ARITH_TAC
QED

Theorem bounded_atan_upper_gap_derivative_positive:
  &0 < x ==>
  &0 < (&1 - x pow 2 + x pow 4 - x pow 6 + x pow 8 - x pow 10 +
    x pow 12) - inv (&1 + x pow 2)
Proof
  strip_tac
  >> rw [bounded_atan_upper_gap_derivative_identity]
  >> irule REAL_LT_MUL
  >> conj_tac
  >- (mp_tac (Q.SPECL [`x`, `13`] POW_POS_LT)
      >> simp [])
  >> irule REAL_INV_POS
  >> `&0 <= x pow 2` by simp [POW_2, REAL_LE_SQUARE]
  >> REAL_ASM_ARITH_TAC
QED

Theorem bounded_atan_lower_gap_contl_zero:
  (\x:real. atn x - bounded_atan_lower_real x) contl &0
Proof
  irule DIFF_CONT
  >> qexists_tac
       `inv (&1 + (&0) pow 2) -
          (&1 - (&0) pow 2 + (&0) pow 4 - (&0) pow 6 +
            (&0) pow 8 - (&0) pow 10)`
  >> MATCH_ACCEPT_TAC
       (Q.INST [`x` |-> `&0`] bounded_atan_lower_gap_diffl)
QED

Theorem bounded_atan_lower_gap_has_positive_derivative:
  &0 < z ==>
  ?l. &0 < l /\
    ((\x:real. atn x - bounded_atan_lower_real x) diffl l) z
Proof
  strip_tac
  >> qexists_tac
       `inv (&1 + z pow 2) -
          (&1 - z pow 2 + z pow 4 - z pow 6 + z pow 8 - z pow 10)`
  >> conj_tac
  >- (mp_tac
        (Q.INST [`x` |-> `z`]
          bounded_atan_lower_gap_derivative_positive)
      >> asm_rewrite_tac [])
  >> MATCH_ACCEPT_TAC
       (Q.INST [`x` |-> `z`] bounded_atan_lower_gap_diffl)
QED

Theorem bounded_atan_lower_gap_mono_from_zero:
  &0 <= x /\ x < y ==>
  atn x - bounded_atan_lower_real x <
    atn y - bounded_atan_lower_real y
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL
         [`\x:real. atn x - bounded_atan_lower_real x`, `&0`]
         DIFF_POS_MONO_LT_CU)
  >> impl_tac
  >- (conj_tac
      >- MATCH_ACCEPT_TAC bounded_atan_lower_gap_contl_zero
      >> gen_tac
      >> strip_tac
      >> mp_tac
           (Q.INST [`z` |-> `z`]
             bounded_atan_lower_gap_has_positive_derivative)
      >> asm_rewrite_tac [])
  >> disch_then (qspecl_then [`x`, `y`] mp_tac)
  >> simp []
QED

Theorem bounded_atan_lower_gap_positive:
  &0 < x ==> &0 < atn x - bounded_atan_lower_real x
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`x` |-> `&0`, `y` |-> `x`]
         bounded_atan_lower_gap_mono_from_zero)
  >> impl_tac >- REAL_ASM_ARITH_TAC
  >> simp [bounded_atan_zero, bounded_atan_lower_real_def]
QED

Theorem bounded_atan_upper_gap_contl_zero:
  (\x:real. bounded_atan_upper_real x - atn x) contl &0
Proof
  irule DIFF_CONT
  >> qexists_tac
       `(&1 - (&0) pow 2 + (&0) pow 4 - (&0) pow 6 +
           (&0) pow 8 - (&0) pow 10 + (&0) pow 12) -
          inv (&1 + (&0) pow 2)`
  >> MATCH_ACCEPT_TAC
       (Q.INST [`x` |-> `&0`] bounded_atan_upper_gap_diffl)
QED

Theorem bounded_atan_upper_gap_has_positive_derivative:
  &0 < z ==>
  ?l. &0 < l /\
    ((\x:real. bounded_atan_upper_real x - atn x) diffl l) z
Proof
  strip_tac
  >> qexists_tac
       `(&1 - z pow 2 + z pow 4 - z pow 6 + z pow 8 - z pow 10 +
           z pow 12) - inv (&1 + z pow 2)`
  >> conj_tac
  >- (mp_tac
        (Q.INST [`x` |-> `z`]
          bounded_atan_upper_gap_derivative_positive)
      >> asm_rewrite_tac [])
  >> MATCH_ACCEPT_TAC
       (Q.INST [`x` |-> `z`] bounded_atan_upper_gap_diffl)
QED

Theorem bounded_atan_upper_gap_mono_from_zero:
  &0 <= x /\ x < y ==>
  bounded_atan_upper_real x - atn x <
    bounded_atan_upper_real y - atn y
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL
         [`\x:real. bounded_atan_upper_real x - atn x`, `&0`]
         DIFF_POS_MONO_LT_CU)
  >> impl_tac
  >- (conj_tac
      >- MATCH_ACCEPT_TAC bounded_atan_upper_gap_contl_zero
      >> gen_tac
      >> strip_tac
      >> mp_tac
           (Q.INST [`z` |-> `z`]
             bounded_atan_upper_gap_has_positive_derivative)
      >> asm_rewrite_tac [])
  >> disch_then (qspecl_then [`x`, `y`] mp_tac)
  >> simp []
QED

Theorem bounded_atan_upper_gap_positive:
  &0 < x ==> &0 < bounded_atan_upper_real x - atn x
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`x` |-> `&0`, `y` |-> `x`]
         bounded_atan_upper_gap_mono_from_zero)
  >> impl_tac >- REAL_ASM_ARITH_TAC
  >> simp [bounded_atan_zero, bounded_atan_upper_real_def,
           bounded_atan_lower_real_def]
QED

Theorem bounded_atan_alternating_bounds_nonnegative:
  &0 <= x ==>
  bounded_atan_lower_real x <= atn x /\
  atn x <= bounded_atan_upper_real x
Proof
  strip_tac
  >> Cases_on `x = &0`
  >- simp [bounded_atan_zero, bounded_atan_lower_real_def,
           bounded_atan_upper_real_def]
  >> `&0 < x` by REAL_ASM_ARITH_TAC
  >> metis_tac
       [bounded_atan_lower_gap_positive,
        bounded_atan_upper_gap_positive,
        REAL_LT_IMP_LE,
        REAL_SUB_LT]
QED

val _ = export_theory ();
