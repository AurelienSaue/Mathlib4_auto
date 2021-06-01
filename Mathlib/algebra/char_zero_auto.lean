/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Natural homomorphism from the natural numbers into a monoid with one.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.cast
import Mathlib.data.fintype.basic
import Mathlib.tactic.wlog
import Mathlib.PostPort

universes u_1 l 

namespace Mathlib

/-- Typeclass for monoids with characteristic zero.
  (This is usually stated on fields but it makes sense for any additive monoid with 1.) -/
class char_zero (R : Type u_1) [add_monoid R] [HasOne R] where
  cast_injective : function.injective coe

theorem char_zero_of_inj_zero {R : Type u_1} [add_left_cancel_monoid R] [HasOne R]
    (H : ∀ (n : ℕ), ↑n = 0 → n = 0) : char_zero R :=
  sorry

protected instance linear_ordered_semiring.to_char_zero {R : Type u_1} [linear_ordered_semiring R] :
    char_zero R :=
  char_zero.mk (strict_mono.injective nat.strict_mono_cast)

namespace nat


theorem cast_injective {R : Type u_1} [add_monoid R] [HasOne R] [char_zero R] :
    function.injective coe :=
  char_zero.cast_injective

@[simp] theorem cast_inj {R : Type u_1} [add_monoid R] [HasOne R] [char_zero R] {m : ℕ} {n : ℕ} :
    ↑m = ↑n ↔ m = n :=
  function.injective.eq_iff cast_injective

@[simp] theorem cast_eq_zero {R : Type u_1} [add_monoid R] [HasOne R] [char_zero R] {n : ℕ} :
    ↑n = 0 ↔ n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n = 0 ↔ n = 0)) (Eq.symm cast_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n = ↑0 ↔ n = 0)) (propext cast_inj))) (iff.refl (n = 0)))

theorem cast_ne_zero {R : Type u_1} [add_monoid R] [HasOne R] [char_zero R] {n : ℕ} :
    ↑n ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero

theorem cast_add_one_ne_zero {R : Type u_1} [add_monoid R] [HasOne R] [char_zero R] (n : ℕ) :
    ↑n + 1 ≠ 0 :=
  sorry

@[simp] theorem cast_dvd_char_zero {k : Type u_1} [field k] [char_zero k] {m : ℕ} {n : ℕ}
    (n_dvd : n ∣ m) : ↑(m / n) = ↑m / ↑n :=
  sorry

end nat


protected instance char_zero.infinite (M : Type u_1) [add_monoid M] [HasOne M] [char_zero M] :
    infinite M :=
  infinite.of_injective coe nat.cast_injective

theorem two_ne_zero' {M : Type u_1} [add_monoid M] [HasOne M] [char_zero M] : bit0 1 ≠ 0 :=
  (fun (this : ↑(bit0 1) ≠ 0) => eq.mp (Eq._oldrec (Eq.refl (↑(bit0 1) ≠ 0)) nat.cast_two) this)
    (iff.mpr nat.cast_ne_zero (of_as_true trivial))

theorem add_self_eq_zero {R : Type u_1} [semiring R] [no_zero_divisors R] [char_zero R] {a : R} :
    a + a = 0 ↔ a = 0 :=
  sorry

theorem bit0_eq_zero {R : Type u_1} [semiring R] [no_zero_divisors R] [char_zero R] {a : R} :
    bit0 a = 0 ↔ a = 0 :=
  add_self_eq_zero

@[simp] theorem half_add_self {R : Type u_1} [division_ring R] [char_zero R] (a : R) :
    (a + a) / bit0 1 = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + a) / bit0 1 = a)) (Eq.symm (mul_two a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * bit0 1 / bit0 1 = a)) (mul_div_cancel a two_ne_zero')))
      (Eq.refl a))

@[simp] theorem add_halves' {R : Type u_1} [division_ring R] [char_zero R] (a : R) :
    a / bit0 1 + a / bit0 1 = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / bit0 1 + a / bit0 1 = a)) (Eq.symm (add_div a a (bit0 1)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((a + a) / bit0 1 = a)) (half_add_self a))) (Eq.refl a))

theorem sub_half {R : Type u_1} [division_ring R] [char_zero R] (a : R) :
    a - a / bit0 1 = a / bit0 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - a / bit0 1 = a / bit0 1)) (propext sub_eq_iff_eq_add)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = a / bit0 1 + a / bit0 1)) (add_halves' a))) (Eq.refl a))

theorem half_sub {R : Type u_1} [division_ring R] [char_zero R] (a : R) :
    a / bit0 1 - a = -(a / bit0 1) :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (a / bit0 1 - a = -(a / bit0 1))) (Eq.symm (neg_sub a (a / bit0 1)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-(a - a / bit0 1) = -(a / bit0 1))) (sub_half a)))
      (Eq.refl (-(a / bit0 1))))

namespace with_top


protected instance char_zero {R : Type u_1} [add_monoid R] [HasOne R] [char_zero R] :
    char_zero (with_top R) :=
  char_zero.mk
    fun (m n : ℕ) (h : ↑m = ↑n) =>
      eq.mp (Eq._oldrec (Eq.refl (↑m = ↑n)) (propext nat.cast_inj))
        (eq.mp (Eq._oldrec (Eq.refl (↑↑m = ↑↑n)) (propext coe_eq_coe))
          (eq.mp (Eq._oldrec (Eq.refl (↑↑m = ↑n)) (Eq.symm (coe_nat n)))
            (eq.mp (Eq._oldrec (Eq.refl (↑m = ↑n)) (Eq.symm (coe_nat m))) h)))

end Mathlib