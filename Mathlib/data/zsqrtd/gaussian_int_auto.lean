/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.zsqrtd.basic
import Mathlib.data.complex.basic
import Mathlib.ring_theory.principal_ideal_domain
import Mathlib.number_theory.quadratic_reciprocity
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Gaussian integers

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `to_complex` into the complex numbers is also defined in this file.

## Main statements

`prime_iff_mod_four_eq_three_of_nat_prime`
A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notations

This file uses the local notation `ℤ[i]` for `gaussian_int`

## Implementation notes

Gaussian integers are implemented using the more general definition `zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `zsqrtd` can easily be used.
-/

def gaussian_int := ℤ√(-1)

namespace gaussian_int


protected instance has_repr : has_repr gaussian_int :=
  has_repr.mk
    fun (x : gaussian_int) =>
      string.str string.empty
                (char.of_nat
                  (bit0
                    (bit0
                      (bit0
                        (bit1
                          (bit0 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit0 (bit0 1)))))))))))))) ++
              repr (zsqrtd.re x) ++
            string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit0 1)))))))
              (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))) ++
          repr (zsqrtd.im x) ++
        string.str string.empty
          (char.of_nat
            (bit1
              (bit0
                (bit0 (bit1 (bit0 (bit1 (bit1 (bit1 (bit1 (bit1 (bit1 (bit0 (bit0 1))))))))))))))

protected instance comm_ring : comm_ring gaussian_int := zsqrtd.comm_ring

/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
def to_complex : gaussian_int →+* ℂ := coe_fn zsqrtd.lift { val := complex.I, property := sorry }

protected instance complex.has_coe : has_coe gaussian_int ℂ := has_coe.mk ⇑to_complex

theorem to_complex_def (x : gaussian_int) : ↑x = ↑(zsqrtd.re x) + ↑(zsqrtd.im x) * complex.I := rfl

theorem to_complex_def' (x : ℤ) (y : ℤ) : ↑(zsqrtd.mk x y) = ↑x + ↑y * complex.I := sorry

theorem to_complex_def₂ (x : gaussian_int) : ↑x = complex.mk ↑(zsqrtd.re x) ↑(zsqrtd.im x) := sorry

@[simp] theorem to_real_re (x : gaussian_int) : ↑(zsqrtd.re x) = complex.re ↑x := sorry

@[simp] theorem to_real_im (x : gaussian_int) : ↑(zsqrtd.im x) = complex.im ↑x := sorry

@[simp] theorem to_complex_re (x : ℤ) (y : ℤ) : complex.re ↑(zsqrtd.mk x y) = ↑x := sorry

@[simp] theorem to_complex_im (x : ℤ) (y : ℤ) : complex.im ↑(zsqrtd.mk x y) = ↑y := sorry

@[simp] theorem to_complex_add (x : gaussian_int) (y : gaussian_int) : ↑(x + y) = ↑x + ↑y :=
  ring_hom.map_add to_complex x y

@[simp] theorem to_complex_mul (x : gaussian_int) (y : gaussian_int) : ↑(x * y) = ↑x * ↑y :=
  ring_hom.map_mul to_complex x y

@[simp] theorem to_complex_one : ↑1 = 1 := ring_hom.map_one to_complex

@[simp] theorem to_complex_zero : ↑0 = 0 := ring_hom.map_zero to_complex

@[simp] theorem to_complex_neg (x : gaussian_int) : ↑(-x) = -↑x := ring_hom.map_neg to_complex x

@[simp] theorem to_complex_sub (x : gaussian_int) (y : gaussian_int) : ↑(x - y) = ↑x - ↑y :=
  ring_hom.map_sub to_complex x y

@[simp] theorem to_complex_inj {x : gaussian_int} {y : gaussian_int} : ↑x = ↑y ↔ x = y := sorry

@[simp] theorem to_complex_eq_zero {x : gaussian_int} : ↑x = 0 ↔ x = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑x = 0 ↔ x = 0)) (Eq.symm to_complex_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑x = ↑0 ↔ x = 0)) (propext to_complex_inj)))
      (iff.refl (x = 0)))

@[simp] theorem nat_cast_real_norm (x : gaussian_int) :
    ↑(zsqrtd.norm x) = coe_fn complex.norm_sq ↑x :=
  sorry

@[simp] theorem nat_cast_complex_norm (x : gaussian_int) :
    ↑(zsqrtd.norm x) = ↑(coe_fn complex.norm_sq ↑x) :=
  sorry

theorem norm_nonneg (x : gaussian_int) : 0 ≤ zsqrtd.norm x :=
  zsqrtd.norm_nonneg
    (eq.mpr (id (eq_true_intro (neg_nonpos_of_nonneg (norm_num.nonneg_pos 1 zero_lt_one'))))
      trivial)
    x

@[simp] theorem norm_eq_zero {x : gaussian_int} : zsqrtd.norm x = 0 ↔ x = 0 := sorry

theorem norm_pos {x : gaussian_int} : 0 < zsqrtd.norm x ↔ x ≠ 0 := sorry

@[simp] theorem coe_nat_abs_norm (x : gaussian_int) :
    ↑(int.nat_abs (zsqrtd.norm x)) = zsqrtd.norm x :=
  int.nat_abs_of_nonneg (norm_nonneg x)

@[simp] theorem nat_cast_nat_abs_norm {α : Type u_1} [ring α] (x : gaussian_int) :
    ↑(int.nat_abs (zsqrtd.norm x)) = ↑(zsqrtd.norm x) :=
  sorry

theorem nat_abs_norm_eq (x : gaussian_int) :
    int.nat_abs (zsqrtd.norm x) =
        int.nat_abs (zsqrtd.re x) * int.nat_abs (zsqrtd.re x) +
          int.nat_abs (zsqrtd.im x) * int.nat_abs (zsqrtd.im x) :=
  sorry

protected def div (x : gaussian_int) (y : gaussian_int) : gaussian_int :=
  let n : ℚ := rat.of_int (zsqrtd.norm y)⁻¹;
  let c : ℤ√(-1) := zsqrtd.conj y;
  zsqrtd.mk (round (rat.of_int (zsqrtd.re (x * c)) * n))
    (round (rat.of_int (zsqrtd.im (x * c)) * n))

protected instance has_div : Div gaussian_int := { div := gaussian_int.div }

theorem div_def (x : gaussian_int) (y : gaussian_int) :
    x / y =
        zsqrtd.mk (round (↑(zsqrtd.re (x * zsqrtd.conj y)) / ↑(zsqrtd.norm y)))
          (round (↑(zsqrtd.im (x * zsqrtd.conj y)) / ↑(zsqrtd.norm y))) :=
  sorry

theorem to_complex_div_re (x : gaussian_int) (y : gaussian_int) :
    complex.re ↑(x / y) = ↑(round (complex.re (↑x / ↑y))) :=
  sorry

theorem to_complex_div_im (x : gaussian_int) (y : gaussian_int) :
    complex.im ↑(x / y) = ↑(round (complex.im (↑x / ↑y))) :=
  sorry

theorem norm_sq_le_norm_sq_of_re_le_of_im_le {x : ℂ} {y : ℂ}
    (hre : abs (complex.re x) ≤ abs (complex.re y))
    (him : abs (complex.im x) ≤ abs (complex.im y)) :
    coe_fn complex.norm_sq x ≤ coe_fn complex.norm_sq y :=
  sorry

theorem norm_sq_div_sub_div_lt_one (x : gaussian_int) (y : gaussian_int) :
    coe_fn complex.norm_sq (↑x / ↑y - ↑(x / y)) < 1 :=
  sorry

protected def mod (x : gaussian_int) (y : gaussian_int) : gaussian_int := x - y * (x / y)

protected instance has_mod : Mod gaussian_int := { mod := gaussian_int.mod }

theorem mod_def (x : gaussian_int) (y : gaussian_int) : x % y = x - y * (x / y) := rfl

theorem norm_mod_lt (x : gaussian_int) {y : gaussian_int} (hy : y ≠ 0) :
    zsqrtd.norm (x % y) < zsqrtd.norm y :=
  sorry

theorem nat_abs_norm_mod_lt (x : gaussian_int) {y : gaussian_int} (hy : y ≠ 0) :
    int.nat_abs (zsqrtd.norm (x % y)) < int.nat_abs (zsqrtd.norm y) :=
  sorry

theorem norm_le_norm_mul_left (x : gaussian_int) {y : gaussian_int} (hy : y ≠ 0) :
    int.nat_abs (zsqrtd.norm x) ≤ int.nat_abs (zsqrtd.norm (x * y)) :=
  sorry

protected instance nontrivial : nontrivial gaussian_int :=
  nontrivial.mk (Exists.intro 0 (Exists.intro 1 (of_as_true trivial)))

protected instance euclidean_domain : euclidean_domain gaussian_int :=
  euclidean_domain.mk comm_ring.add comm_ring.add_assoc comm_ring.zero comm_ring.zero_add
    comm_ring.add_zero comm_ring.neg comm_ring.sub comm_ring.add_left_neg comm_ring.add_comm
    comm_ring.mul comm_ring.mul_assoc comm_ring.one comm_ring.one_mul comm_ring.mul_one
    comm_ring.left_distrib comm_ring.right_distrib comm_ring.mul_comm nontrivial.exists_pair_ne
    Div.div sorry Mod.mod sorry (measure (int.nat_abs ∘ zsqrtd.norm)) sorry nat_abs_norm_mod_lt
    sorry

theorem mod_four_eq_three_of_nat_prime_of_prime (p : ℕ) [hp : fact (nat.prime p)] (hpi : prime ↑p) :
    p % bit0 (bit0 1) = bit1 1 :=
  sorry

theorem sum_two_squares_of_nat_prime_of_not_irreducible (p : ℕ) [hp : fact (nat.prime p)]
    (hpi : ¬irreducible ↑p) : ∃ (a : ℕ), ∃ (b : ℕ), a ^ bit0 1 + b ^ bit0 1 = p :=
  sorry

theorem prime_of_nat_prime_of_mod_four_eq_three (p : ℕ) [hp : fact (nat.prime p)]
    (hp3 : p % bit0 (bit0 1) = bit1 1) : prime ↑p :=
  sorry

/-- A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4` -/
theorem prime_iff_mod_four_eq_three_of_nat_prime (p : ℕ) [hp : fact (nat.prime p)] :
    prime ↑p ↔ p % bit0 (bit0 1) = bit1 1 :=
  { mp := mod_four_eq_three_of_nat_prime_of_prime p,
    mpr := prime_of_nat_prime_of_mod_four_eq_three p }

end Mathlib