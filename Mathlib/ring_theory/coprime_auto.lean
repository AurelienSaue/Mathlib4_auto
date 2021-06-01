/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.ring
import Mathlib.algebra.big_operators.basic
import Mathlib.data.fintype.basic
import Mathlib.data.int.gcd
import Mathlib.data.set.disjointed
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Coprime elements of a ring

## Main definitions

* `is_coprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.

-/

/-- The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime. -/
@[simp] def is_coprime {R : Type u} [comm_semiring R] (x : R) (y : R) :=
  ∃ (a : R), ∃ (b : R), a * x + b * y = 1

theorem nat.is_coprime_iff_coprime {m : ℕ} {n : ℕ} : is_coprime ↑m ↑n ↔ nat.coprime m n := sorry

theorem is_coprime.symm {R : Type u} [comm_semiring R] {x : R} {y : R} (H : is_coprime x y) :
    is_coprime y x :=
  sorry

theorem is_coprime_comm {R : Type u} [comm_semiring R] {x : R} {y : R} :
    is_coprime x y ↔ is_coprime y x :=
  { mp := is_coprime.symm, mpr := is_coprime.symm }

theorem is_coprime_self {R : Type u} [comm_semiring R] {x : R} : is_coprime x x ↔ is_unit x := sorry

theorem is_coprime_zero_left {R : Type u} [comm_semiring R] {x : R} : is_coprime 0 x ↔ is_unit x :=
  sorry

theorem is_coprime_zero_right {R : Type u} [comm_semiring R] {x : R} : is_coprime x 0 ↔ is_unit x :=
  iff.trans is_coprime_comm is_coprime_zero_left

theorem is_coprime_one_left {R : Type u} [comm_semiring R] {x : R} : is_coprime 1 x := sorry

theorem is_coprime_one_right {R : Type u} [comm_semiring R] {x : R} : is_coprime x 1 := sorry

theorem is_coprime.dvd_of_dvd_mul_right {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (H1 : is_coprime x z) (H2 : x ∣ y * z) : x ∣ y :=
  sorry

theorem is_coprime.dvd_of_dvd_mul_left {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (H1 : is_coprime x y) (H2 : x ∣ y * z) : x ∣ z :=
  sorry

theorem is_coprime.mul_left {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (H1 : is_coprime x z) (H2 : is_coprime y z) : is_coprime (x * y) z :=
  sorry

theorem is_coprime.mul_right {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (H1 : is_coprime x y) (H2 : is_coprime x z) : is_coprime x (y * z) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime x (y * z))) (propext is_coprime_comm)))
    (is_coprime.mul_left
      (eq.mp (Eq._oldrec (Eq.refl (is_coprime x y)) (propext is_coprime_comm)) H1)
      (eq.mp (Eq._oldrec (Eq.refl (is_coprime x z)) (propext is_coprime_comm)) H2))

theorem is_coprime.prod_left {R : Type u} [comm_semiring R] {x : R} {I : Type v} {s : I → R}
    {t : finset I} :
    (∀ (i : I), i ∈ t → is_coprime (s i) x) → is_coprime (finset.prod t fun (i : I) => s i) x :=
  sorry

theorem is_coprime.prod_right {R : Type u} [comm_semiring R] {x : R} {I : Type v} {s : I → R}
    {t : finset I} :
    (∀ (i : I), i ∈ t → is_coprime x (s i)) → is_coprime x (finset.prod t fun (i : I) => s i) :=
  sorry

theorem is_coprime.mul_dvd {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (H : is_coprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z :=
  sorry

theorem finset.prod_dvd_of_coprime {R : Type u} [comm_semiring R] {z : R} {I : Type v} {s : I → R}
    {t : finset I} (Hs : set.pairwise_on (↑t) (is_coprime on s))
    (Hs1 : ∀ (i : I), i ∈ t → s i ∣ z) : (finset.prod t fun (x : I) => s x) ∣ z :=
  sorry

theorem fintype.prod_dvd_of_coprime {R : Type u} [comm_semiring R] {z : R} {I : Type v} {s : I → R}
    [fintype I] (Hs : pairwise (is_coprime on s)) (Hs1 : ∀ (i : I), s i ∣ z) :
    (finset.prod finset.univ fun (x : I) => s x) ∣ z :=
  finset.prod_dvd_of_coprime (pairwise.pairwise_on Hs ↑finset.univ)
    fun (i : I) (_x : i ∈ finset.univ) => Hs1 i

theorem is_coprime.of_mul_left_left {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (H : is_coprime (x * y) z) : is_coprime x z :=
  sorry

theorem is_coprime.of_mul_left_right {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (H : is_coprime (x * y) z) : is_coprime y z :=
  is_coprime.of_mul_left_left (eq.mp (Eq._oldrec (Eq.refl (is_coprime (x * y) z)) (mul_comm x y)) H)

theorem is_coprime.of_mul_right_left {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (H : is_coprime x (y * z)) : is_coprime x y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime x y)) (propext is_coprime_comm)))
    (is_coprime.of_mul_left_left
      (eq.mp (Eq._oldrec (Eq.refl (is_coprime x (y * z))) (propext is_coprime_comm)) H))

theorem is_coprime.of_mul_right_right {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (H : is_coprime x (y * z)) : is_coprime x z :=
  is_coprime.of_mul_right_left
    (eq.mp (Eq._oldrec (Eq.refl (is_coprime x (y * z))) (mul_comm y z)) H)

theorem is_coprime.mul_left_iff {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R} :
    is_coprime (x * y) z ↔ is_coprime x z ∧ is_coprime y z :=
  sorry

theorem is_coprime.mul_right_iff {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R} :
    is_coprime x (y * z) ↔ is_coprime x y ∧ is_coprime x z :=
  sorry

theorem is_coprime.prod_left_iff {R : Type u} [comm_semiring R] {x : R} {I : Type v} {s : I → R}
    {t : finset I} :
    is_coprime (finset.prod t fun (i : I) => s i) x ↔ ∀ (i : I), i ∈ t → is_coprime (s i) x :=
  sorry

theorem is_coprime.prod_right_iff {R : Type u} [comm_semiring R] {x : R} {I : Type v} {s : I → R}
    {t : finset I} :
    is_coprime x (finset.prod t fun (i : I) => s i) ↔ ∀ (i : I), i ∈ t → is_coprime x (s i) :=
  sorry

theorem is_coprime.of_prod_left {R : Type u} [comm_semiring R] {x : R} {I : Type v} {s : I → R}
    {t : finset I} (H1 : is_coprime (finset.prod t fun (i : I) => s i) x) (i : I) (hit : i ∈ t) :
    is_coprime (s i) x :=
  iff.mp is_coprime.prod_left_iff H1 i hit

theorem is_coprime.of_prod_right {R : Type u} [comm_semiring R] {x : R} {I : Type v} {s : I → R}
    {t : finset I} (H1 : is_coprime x (finset.prod t fun (i : I) => s i)) (i : I) (hit : i ∈ t) :
    is_coprime x (s i) :=
  iff.mp is_coprime.prod_right_iff H1 i hit

theorem is_coprime.pow_left {R : Type u} [comm_semiring R] {x : R} {y : R} {m : ℕ}
    (H : is_coprime x y) : is_coprime (x ^ m) y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime (x ^ m) y)) (Eq.symm (finset.card_range m))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (is_coprime (x ^ finset.card (finset.range m)) y))
          (Eq.symm (finset.prod_const x))))
      (is_coprime.prod_left fun (_x : ℕ) (_x : _x ∈ finset.range m) => H))

theorem is_coprime.pow_right {R : Type u} [comm_semiring R] {x : R} {y : R} {n : ℕ}
    (H : is_coprime x y) : is_coprime x (y ^ n) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime x (y ^ n))) (Eq.symm (finset.card_range n))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (is_coprime x (y ^ finset.card (finset.range n))))
          (Eq.symm (finset.prod_const y))))
      (is_coprime.prod_right fun (_x : ℕ) (_x : _x ∈ finset.range n) => H))

theorem is_coprime.pow {R : Type u} [comm_semiring R] {x : R} {y : R} {m : ℕ} {n : ℕ}
    (H : is_coprime x y) : is_coprime (x ^ m) (y ^ n) :=
  is_coprime.pow_right (is_coprime.pow_left H)

theorem is_coprime.is_unit_of_dvd {R : Type u} [comm_semiring R] {x : R} {y : R}
    (H : is_coprime x y) (d : x ∣ y) : is_unit x :=
  sorry

theorem is_coprime.map {R : Type u} [comm_semiring R] {x : R} {y : R} (H : is_coprime x y)
    {S : Type v} [comm_semiring S] (f : R →+* S) : is_coprime (coe_fn f x) (coe_fn f y) :=
  sorry

theorem is_coprime.of_add_mul_left_left {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (h : is_coprime (x + y * z) y) : is_coprime x y :=
  sorry

theorem is_coprime.of_add_mul_right_left {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (h : is_coprime (x + z * y) y) : is_coprime x y :=
  is_coprime.of_add_mul_left_left
    (eq.mp (Eq._oldrec (Eq.refl (is_coprime (x + z * y) y)) (mul_comm z y)) h)

theorem is_coprime.of_add_mul_left_right {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (h : is_coprime x (y + x * z)) : is_coprime x y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime x y)) (propext is_coprime_comm)))
    (is_coprime.of_add_mul_left_left
      (eq.mp (Eq._oldrec (Eq.refl (is_coprime x (y + x * z))) (propext is_coprime_comm)) h))

theorem is_coprime.of_add_mul_right_right {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (h : is_coprime x (y + z * x)) : is_coprime x y :=
  is_coprime.of_add_mul_left_right
    (eq.mp (Eq._oldrec (Eq.refl (is_coprime x (y + z * x))) (mul_comm z x)) h)

theorem is_coprime.of_mul_add_left_left {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (h : is_coprime (y * z + x) y) : is_coprime x y :=
  is_coprime.of_add_mul_left_left
    (eq.mp (Eq._oldrec (Eq.refl (is_coprime (y * z + x) y)) (add_comm (y * z) x)) h)

theorem is_coprime.of_mul_add_right_left {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (h : is_coprime (z * y + x) y) : is_coprime x y :=
  is_coprime.of_add_mul_right_left
    (eq.mp (Eq._oldrec (Eq.refl (is_coprime (z * y + x) y)) (add_comm (z * y) x)) h)

theorem is_coprime.of_mul_add_left_right {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (h : is_coprime x (x * z + y)) : is_coprime x y :=
  is_coprime.of_add_mul_left_right
    (eq.mp (Eq._oldrec (Eq.refl (is_coprime x (x * z + y))) (add_comm (x * z) y)) h)

theorem is_coprime.of_mul_add_right_right {R : Type u} [comm_semiring R] {x : R} {y : R} {z : R}
    (h : is_coprime x (z * x + y)) : is_coprime x y :=
  is_coprime.of_add_mul_right_right
    (eq.mp (Eq._oldrec (Eq.refl (is_coprime x (z * x + y))) (add_comm (z * x) y)) h)

namespace is_coprime


theorem add_mul_left_left {R : Type u} [comm_ring R] {x : R} {y : R} (h : is_coprime x y) (z : R) :
    is_coprime (x + y * z) y :=
  sorry

theorem add_mul_right_left {R : Type u} [comm_ring R] {x : R} {y : R} (h : is_coprime x y) (z : R) :
    is_coprime (x + z * y) y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime (x + z * y) y)) (mul_comm z y)))
    (add_mul_left_left h z)

theorem add_mul_left_right {R : Type u} [comm_ring R] {x : R} {y : R} (h : is_coprime x y) (z : R) :
    is_coprime x (y + x * z) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime x (y + x * z))) (propext is_coprime_comm)))
    (add_mul_left_left (symm h) z)

theorem add_mul_right_right {R : Type u} [comm_ring R] {x : R} {y : R} (h : is_coprime x y)
    (z : R) : is_coprime x (y + z * x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime x (y + z * x))) (propext is_coprime_comm)))
    (add_mul_right_left (symm h) z)

theorem mul_add_left_left {R : Type u} [comm_ring R] {x : R} {y : R} (h : is_coprime x y) (z : R) :
    is_coprime (y * z + x) y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime (y * z + x) y)) (add_comm (y * z) x)))
    (add_mul_left_left h z)

theorem mul_add_right_left {R : Type u} [comm_ring R] {x : R} {y : R} (h : is_coprime x y) (z : R) :
    is_coprime (z * y + x) y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime (z * y + x) y)) (add_comm (z * y) x)))
    (add_mul_right_left h z)

theorem mul_add_left_right {R : Type u} [comm_ring R] {x : R} {y : R} (h : is_coprime x y) (z : R) :
    is_coprime x (x * z + y) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime x (x * z + y))) (add_comm (x * z) y)))
    (add_mul_left_right h z)

theorem mul_add_right_right {R : Type u} [comm_ring R] {x : R} {y : R} (h : is_coprime x y)
    (z : R) : is_coprime x (z * x + y) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_coprime x (z * x + y))) (add_comm (z * x) y)))
    (add_mul_right_right h z)

theorem add_mul_left_left_iff {R : Type u} [comm_ring R] {x : R} {y : R} {z : R} :
    is_coprime (x + y * z) y ↔ is_coprime x y :=
  { mp := of_add_mul_left_left, mpr := fun (h : is_coprime x y) => add_mul_left_left h z }

theorem add_mul_right_left_iff {R : Type u} [comm_ring R] {x : R} {y : R} {z : R} :
    is_coprime (x + z * y) y ↔ is_coprime x y :=
  { mp := of_add_mul_right_left, mpr := fun (h : is_coprime x y) => add_mul_right_left h z }

theorem add_mul_left_right_iff {R : Type u} [comm_ring R] {x : R} {y : R} {z : R} :
    is_coprime x (y + x * z) ↔ is_coprime x y :=
  { mp := of_add_mul_left_right, mpr := fun (h : is_coprime x y) => add_mul_left_right h z }

theorem add_mul_right_right_iff {R : Type u} [comm_ring R] {x : R} {y : R} {z : R} :
    is_coprime x (y + z * x) ↔ is_coprime x y :=
  { mp := of_add_mul_right_right, mpr := fun (h : is_coprime x y) => add_mul_right_right h z }

theorem mul_add_left_left_iff {R : Type u} [comm_ring R] {x : R} {y : R} {z : R} :
    is_coprime (y * z + x) y ↔ is_coprime x y :=
  { mp := of_mul_add_left_left, mpr := fun (h : is_coprime x y) => mul_add_left_left h z }

theorem mul_add_right_left_iff {R : Type u} [comm_ring R] {x : R} {y : R} {z : R} :
    is_coprime (z * y + x) y ↔ is_coprime x y :=
  { mp := of_mul_add_right_left, mpr := fun (h : is_coprime x y) => mul_add_right_left h z }

theorem mul_add_left_right_iff {R : Type u} [comm_ring R] {x : R} {y : R} {z : R} :
    is_coprime x (x * z + y) ↔ is_coprime x y :=
  { mp := of_mul_add_left_right, mpr := fun (h : is_coprime x y) => mul_add_left_right h z }

theorem mul_add_right_right_iff {R : Type u} [comm_ring R] {x : R} {y : R} {z : R} :
    is_coprime x (z * x + y) ↔ is_coprime x y :=
  { mp := of_mul_add_right_right, mpr := fun (h : is_coprime x y) => mul_add_right_right h z }

end Mathlib