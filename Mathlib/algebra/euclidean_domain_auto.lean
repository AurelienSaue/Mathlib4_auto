/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro

Euclidean domains and Euclidean algorithm (extended to come)
A lot is based on pre-existing code in mathlib for natural number gcds
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.int.basic
import Mathlib.algebra.field
import Mathlib.PostPort

universes u l u_1 

namespace Mathlib

/-- A `euclidean_domain` is an `integral_domain` with a division and a remainder, satisfying
  `b * (a / b) + a % b = a`. The definition of a euclidean domain usually includes a valuation
  function `R → ℕ`. This definition is slightly generalised to include a well founded relation
  `r` with the property that `r (a % b) b`, instead of a valuation.  -/
class euclidean_domain (R : Type u) extends comm_ring R, nontrivial R where
  quotient : R → R → R
  quotient_zero : ∀ (a : R), quotient a 0 = 0
  remainder : R → R → R
  quotient_mul_add_remainder_eq : ∀ (a b : R), b * quotient a b + remainder a b = a
  r : R → R → Prop
  r_well_founded : well_founded r
  remainder_lt : ∀ (a : R) {b : R}, b ≠ 0 → r (remainder a b) b
  mul_left_not_lt : ∀ (a : R) {b : R}, b ≠ 0 → ¬r (a * b) a

namespace euclidean_domain


protected instance has_div {R : Type u} [euclidean_domain R] : Div R :=
  { div := euclidean_domain.quotient }

protected instance has_mod {R : Type u} [euclidean_domain R] : Mod R :=
  { mod := euclidean_domain.remainder }

theorem div_add_mod {R : Type u} [euclidean_domain R] (a : R) (b : R) : b * (a / b) + a % b = a :=
  euclidean_domain.quotient_mul_add_remainder_eq a b

theorem mod_add_div {R : Type u} [euclidean_domain R] (a : R) (b : R) : a % b + b * (a / b) = a :=
  Eq.trans (add_comm (a % b) (b * (a / b))) (div_add_mod a b)

theorem mod_eq_sub_mul_div {R : Type u_1} [euclidean_domain R] (a : R) (b : R) :
    a % b = a - b * (a / b) :=
  Eq.trans (Eq.symm (add_sub_cancel' (b * (a / b)) (a % b)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (b * (a / b) + a % b - b * (a / b) = a - b * (a / b)))
          (div_add_mod a b)))
      (Eq.refl (a - b * (a / b))))

theorem mod_lt {R : Type u} [euclidean_domain R] (a : R) {b : R} :
    b ≠ 0 → euclidean_domain.r (a % b) b :=
  euclidean_domain.remainder_lt

theorem mul_right_not_lt {R : Type u} [euclidean_domain R] {a : R} (b : R) (h : a ≠ 0) :
    ¬euclidean_domain.r (a * b) b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬euclidean_domain.r (a * b) b)) (mul_comm a b)))
    (mul_left_not_lt b h)

theorem mul_div_cancel_left {R : Type u} [euclidean_domain R] {a : R} (b : R) (a0 : a ≠ 0) :
    a * b / a = b :=
  sorry

theorem mul_div_cancel {R : Type u} [euclidean_domain R] (a : R) {b : R} (b0 : b ≠ 0) :
    a * b / b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b / b = a)) (mul_comm a b))) (mul_div_cancel_left a b0)

@[simp] theorem mod_zero {R : Type u} [euclidean_domain R] (a : R) : a % 0 = a := sorry

@[simp] theorem mod_eq_zero {R : Type u} [euclidean_domain R] {a : R} {b : R} : a % b = 0 ↔ b ∣ a :=
  sorry

@[simp] theorem mod_self {R : Type u} [euclidean_domain R] (a : R) : a % a = 0 :=
  iff.mpr mod_eq_zero (dvd_refl a)

theorem dvd_mod_iff {R : Type u} [euclidean_domain R] {a : R} {b : R} {c : R} (h : c ∣ b) :
    c ∣ a % b ↔ c ∣ a :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (c ∣ a % b ↔ c ∣ a))
        (propext (dvd_add_iff_right (dvd_mul_of_dvd_left h (a / b))))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (c ∣ b * (a / b) + a % b ↔ c ∣ a)) (div_add_mod a b)))
      (iff.refl (c ∣ a)))

theorem lt_one {R : Type u} [euclidean_domain R] (a : R) : euclidean_domain.r a 1 → a = 0 := sorry

theorem val_dvd_le {R : Type u} [euclidean_domain R] (a : R) (b : R) :
    b ∣ a → a ≠ 0 → ¬euclidean_domain.r a b :=
  sorry

@[simp] theorem mod_one {R : Type u} [euclidean_domain R] (a : R) : a % 1 = 0 :=
  iff.mpr mod_eq_zero (one_dvd a)

@[simp] theorem zero_mod {R : Type u} [euclidean_domain R] (b : R) : 0 % b = 0 :=
  iff.mpr mod_eq_zero (dvd_zero b)

@[simp] theorem div_zero {R : Type u} [euclidean_domain R] (a : R) : a / 0 = 0 :=
  euclidean_domain.quotient_zero a

@[simp] theorem zero_div {R : Type u} [euclidean_domain R] {a : R} : 0 / a = 0 := sorry

@[simp] theorem div_self {R : Type u} [euclidean_domain R] {a : R} (a0 : a ≠ 0) : a / a = 1 := sorry

theorem eq_div_of_mul_eq_left {R : Type u} [euclidean_domain R] {a : R} {b : R} {c : R} (hb : b ≠ 0)
    (h : a * b = c) : a = c / b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = c / b)) (Eq.symm h)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = a * b / b)) (mul_div_cancel a hb))) (Eq.refl a))

theorem eq_div_of_mul_eq_right {R : Type u} [euclidean_domain R] {a : R} {b : R} {c : R}
    (ha : a ≠ 0) (h : a * b = c) : b = c / a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b = c / a)) (Eq.symm h)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b = a * b / a)) (mul_div_cancel_left b ha))) (Eq.refl b))

theorem mul_div_assoc {R : Type u} [euclidean_domain R] (x : R) {y : R} {z : R} (h : z ∣ y) :
    x * y / z = x * (y / z) :=
  sorry

theorem gcd.induction {R : Type u} [euclidean_domain R] {P : R → R → Prop} (a : R) (b : R) :
    (∀ (x : R), P 0 x) → (∀ (a b : R), a ≠ 0 → P (b % a) a → P a b) → P a b :=
  sorry

/-- `gcd a b` is a (non-unique) element such that `gcd a b ∣ a` `gcd a b ∣ b`, and for
  any element `c` such that `c ∣ a` and `c ∣ b`, then `c ∣ gcd a b` -/
def gcd {R : Type u} [euclidean_domain R] [DecidableEq R] : R → R → R := sorry

@[simp] theorem gcd_zero_left {R : Type u} [euclidean_domain R] [DecidableEq R] (a : R) :
    gcd 0 a = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (gcd 0 a = a)) (gcd.equations._eqn_1 0))) (if_pos rfl)

@[simp] theorem gcd_zero_right {R : Type u} [euclidean_domain R] [DecidableEq R] (a : R) :
    gcd a 0 = a :=
  sorry

theorem gcd_val {R : Type u} [euclidean_domain R] [DecidableEq R] (a : R) (b : R) :
    gcd a b = gcd (b % a) a :=
  sorry

theorem gcd_dvd {R : Type u} [euclidean_domain R] [DecidableEq R] (a : R) (b : R) :
    gcd a b ∣ a ∧ gcd a b ∣ b :=
  sorry

theorem gcd_dvd_left {R : Type u} [euclidean_domain R] [DecidableEq R] (a : R) (b : R) :
    gcd a b ∣ a :=
  and.left (gcd_dvd a b)

theorem gcd_dvd_right {R : Type u} [euclidean_domain R] [DecidableEq R] (a : R) (b : R) :
    gcd a b ∣ b :=
  and.right (gcd_dvd a b)

protected theorem gcd_eq_zero_iff {R : Type u} [euclidean_domain R] [DecidableEq R] {a : R}
    {b : R} : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  sorry

theorem dvd_gcd {R : Type u} [euclidean_domain R] [DecidableEq R] {a : R} {b : R} {c : R} :
    c ∣ a → c ∣ b → c ∣ gcd a b :=
  sorry

theorem gcd_eq_left {R : Type u} [euclidean_domain R] [DecidableEq R] {a : R} {b : R} :
    gcd a b = a ↔ a ∣ b :=
  sorry

@[simp] theorem gcd_one_left {R : Type u} [euclidean_domain R] [DecidableEq R] (a : R) :
    gcd 1 a = 1 :=
  iff.mpr gcd_eq_left (one_dvd a)

@[simp] theorem gcd_self {R : Type u} [euclidean_domain R] [DecidableEq R] (a : R) : gcd a a = a :=
  iff.mpr gcd_eq_left (dvd_refl a)

/--
An implementation of the extended GCD algorithm.
At each step we are computing a triple `(r, s, t)`, where `r` is the next value of the GCD
algorithm, to compute the greatest common divisor of the input (say `x` and `y`), and `s` and `t`
are the coefficients in front of `x` and `y` to obtain `r` (i.e. `r = s * x + t * y`).
The function `xgcd_aux` takes in two triples, and from these recursively computes the next triple:
```
xgcd_aux (r, s, t) (r', s', t') = xgcd_aux (r' % r, s' - (r' / r) * s, t' - (r' / r) * t) (r, s, t)
```
-/
def xgcd_aux {R : Type u} [euclidean_domain R] [DecidableEq R] :
    R → R → R → R → R → R → R × R × R :=
  sorry

@[simp] theorem xgcd_zero_left {R : Type u} [euclidean_domain R] [DecidableEq R] {s : R} {t : R}
    {r' : R} {s' : R} {t' : R} : xgcd_aux 0 s t r' s' t' = (r', s', t') :=
  sorry

theorem xgcd_aux_rec {R : Type u} [euclidean_domain R] [DecidableEq R] {r : R} {s : R} {t : R}
    {r' : R} {s' : R} {t' : R} (h : r ≠ 0) :
    xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t :=
  sorry

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) (y : R) : R × R :=
  prod.snd (xgcd_aux x 1 0 y 0 1)

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_a {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) (y : R) : R :=
  prod.fst (xgcd x y)

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_b {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) (y : R) : R :=
  prod.snd (xgcd x y)

@[simp] theorem gcd_a_zero_left {R : Type u} [euclidean_domain R] [DecidableEq R] {s : R} :
    gcd_a 0 s = 0 :=
  sorry

@[simp] theorem gcd_b_zero_left {R : Type u} [euclidean_domain R] [DecidableEq R] {s : R} :
    gcd_b 0 s = 1 :=
  sorry

@[simp] theorem xgcd_aux_fst {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) (y : R)
    (s : R) (t : R) (s' : R) (t' : R) : prod.fst (xgcd_aux x s t y s' t') = gcd x y :=
  sorry

theorem xgcd_aux_val {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) (y : R) :
    xgcd_aux x 1 0 y 0 1 = (gcd x y, xgcd x y) :=
  sorry

theorem xgcd_val {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) (y : R) :
    xgcd x y = (gcd_a x y, gcd_b x y) :=
  Eq.symm prod.mk.eta

theorem xgcd_aux_P {R : Type u} [euclidean_domain R] [DecidableEq R] (a : R) (b : R) {r : R}
    {r' : R} {s : R} {t : R} {s' : R} {t' : R} :
    P a b (r, s, t) → P a b (r', s', t') → P a b (xgcd_aux r s t r' s' t') :=
  sorry

theorem gcd_eq_gcd_ab {R : Type u} [euclidean_domain R] [DecidableEq R] (a : R) (b : R) :
    gcd a b = a * gcd_a a b + b * gcd_b a b :=
  sorry

protected instance integral_domain (R : Type u_1) [e : euclidean_domain R] : integral_domain R :=
  integral_domain.mk Add.add euclidean_domain.add_assoc 0 euclidean_domain.zero_add
    euclidean_domain.add_zero euclidean_domain.neg euclidean_domain.sub
    euclidean_domain.add_left_neg euclidean_domain.add_comm Mul.mul euclidean_domain.mul_assoc
    euclidean_domain.one euclidean_domain.one_mul euclidean_domain.mul_one
    euclidean_domain.left_distrib euclidean_domain.right_distrib euclidean_domain.mul_comm
    euclidean_domain.exists_pair_ne sorry

/-- `lcm a b` is a (non-unique) element such that `a ∣ lcm a b` `b ∣ lcm a b`, and for
  any element `c` such that `a ∣ c` and `b ∣ c`, then `lcm a b ∣ c` -/
def lcm {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) (y : R) : R := x * y / gcd x y

theorem dvd_lcm_left {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) (y : R) :
    x ∣ lcm x y :=
  sorry

theorem dvd_lcm_right {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) (y : R) :
    y ∣ lcm x y :=
  sorry

theorem lcm_dvd {R : Type u} [euclidean_domain R] [DecidableEq R] {x : R} {y : R} {z : R}
    (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z :=
  sorry

@[simp] theorem lcm_dvd_iff {R : Type u} [euclidean_domain R] [DecidableEq R] {x : R} {y : R}
    {z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z :=
  sorry

@[simp] theorem lcm_zero_left {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) :
    lcm 0 x = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lcm 0 x = 0)) (lcm.equations._eqn_1 0 x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 * x / gcd 0 x = 0)) (zero_mul x)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 / gcd 0 x = 0)) zero_div)) (Eq.refl 0)))

@[simp] theorem lcm_zero_right {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) :
    lcm x 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lcm x 0 = 0)) (lcm.equations._eqn_1 x 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x * 0 / gcd x 0 = 0)) (mul_zero x)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 / gcd x 0 = 0)) zero_div)) (Eq.refl 0)))

@[simp] theorem lcm_eq_zero_iff {R : Type u} [euclidean_domain R] [DecidableEq R] {x : R} {y : R} :
    lcm x y = 0 ↔ x = 0 ∨ y = 0 :=
  sorry

@[simp] theorem gcd_mul_lcm {R : Type u} [euclidean_domain R] [DecidableEq R] (x : R) (y : R) :
    gcd x y * lcm x y = x * y :=
  sorry

end euclidean_domain


protected instance int.euclidean_domain : euclidean_domain ℤ :=
  euclidean_domain.mk Add.add comm_ring.add_assoc 0 comm_ring.zero_add comm_ring.add_zero Neg.neg
    comm_ring.sub comm_ring.add_left_neg comm_ring.add_comm Mul.mul comm_ring.mul_assoc 1
    comm_ring.one_mul comm_ring.mul_one comm_ring.left_distrib comm_ring.right_distrib
    comm_ring.mul_comm nontrivial.exists_pair_ne Div.div int.div_zero Mod.mod sorry
    (fun (a b : ℤ) => int.nat_abs a < int.nat_abs b) sorry sorry sorry

protected instance field.to_euclidean_domain {K : Type u} [field K] : euclidean_domain K :=
  euclidean_domain.mk Add.add field.add_assoc 0 field.zero_add field.add_zero Neg.neg field.sub
    field.add_left_neg field.add_comm Mul.mul field.mul_assoc 1 field.one_mul field.mul_one
    field.left_distrib field.right_distrib field.mul_comm field.exists_pair_ne Div.div sorry
    (fun (a b : K) => a - a * b / b) sorry (fun (a b : K) => a = 0 ∧ b ≠ 0) sorry sorry sorry

end Mathlib