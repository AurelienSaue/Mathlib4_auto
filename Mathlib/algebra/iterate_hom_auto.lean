/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group_power.default
import Mathlib.logic.function.iterate
import PostPort

universes u_1 u_3 u_5 

namespace Mathlib

/-!
# Iterates of monoid and ring homomorphisms

Iterate of a monoid/ring homomorphism is a monoid/ring homomorphism but it has a wrong type, so Lean
can't apply lemmas like `monoid_hom.map_one` to `f^[n] 1`. Though it is possible to define
a monoid structure on the endomorphisms, quite often we do not want to convert from
`M →* M` to (not yet defined) `monoid.End M` and from `f^[n]` to `f^n` just to apply a simple lemma.

So, we restate standard `*_hom.map_*` lemmas under names `*_hom.iterate_map_*`.

We also prove formulas for iterates of add/mul left/right.

## Tags

homomorphism, iterate
-/

namespace monoid_hom


@[simp] theorem Mathlib.add_monoid_hom.iterate_map_zero {M : Type u_1} [add_monoid M] (f : M →+ M) (n : ℕ) : nat.iterate (⇑f) n 0 = 0 :=
  function.iterate_fixed (add_monoid_hom.map_zero f) n

@[simp] theorem iterate_map_mul {M : Type u_1} [monoid M] (f : M →* M) (n : ℕ) (x : M) (y : M) : nat.iterate (⇑f) n (x * y) = nat.iterate (⇑f) n x * nat.iterate (⇑f) n y :=
  function.semiconj₂.iterate (map_mul f) n x y

@[simp] theorem iterate_map_inv {G : Type u_3} [group G] (f : G →* G) (n : ℕ) (x : G) : nat.iterate (⇑f) n (x⁻¹) = (nat.iterate (⇑f) n x⁻¹) :=
  function.commute.iterate_left (map_inv f) n x

theorem iterate_map_pow {M : Type u_1} [monoid M] (f : M →* M) (a : M) (n : ℕ) (m : ℕ) : nat.iterate (⇑f) n (a ^ m) = nat.iterate (⇑f) n a ^ m :=
  function.commute.iterate_left (fun (x : M) => map_pow f x m) n a

theorem iterate_map_gpow {G : Type u_3} [group G] (f : G →* G) (a : G) (n : ℕ) (m : ℤ) : nat.iterate (⇑f) n (a ^ m) = nat.iterate (⇑f) n a ^ m :=
  function.commute.iterate_left (fun (x : G) => map_gpow f x m) n a

end monoid_hom


namespace add_monoid_hom


@[simp] theorem iterate_map_sub {G : Type u_3} [add_group G] (f : G →+ G) (n : ℕ) (x : G) (y : G) : nat.iterate (⇑f) n (x - y) = nat.iterate (⇑f) n x - nat.iterate (⇑f) n y :=
  function.semiconj₂.iterate (map_sub f) n x y

theorem iterate_map_smul {M : Type u_1} [add_monoid M] (f : M →+ M) (n : ℕ) (m : ℕ) (x : M) : nat.iterate (⇑f) n (m •ℕ x) = m •ℕ nat.iterate (⇑f) n x :=
  monoid_hom.iterate_map_pow (coe_fn to_multiplicative f) x n m

theorem iterate_map_gsmul {G : Type u_3} [add_group G] (f : G →+ G) (n : ℕ) (m : ℤ) (x : G) : nat.iterate (⇑f) n (m •ℤ x) = m •ℤ nat.iterate (⇑f) n x :=
  monoid_hom.iterate_map_gpow (coe_fn to_multiplicative f) x n m

end add_monoid_hom


namespace ring_hom


theorem coe_pow {R : Type u_5} [semiring R] (f : R →+* R) (n : ℕ) : ⇑(f ^ n) = nat.iterate (⇑f) n := sorry

theorem iterate_map_one {R : Type u_5} [semiring R] (f : R →+* R) (n : ℕ) : nat.iterate (⇑f) n 1 = 1 :=
  monoid_hom.iterate_map_one (to_monoid_hom f) n

theorem iterate_map_zero {R : Type u_5} [semiring R] (f : R →+* R) (n : ℕ) : nat.iterate (⇑f) n 0 = 0 :=
  add_monoid_hom.iterate_map_zero (to_add_monoid_hom f) n

theorem iterate_map_add {R : Type u_5} [semiring R] (f : R →+* R) (n : ℕ) (x : R) (y : R) : nat.iterate (⇑f) n (x + y) = nat.iterate (⇑f) n x + nat.iterate (⇑f) n y :=
  add_monoid_hom.iterate_map_add (to_add_monoid_hom f) n x y

theorem iterate_map_mul {R : Type u_5} [semiring R] (f : R →+* R) (n : ℕ) (x : R) (y : R) : nat.iterate (⇑f) n (x * y) = nat.iterate (⇑f) n x * nat.iterate (⇑f) n y :=
  monoid_hom.iterate_map_mul (to_monoid_hom f) n x y

theorem iterate_map_pow {R : Type u_5} [semiring R] (f : R →+* R) (a : R) (n : ℕ) (m : ℕ) : nat.iterate (⇑f) n (a ^ m) = nat.iterate (⇑f) n a ^ m :=
  monoid_hom.iterate_map_pow (to_monoid_hom f) a n m

theorem iterate_map_smul {R : Type u_5} [semiring R] (f : R →+* R) (n : ℕ) (m : ℕ) (x : R) : nat.iterate (⇑f) n (m •ℕ x) = m •ℕ nat.iterate (⇑f) n x :=
  add_monoid_hom.iterate_map_smul (to_add_monoid_hom f) n m x

theorem iterate_map_sub {R : Type u_5} [ring R] (f : R →+* R) (n : ℕ) (x : R) (y : R) : nat.iterate (⇑f) n (x - y) = nat.iterate (⇑f) n x - nat.iterate (⇑f) n y :=
  add_monoid_hom.iterate_map_sub (to_add_monoid_hom f) n x y

theorem iterate_map_neg {R : Type u_5} [ring R] (f : R →+* R) (n : ℕ) (x : R) : nat.iterate (⇑f) n (-x) = -nat.iterate (⇑f) n x :=
  add_monoid_hom.iterate_map_neg (to_add_monoid_hom f) n x

theorem iterate_map_gsmul {R : Type u_5} [ring R] (f : R →+* R) (n : ℕ) (m : ℤ) (x : R) : nat.iterate (⇑f) n (m •ℤ x) = m •ℤ nat.iterate (⇑f) n x :=
  add_monoid_hom.iterate_map_gsmul (to_add_monoid_hom f) n m x

end ring_hom


@[simp] theorem mul_left_iterate {M : Type u_1} [monoid M] (a : M) (n : ℕ) : nat.iterate (Mul.mul a) n = Mul.mul (a ^ n) := sorry

@[simp] theorem add_left_iterate {M : Type u_1} [add_monoid M] (a : M) (n : ℕ) : nat.iterate (Add.add a) n = Add.add (n •ℕ a) :=
  mul_left_iterate a n

@[simp] theorem mul_right_iterate {M : Type u_1} [monoid M] (a : M) (n : ℕ) : nat.iterate (fun (x : M) => x * a) n = fun (x : M) => x * a ^ n := sorry

@[simp] theorem add_right_iterate {M : Type u_1} [add_monoid M] (a : M) (n : ℕ) : nat.iterate (fun (x : M) => x + a) n = fun (x : M) => x + n •ℕ a :=
  mul_right_iterate a n

