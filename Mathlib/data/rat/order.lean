/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.rat.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# Order for Rational Numbers

## Summary

We define the order on `ℚ`, prove that `ℚ` is a discrete, linearly ordered field, and define
functions such as `abs` and `sqrt` that depend on this order.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering, sqrt, abs
-/

namespace rat


protected def nonneg : ℚ → Prop :=
  sorry

@[simp] theorem mk_nonneg (a : ℤ) {b : ℤ} (h : 0 < b) : rat.nonneg (mk a b) ↔ 0 ≤ a := sorry

protected theorem nonneg_add {a : ℚ} {b : ℚ} : rat.nonneg a → rat.nonneg b → rat.nonneg (a + b) := sorry

protected theorem nonneg_mul {a : ℚ} {b : ℚ} : rat.nonneg a → rat.nonneg b → rat.nonneg (a * b) := sorry

protected theorem nonneg_antisymm {a : ℚ} : rat.nonneg a → rat.nonneg (-a) → a = 0 := sorry

protected theorem nonneg_total (a : ℚ) : rat.nonneg a ∨ rat.nonneg (-a) :=
  cases_on a
    fun (n : ℤ) (a_denom : ℕ) (a_pos : 0 < a_denom) (a_cop : nat.coprime (int.nat_abs n) a_denom) =>
      or.imp_right neg_nonneg_of_nonpos (le_total 0 n)

protected instance decidable_nonneg (a : ℚ) : Decidable (rat.nonneg a) :=
  cases_on a
    fun (a_num : ℤ) (a_denom : ℕ) (a_pos : 0 < a_denom) (a_cop : nat.coprime (int.nat_abs a_num) a_denom) =>
      eq.mpr sorry (int.decidable_le 0 a_num)

protected def le (a : ℚ) (b : ℚ) :=
  rat.nonneg (b - a)

protected instance has_le : HasLessEq ℚ :=
  { LessEq := rat.le }

protected instance decidable_le : DecidableRel LessEq :=
  sorry

protected theorem le_def {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (b0 : 0 < b) (d0 : 0 < d) : mk a b ≤ mk c d ↔ a * d ≤ c * b := sorry

protected theorem le_refl (a : ℚ) : a ≤ a :=
  (fun (this : rat.nonneg (a - a)) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (rat.nonneg (a - a))) (sub_self a))) (le_refl 0))

protected theorem le_total (a : ℚ) (b : ℚ) : a ≤ b ∨ b ≤ a :=
  eq.mp (Eq._oldrec (Eq.refl (rat.nonneg (b - a) ∨ rat.nonneg (-(b - a)))) (neg_sub b a)) (rat.nonneg_total (b - a))

protected theorem le_antisymm {a : ℚ} {b : ℚ} (hab : a ≤ b) (hba : b ≤ a) : a = b := sorry

protected theorem le_trans {a : ℚ} {b : ℚ} {c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := sorry

protected instance linear_order : linear_order ℚ :=
  linear_order.mk rat.le (partial_order.lt._default rat.le) rat.le_refl rat.le_trans rat.le_antisymm rat.le_total
    (fun (a b : ℚ) => rat.decidable_nonneg (b - a)) (fun (a b : ℚ) => rat.decidable_eq a b)
    Mathlib.decidable_lt_of_decidable_le

/- Extra instances to short-circuit type class resolution -/

protected instance has_lt : HasLess ℚ :=
  preorder.to_has_lt ℚ

protected instance distrib_lattice : distrib_lattice ℚ :=
  Mathlib.distrib_lattice_of_linear_order

protected instance lattice : lattice ℚ :=
  Mathlib.lattice_of_linear_order

protected instance semilattice_inf : semilattice_inf ℚ :=
  lattice.to_semilattice_inf ℚ

protected instance semilattice_sup : semilattice_sup ℚ :=
  lattice.to_semilattice_sup ℚ

protected instance has_inf : has_inf ℚ :=
  semilattice_inf.to_has_inf ℚ

protected instance has_sup : has_sup ℚ :=
  semilattice_sup.to_has_sup ℚ

protected instance partial_order : partial_order ℚ :=
  semilattice_inf.to_partial_order ℚ

protected instance preorder : preorder ℚ :=
  directed_order.to_preorder

protected theorem le_def' {p : ℚ} {q : ℚ} : p ≤ q ↔ num p * ↑(denom q) ≤ num q * ↑(denom p) := sorry

protected theorem lt_def {p : ℚ} {q : ℚ} : p < q ↔ num p * ↑(denom q) < num q * ↑(denom p) := sorry

theorem nonneg_iff_zero_le {a : ℚ} : rat.nonneg a ↔ 0 ≤ a := sorry

theorem num_nonneg_iff_zero_le {a : ℚ} : 0 ≤ num a ↔ 0 ≤ a :=
  cases_on a
    fun (a_num : ℤ) (a_denom : ℕ) (a_pos : 0 < a_denom) (a_cop : nat.coprime (int.nat_abs a_num) a_denom) =>
      idRhs (rat.nonneg (mk' a_num a_denom a_pos a_cop) ↔ 0 ≤ mk' a_num a_denom a_pos a_cop) nonneg_iff_zero_le

protected theorem add_le_add_left {a : ℚ} {b : ℚ} {c : ℚ} : c + a ≤ c + b ↔ a ≤ b := sorry

protected theorem mul_nonneg {a : ℚ} {b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ a * b)) (Eq.symm (propext nonneg_iff_zero_le))))
    (rat.nonneg_mul (eq.mp (Eq._oldrec (Eq.refl (0 ≤ a)) (Eq.symm (propext nonneg_iff_zero_le))) ha)
      (eq.mp (Eq._oldrec (Eq.refl (0 ≤ b)) (Eq.symm (propext nonneg_iff_zero_le))) hb))

protected instance linear_ordered_field : linear_ordered_field ℚ :=
  linear_ordered_field.mk field.add field.add_assoc field.zero field.zero_add field.add_zero field.neg field.sub
    field.add_left_neg field.add_comm field.mul field.mul_assoc field.one field.one_mul field.mul_one field.left_distrib
    field.right_distrib linear_order.le linear_order.lt linear_order.le_refl linear_order.le_trans
    linear_order.le_antisymm sorry sorry sorry linear_order.le_total linear_order.decidable_le linear_order.decidable_eq
    linear_order.decidable_lt field.exists_pair_ne field.mul_comm field.inv field.mul_inv_cancel field.inv_zero

/- Extra instances to short-circuit type class resolution -/

protected instance linear_ordered_comm_ring : linear_ordered_comm_ring ℚ :=
  linear_ordered_field.to_linear_ordered_comm_ring ℚ

protected instance linear_ordered_ring : linear_ordered_ring ℚ :=
  linear_ordered_comm_ring.to_linear_ordered_ring ℚ

protected instance ordered_ring : ordered_ring ℚ :=
  linear_ordered_ring.to_ordered_ring ℚ

protected instance linear_ordered_semiring : linear_ordered_semiring ℚ :=
  linear_ordered_comm_ring.to_linear_ordered_semiring

protected instance ordered_semiring : ordered_semiring ℚ :=
  ordered_ring.to_ordered_semiring

protected instance linear_ordered_add_comm_group : linear_ordered_add_comm_group ℚ :=
  linear_ordered_ring.to_linear_ordered_add_comm_group

protected instance ordered_add_comm_group : ordered_add_comm_group ℚ :=
  ordered_ring.to_ordered_add_comm_group ℚ

protected instance ordered_cancel_add_comm_monoid : ordered_cancel_add_comm_monoid ℚ :=
  ordered_semiring.to_ordered_cancel_add_comm_monoid ℚ

protected instance ordered_add_comm_monoid : ordered_add_comm_monoid ℚ :=
  ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid

theorem num_pos_iff_pos {a : ℚ} : 0 < num a ↔ 0 < a := sorry

theorem div_lt_div_iff_mul_lt_mul {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) : ↑a / ↑b < ↑c / ↑d ↔ a * d < c * b := sorry

theorem lt_one_iff_num_lt_denom {q : ℚ} : q < 1 ↔ num q < ↑(denom q) := sorry

theorem abs_def (q : ℚ) : abs q = mk ↑(int.nat_abs (num q)) ↑(denom q) := sorry

