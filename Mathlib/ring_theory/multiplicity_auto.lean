/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.associated
import Mathlib.algebra.big_operators.basic
import Mathlib.data.nat.enat
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-- `multiplicity a b` returns the largest natural number `n` such that
  `a ^ n ∣ b`, as an `enat` or natural with infinity. If `∀ n, a ^ n ∣ b`,
  then it returns `⊤`-/
def multiplicity {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] (a : α) (b : α) : enat :=
  enat.find fun (n : ℕ) => ¬a ^ (n + 1) ∣ b

namespace multiplicity


/-- `multiplicity.finite a b` indicates that the multiplicity of `a` in `b` is finite. -/
def finite {α : Type u_1} [comm_monoid α] (a : α) (b : α) := ∃ (n : ℕ), ¬a ^ (n + 1) ∣ b

theorem finite_iff_dom {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α} {b : α} :
    finite a b ↔ roption.dom (multiplicity a b) :=
  iff.rfl

theorem finite_def {α : Type u_1} [comm_monoid α] {a : α} {b : α} :
    finite a b ↔ ∃ (n : ℕ), ¬a ^ (n + 1) ∣ b :=
  iff.rfl

theorem int.coe_nat_multiplicity (a : ℕ) (b : ℕ) : multiplicity ↑a ↑b = multiplicity a b := sorry

theorem not_finite_iff_forall {α : Type u_1} [comm_monoid α] {a : α} {b : α} :
    ¬finite a b ↔ ∀ (n : ℕ), a ^ n ∣ b :=
  sorry

theorem not_unit_of_finite {α : Type u_1} [comm_monoid α] {a : α} {b : α} (h : finite a b) :
    ¬is_unit a :=
  sorry

theorem finite_of_finite_mul_left {α : Type u_1} [comm_monoid α] {a : α} {b : α} {c : α} :
    finite a (b * c) → finite a c :=
  sorry

theorem finite_of_finite_mul_right {α : Type u_1} [comm_monoid α] {a : α} {b : α} {c : α} :
    finite a (b * c) → finite a b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finite a (b * c) → finite a b)) (mul_comm b c)))
    finite_of_finite_mul_left

theorem pow_dvd_of_le_multiplicity {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α}
    {b : α} {k : ℕ} : ↑k ≤ multiplicity a b → a ^ k ∣ b :=
  sorry

theorem pow_multiplicity_dvd {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α}
    {b : α} (h : finite a b) : a ^ roption.get (multiplicity a b) h ∣ b :=
  pow_dvd_of_le_multiplicity
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (↑(roption.get (multiplicity a b) h) ≤ multiplicity a b))
          (enat.coe_get h)))
      (le_refl (multiplicity a b)))

theorem is_greatest {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α} {b : α}
    {m : ℕ} (hm : multiplicity a b < ↑m) : ¬a ^ m ∣ b :=
  sorry

theorem is_greatest' {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α} {b : α}
    {m : ℕ} (h : finite a b) (hm : roption.get (multiplicity a b) h < m) : ¬a ^ m ∣ b :=
  is_greatest
    (eq.mp (Eq._oldrec (Eq.refl (↑(roption.get (multiplicity a b) h) < ↑m)) (enat.coe_get h))
      (eq.mp
        (Eq._oldrec (Eq.refl (roption.get (multiplicity a b) h < m))
          (Eq.symm (propext enat.coe_lt_coe)))
        hm))

theorem unique {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α} {b : α} {k : ℕ}
    (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) : ↑k = multiplicity a b :=
  sorry

theorem unique' {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α} {b : α} {k : ℕ}
    (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    k = roption.get (multiplicity a b) (Exists.intro k hsucc) :=
  sorry

theorem le_multiplicity_of_pow_dvd {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α}
    {b : α} {k : ℕ} (hk : a ^ k ∣ b) : ↑k ≤ multiplicity a b :=
  le_of_not_gt fun (hk' : ↑k > multiplicity a b) => is_greatest hk' hk

theorem pow_dvd_iff_le_multiplicity {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd]
    {a : α} {b : α} {k : ℕ} : a ^ k ∣ b ↔ ↑k ≤ multiplicity a b :=
  { mp := le_multiplicity_of_pow_dvd, mpr := pow_dvd_of_le_multiplicity }

theorem multiplicity_lt_iff_neg_dvd {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd]
    {a : α} {b : α} {k : ℕ} : multiplicity a b < ↑k ↔ ¬a ^ k ∣ b :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (multiplicity a b < ↑k ↔ ¬a ^ k ∣ b))
        (propext pow_dvd_iff_le_multiplicity)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (multiplicity a b < ↑k ↔ ¬↑k ≤ multiplicity a b)) (propext not_le)))
      (iff.refl (multiplicity a b < ↑k)))

theorem eq_some_iff {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α} {b : α}
    {n : ℕ} : multiplicity a b = ↑n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b :=
  sorry

theorem eq_top_iff {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α} {b : α} :
    multiplicity a b = ⊤ ↔ ∀ (n : ℕ), a ^ n ∣ b :=
  sorry

theorem one_right {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α}
    (ha : ¬is_unit a) : multiplicity a 1 = 0 :=
  sorry

@[simp] theorem get_one_right {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α}
    (ha : finite a 1) : roption.get (multiplicity a 1) ha = 0 :=
  sorry

@[simp] theorem multiplicity_unit {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α}
    (b : α) (ha : is_unit a) : multiplicity a b = ⊤ :=
  iff.mpr eq_top_iff fun (_x : ℕ) => iff.mp is_unit_iff_forall_dvd (is_unit.pow _x ha) b

@[simp] theorem one_left {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] (b : α) :
    multiplicity 1 b = ⊤ :=
  sorry

theorem multiplicity_eq_zero_of_not_dvd {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd]
    {a : α} {b : α} (ha : ¬a ∣ b) : multiplicity a b = 0 :=
  sorry

theorem eq_top_iff_not_finite {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α}
    {b : α} : multiplicity a b = ⊤ ↔ ¬finite a b :=
  roption.eq_none_iff'

theorem multiplicity_le_multiplicity_iff {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd]
    {a : α} {b : α} {c : α} {d : α} :
    multiplicity a b ≤ multiplicity c d ↔ ∀ (n : ℕ), a ^ n ∣ b → c ^ n ∣ d :=
  sorry

theorem multiplicity_le_multiplicity_of_dvd {α : Type u_1} [comm_monoid α]
    [DecidableRel has_dvd.dvd] {a : α} {b : α} {c : α} (hdvd : a ∣ b) :
    multiplicity b c ≤ multiplicity a c :=
  iff.mpr multiplicity_le_multiplicity_iff
    fun (n : ℕ) (h : b ^ n ∣ c) => dvd_trans (pow_dvd_pow_of_dvd hdvd n) h

theorem dvd_of_multiplicity_pos {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α}
    {b : α} (h : 0 < multiplicity a b) : a ∣ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∣ b)) (Eq.symm (pow_one a))))
    (pow_dvd_of_le_multiplicity (iff.mp enat.pos_iff_one_le h))

theorem dvd_iff_multiplicity_pos {α : Type u_1} [comm_monoid α] [DecidableRel has_dvd.dvd] {a : α}
    {b : α} : 0 < multiplicity a b ↔ a ∣ b :=
  sorry

theorem finite_nat_iff {a : ℕ} {b : ℕ} : finite a b ↔ a ≠ 1 ∧ 0 < b := sorry

theorem ne_zero_of_finite {α : Type u_1} [comm_monoid_with_zero α] {a : α} {b : α}
    (h : finite a b) : b ≠ 0 :=
  sorry

@[simp] protected theorem zero {α : Type u_1} [comm_monoid_with_zero α] [DecidableRel has_dvd.dvd]
    (a : α) : multiplicity a 0 = ⊤ :=
  sorry

@[simp] theorem multiplicity_zero_eq_zero_of_ne_zero {α : Type u_1} [comm_monoid_with_zero α]
    [DecidableRel has_dvd.dvd] (a : α) (ha : a ≠ 0) : multiplicity 0 a = 0 :=
  multiplicity_eq_zero_of_not_dvd
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬0 ∣ a)) (propext zero_dvd_iff))) ha)

theorem min_le_multiplicity_add {α : Type u_1} [comm_semiring α] [DecidableRel has_dvd.dvd] {p : α}
    {a : α} {b : α} : min (multiplicity p a) (multiplicity p b) ≤ multiplicity p (a + b) :=
  sorry

@[simp] protected theorem neg {α : Type u_1} [comm_ring α] [DecidableRel has_dvd.dvd] (a : α)
    (b : α) : multiplicity a (-b) = multiplicity a b :=
  sorry

theorem multiplicity_add_of_gt {α : Type u_1} [comm_ring α] [DecidableRel has_dvd.dvd] {p : α}
    {a : α} {b : α} (h : multiplicity p b < multiplicity p a) :
    multiplicity p (a + b) = multiplicity p b :=
  sorry

theorem multiplicity_sub_of_gt {α : Type u_1} [comm_ring α] [DecidableRel has_dvd.dvd] {p : α}
    {a : α} {b : α} (h : multiplicity p b < multiplicity p a) :
    multiplicity p (a - b) = multiplicity p b :=
  sorry

theorem multiplicity_add_eq_min {α : Type u_1} [comm_ring α] [DecidableRel has_dvd.dvd] {p : α}
    {a : α} {b : α} (h : multiplicity p a ≠ multiplicity p b) :
    multiplicity p (a + b) = min (multiplicity p a) (multiplicity p b) :=
  sorry

theorem finite_mul_aux {α : Type u_1} [comm_cancel_monoid_with_zero α] {p : α} (hp : prime p)
    {n : ℕ} {m : ℕ} {a : α} {b : α} :
    ¬p ^ (n + 1) ∣ a → ¬p ^ (m + 1) ∣ b → ¬p ^ (n + m + 1) ∣ a * b :=
  sorry

theorem finite_mul {α : Type u_1} [comm_cancel_monoid_with_zero α] {p : α} {a : α} {b : α}
    (hp : prime p) : finite p a → finite p b → finite p (a * b) :=
  sorry

theorem finite_mul_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] {p : α} {a : α} {b : α}
    (hp : prime p) : finite p (a * b) ↔ finite p a ∧ finite p b :=
  { mp :=
      fun (h : finite p (a * b)) =>
        { left := finite_of_finite_mul_right h, right := finite_of_finite_mul_left h },
    mpr := fun (h : finite p a ∧ finite p b) => finite_mul hp (and.left h) (and.right h) }

theorem finite_pow {α : Type u_1} [comm_cancel_monoid_with_zero α] {p : α} {a : α} (hp : prime p)
    {k : ℕ} (ha : finite p a) : finite p (a ^ k) :=
  sorry

@[simp] theorem multiplicity_self {α : Type u_1} [comm_cancel_monoid_with_zero α]
    [DecidableRel has_dvd.dvd] {a : α} (ha : ¬is_unit a) (ha0 : a ≠ 0) : multiplicity a a = 1 :=
  sorry

@[simp] theorem get_multiplicity_self {α : Type u_1} [comm_cancel_monoid_with_zero α]
    [DecidableRel has_dvd.dvd] {a : α} (ha : finite a a) : roption.get (multiplicity a a) ha = 1 :=
  sorry

protected theorem mul' {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableRel has_dvd.dvd]
    {p : α} {a : α} {b : α} (hp : prime p) (h : roption.dom (multiplicity p (a * b))) :
    roption.get (multiplicity p (a * b)) h =
        roption.get (multiplicity p a) (and.left (iff.mp (finite_mul_iff hp) h)) +
          roption.get (multiplicity p b) (and.right (iff.mp (finite_mul_iff hp) h)) :=
  sorry

protected theorem mul {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableRel has_dvd.dvd]
    {p : α} {a : α} {b : α} (hp : prime p) :
    multiplicity p (a * b) = multiplicity p a + multiplicity p b :=
  sorry

theorem finset.prod {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableRel has_dvd.dvd]
    {β : Type u_2} {p : α} (hp : prime p) (s : finset β) (f : β → α) :
    multiplicity p (finset.prod s fun (x : β) => f x) =
        finset.sum s fun (x : β) => multiplicity p (f x) :=
  sorry

protected theorem pow' {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableRel has_dvd.dvd]
    {p : α} {a : α} (hp : prime p) (ha : finite p a) {k : ℕ} :
    roption.get (multiplicity p (a ^ k)) (finite_pow hp ha) =
        k * roption.get (multiplicity p a) ha :=
  sorry

theorem pow {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableRel has_dvd.dvd] {p : α}
    {a : α} (hp : prime p) {k : ℕ} : multiplicity p (a ^ k) = k •ℕ multiplicity p a :=
  sorry

theorem multiplicity_pow_self {α : Type u_1} [comm_cancel_monoid_with_zero α]
    [DecidableRel has_dvd.dvd] {p : α} (h0 : p ≠ 0) (hu : ¬is_unit p) (n : ℕ) :
    multiplicity p (p ^ n) = ↑n :=
  sorry

theorem multiplicity_pow_self_of_prime {α : Type u_1} [comm_cancel_monoid_with_zero α]
    [DecidableRel has_dvd.dvd] {p : α} (hp : prime p) (n : ℕ) : multiplicity p (p ^ n) = ↑n :=
  multiplicity_pow_self (prime.ne_zero hp) (prime.not_unit hp) n

end multiplicity


theorem multiplicity_eq_zero_of_coprime {p : ℕ} {a : ℕ} {b : ℕ} (hp : p ≠ 1)
    (hle : multiplicity p a ≤ multiplicity p b) (hab : nat.coprime a b) : multiplicity p a = 0 :=
  sorry

end Mathlib