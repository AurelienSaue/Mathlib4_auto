/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.lattice
import Mathlib.algebra.gcd_monoid
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# GCD and LCM operations on multisets

## Main definitions

- `multiset.gcd` - the greatest common denominator of a `multiset` of elements of a `gcd_monoid`
- `multiset.lcm` - the least common multiple of a `multiset` of elements of a `gcd_monoid`

## Implementation notes

TODO: simplify with a tactic and `data.multiset.lattice`

## Tags

multiset, gcd
-/

namespace multiset


/-! ### lcm -/

/-- Least common multiple of a multiset -/
def lcm {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (s : multiset α) : α :=
  fold lcm 1 s

@[simp] theorem lcm_zero {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] : lcm 0 = 1 :=
  fold_zero lcm 1

@[simp] theorem lcm_cons {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (s : multiset α) : lcm (a ::ₘ s) = lcm a (lcm s) :=
  fold_cons_left lcm 1 a s

@[simp] theorem lcm_singleton {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} : lcm (a ::ₘ 0) = coe_fn normalize a := sorry

@[simp] theorem lcm_add {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (s₁ : multiset α) (s₂ : multiset α) : lcm (s₁ + s₂) = lcm (lcm s₁) (lcm s₂) := sorry

theorem lcm_dvd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {s : multiset α} {a : α} : lcm s ∣ a ↔ ∀ (b : α), b ∈ s → b ∣ a := sorry

theorem dvd_lcm {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {s : multiset α} {a : α} (h : a ∈ s) : a ∣ lcm s :=
  iff.mp lcm_dvd (dvd_refl (lcm s)) a h

theorem lcm_mono {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {s₁ : multiset α} {s₂ : multiset α} (h : s₁ ⊆ s₂) : lcm s₁ ∣ lcm s₂ :=
  iff.mpr lcm_dvd fun (b : α) (hb : b ∈ s₁) => dvd_lcm (h hb)

@[simp] theorem normalize_lcm {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (s : multiset α) : coe_fn normalize (lcm s) = lcm s := sorry

@[simp] theorem lcm_erase_dup {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] [DecidableEq α] (s : multiset α) : lcm (erase_dup s) = lcm s := sorry

@[simp] theorem lcm_ndunion {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] [DecidableEq α] (s₁ : multiset α) (s₂ : multiset α) : lcm (ndunion s₁ s₂) = lcm (lcm s₁) (lcm s₂) := sorry

@[simp] theorem lcm_union {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] [DecidableEq α] (s₁ : multiset α) (s₂ : multiset α) : lcm (s₁ ∪ s₂) = lcm (lcm s₁) (lcm s₂) := sorry

@[simp] theorem lcm_ndinsert {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] [DecidableEq α] (a : α) (s : multiset α) : lcm (ndinsert a s) = lcm a (lcm s) := sorry

/-! ### gcd -/

/-- Greatest common divisor of a multiset -/
def gcd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (s : multiset α) : α :=
  fold gcd 0 s

@[simp] theorem gcd_zero {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] : gcd 0 = 0 :=
  fold_zero gcd 0

@[simp] theorem gcd_cons {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (a : α) (s : multiset α) : gcd (a ::ₘ s) = gcd a (gcd s) :=
  fold_cons_left gcd 0 a s

@[simp] theorem gcd_singleton {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {a : α} : gcd (a ::ₘ 0) = coe_fn normalize a := sorry

@[simp] theorem gcd_add {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (s₁ : multiset α) (s₂ : multiset α) : gcd (s₁ + s₂) = gcd (gcd s₁) (gcd s₂) := sorry

theorem dvd_gcd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {s : multiset α} {a : α} : a ∣ gcd s ↔ ∀ (b : α), b ∈ s → a ∣ b := sorry

theorem gcd_dvd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {s : multiset α} {a : α} (h : a ∈ s) : gcd s ∣ a :=
  iff.mp dvd_gcd (dvd_refl (gcd s)) a h

theorem gcd_mono {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] {s₁ : multiset α} {s₂ : multiset α} (h : s₁ ⊆ s₂) : gcd s₂ ∣ gcd s₁ :=
  iff.mpr dvd_gcd fun (b : α) (hb : b ∈ s₁) => gcd_dvd (h hb)

@[simp] theorem normalize_gcd {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (s : multiset α) : coe_fn normalize (gcd s) = gcd s := sorry

theorem gcd_eq_zero_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] (s : multiset α) : gcd s = 0 ↔ ∀ (x : α), x ∈ s → x = 0 := sorry

@[simp] theorem gcd_erase_dup {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] [DecidableEq α] (s : multiset α) : gcd (erase_dup s) = gcd s := sorry

@[simp] theorem gcd_ndunion {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] [DecidableEq α] (s₁ : multiset α) (s₂ : multiset α) : gcd (ndunion s₁ s₂) = gcd (gcd s₁) (gcd s₂) := sorry

@[simp] theorem gcd_union {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] [DecidableEq α] (s₁ : multiset α) (s₂ : multiset α) : gcd (s₁ ∪ s₂) = gcd (gcd s₁) (gcd s₂) := sorry

@[simp] theorem gcd_ndinsert {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α] [DecidableEq α] (a : α) (s : multiset α) : gcd (ndinsert a s) = gcd a (gcd s) := sorry

