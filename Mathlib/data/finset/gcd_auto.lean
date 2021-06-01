/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.fold
import Mathlib.data.multiset.gcd
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# GCD and LCM operations on finsets

## Main definitions

- `finset.gcd` - the greatest common denominator of a `finset` of elements of a `gcd_monoid`
- `finset.lcm` - the least common multiple of a `finset` of elements of a `gcd_monoid`

## Implementation notes

Many of the proofs use the lemmas `gcd.def` and `lcm.def`, which relate `finset.gcd`
and `finset.lcm` to `multiset.gcd` and `multiset.lcm`.

TODO: simplify with a tactic and `data.finset.lattice`

## Tags

finset, gcd
-/

namespace finset


/-! ### lcm -/

/-- Least common multiple of a finite set -/
def lcm {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α]
    (s : finset β) (f : β → α) : α :=
  fold lcm 1 f s

theorem lcm_def {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} : lcm s f = multiset.lcm (multiset.map f (val s)) :=
  rfl

@[simp] theorem lcm_empty {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {f : β → α} : lcm ∅ f = 1 :=
  fold_empty

@[simp] theorem lcm_dvd_iff {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {s : finset β} {f : β → α} {a : α} :
    lcm s f ∣ a ↔ ∀ (b : β), b ∈ s → f b ∣ a :=
  sorry

theorem lcm_dvd {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} {a : α} :
    (∀ (b : β), b ∈ s → f b ∣ a) → lcm s f ∣ a :=
  iff.mpr lcm_dvd_iff

theorem dvd_lcm {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} {b : β} (hb : b ∈ s) : f b ∣ lcm s f :=
  iff.mp lcm_dvd_iff (dvd_refl (lcm s f)) b hb

@[simp] theorem lcm_insert {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {s : finset β} {f : β → α} [DecidableEq β] {b : β} :
    lcm (insert b s) f = lcm (f b) (lcm s f) :=
  sorry

@[simp] theorem lcm_singleton {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {f : β → α} {b : β} :
    lcm (singleton b) f = coe_fn normalize (f b) :=
  multiset.lcm_singleton

@[simp] theorem normalize_lcm {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {s : finset β} {f : β → α} :
    coe_fn normalize (lcm s f) = lcm s f :=
  sorry

theorem lcm_union {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s₁ : finset β} {s₂ : finset β} {f : β → α} [DecidableEq β] :
    lcm (s₁ ∪ s₂) f = lcm (lcm s₁ f) (lcm s₂ f) :=
  sorry

theorem lcm_congr {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s₁ : finset β} {s₂ : finset β} {f : β → α} {g : β → α} (hs : s₁ = s₂)
    (hfg : ∀ (a : β), a ∈ s₂ → f a = g a) : lcm s₁ f = lcm s₂ g :=
  Eq._oldrec (fun (hfg : ∀ (a : β), a ∈ s₁ → f a = g a) => fold_congr hfg) hs hfg

theorem lcm_mono_fun {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} {g : β → α} (h : ∀ (b : β), b ∈ s → f b ∣ g b) :
    lcm s f ∣ lcm s g :=
  lcm_dvd fun (b : β) (hb : b ∈ s) => dvd_trans (h b hb) (dvd_lcm hb)

theorem lcm_mono {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s₁ : finset β} {s₂ : finset β} {f : β → α} (h : s₁ ⊆ s₂) :
    lcm s₁ f ∣ lcm s₂ f :=
  lcm_dvd fun (b : β) (hb : b ∈ s₁) => dvd_lcm (h hb)

/-! ### gcd -/

/-- Greatest common divisor of a finite set -/
def gcd {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α]
    (s : finset β) (f : β → α) : α :=
  fold gcd 0 f s

theorem gcd_def {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} : gcd s f = multiset.gcd (multiset.map f (val s)) :=
  rfl

@[simp] theorem gcd_empty {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {f : β → α} : gcd ∅ f = 0 :=
  fold_empty

theorem dvd_gcd_iff {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} {a : α} : a ∣ gcd s f ↔ ∀ (b : β), b ∈ s → a ∣ f b :=
  sorry

theorem gcd_dvd {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} {b : β} (hb : b ∈ s) : gcd s f ∣ f b :=
  iff.mp dvd_gcd_iff (dvd_refl (gcd s f)) b hb

theorem dvd_gcd {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} {a : α} :
    (∀ (b : β), b ∈ s → a ∣ f b) → a ∣ gcd s f :=
  iff.mpr dvd_gcd_iff

@[simp] theorem gcd_insert {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {s : finset β} {f : β → α} [DecidableEq β] {b : β} :
    gcd (insert b s) f = gcd (f b) (gcd s f) :=
  sorry

@[simp] theorem gcd_singleton {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {f : β → α} {b : β} :
    gcd (singleton b) f = coe_fn normalize (f b) :=
  multiset.gcd_singleton

@[simp] theorem normalize_gcd {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {s : finset β} {f : β → α} :
    coe_fn normalize (gcd s f) = gcd s f :=
  sorry

theorem gcd_union {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s₁ : finset β} {s₂ : finset β} {f : β → α} [DecidableEq β] :
    gcd (s₁ ∪ s₂) f = gcd (gcd s₁ f) (gcd s₂ f) :=
  sorry

theorem gcd_congr {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s₁ : finset β} {s₂ : finset β} {f : β → α} {g : β → α} (hs : s₁ = s₂)
    (hfg : ∀ (a : β), a ∈ s₂ → f a = g a) : gcd s₁ f = gcd s₂ g :=
  Eq._oldrec (fun (hfg : ∀ (a : β), a ∈ s₁ → f a = g a) => fold_congr hfg) hs hfg

theorem gcd_mono_fun {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} {g : β → α} (h : ∀ (b : β), b ∈ s → f b ∣ g b) :
    gcd s f ∣ gcd s g :=
  dvd_gcd fun (b : β) (hb : b ∈ s) => dvd_trans (gcd_dvd hb) (h b hb)

theorem gcd_mono {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s₁ : finset β} {s₂ : finset β} {f : β → α} (h : s₁ ⊆ s₂) :
    gcd s₂ f ∣ gcd s₁ f :=
  dvd_gcd fun (b : β) (hb : b ∈ s₁) => gcd_dvd (h hb)

theorem gcd_eq_zero_iff {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {s : finset β} {f : β → α} :
    gcd s f = 0 ↔ ∀ (x : β), x ∈ s → f x = 0 :=
  sorry

theorem gcd_eq_gcd_filter_ne_zero {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α]
    [nontrivial α] [gcd_monoid α] {s : finset β} {f : β → α}
    [decidable_pred fun (x : β) => f x = 0] : gcd s f = gcd (filter (fun (x : β) => f x ≠ 0) s) f :=
  sorry

theorem gcd_mul_left {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} {a : α} :
    (gcd s fun (x : β) => a * f x) = coe_fn normalize a * gcd s f :=
  sorry

theorem gcd_mul_right {α : Type u_1} {β : Type u_2} [comm_cancel_monoid_with_zero α] [nontrivial α]
    [gcd_monoid α] {s : finset β} {f : β → α} {a : α} :
    (gcd s fun (x : β) => f x * a) = gcd s f * coe_fn normalize a :=
  sorry

end finset


namespace finset


theorem gcd_eq_of_dvd_sub {α : Type u_1} {β : Type u_2} [nontrivial β] [integral_domain α]
    [gcd_monoid α] {s : finset β} {f : β → α} {g : β → α} {a : α}
    (h : ∀ (x : β), x ∈ s → a ∣ f x - g x) : gcd a (gcd s f) = gcd a (gcd s g) :=
  sorry

end Mathlib