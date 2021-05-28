/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.big_operators.basic
import Mathlib.PostPort

universes u v w 

namespace Mathlib

/-!
# Results about big operators with values in an ordered algebraic structure.

Mostly monotonicity results for the `∑` operation.

-/

namespace finset


theorem le_sum_of_subadditive {α : Type u} {β : Type v} {γ : Type w} [add_comm_monoid α] [ordered_add_comm_monoid β] (f : α → β) (h_zero : f 0 = 0) (h_add : ∀ (x y : α), f (x + y) ≤ f x + f y) (s : finset γ) (g : γ → α) : f (finset.sum s fun (x : γ) => g x) ≤ finset.sum s fun (x : γ) => f (g x) := sorry

theorem abs_sum_le_sum_abs {α : Type u} {β : Type v} [linear_ordered_field α] {f : β → α} {s : finset β} : abs (finset.sum s fun (x : β) => f x) ≤ finset.sum s fun (x : β) => abs (f x) :=
  le_sum_of_subadditive abs abs_zero abs_add s f

theorem abs_prod {α : Type u} {β : Type v} [linear_ordered_comm_ring α] {f : β → α} {s : finset β} : abs (finset.prod s fun (x : β) => f x) = finset.prod s fun (x : β) => abs (f x) :=
  monoid_hom.map_prod (monoid_with_zero_hom.to_monoid_hom abs_hom) (fun (x : β) => f x) s

theorem sum_le_sum {α : Type u} {β : Type v} {s : finset α} {f : α → β} {g : α → β} [ordered_add_comm_monoid β] : (∀ (x : α), x ∈ s → f x ≤ g x) → (finset.sum s fun (x : α) => f x) ≤ finset.sum s fun (x : α) => g x := sorry

theorem card_le_mul_card_image_of_maps_to {α : Type u} {γ : Type w} [DecidableEq γ] {f : α → γ} {s : finset α} {t : finset γ} (Hf : ∀ (a : α), a ∈ s → f a ∈ t) (n : ℕ) (hn : ∀ (a : γ), a ∈ t → card (filter (fun (x : α) => f x = a) s) ≤ n) : card s ≤ n * card t := sorry

theorem card_le_mul_card_image {α : Type u} {γ : Type w} [DecidableEq γ] {f : α → γ} (s : finset α) (n : ℕ) (hn : ∀ (a : γ), a ∈ image f s → card (filter (fun (x : α) => f x = a) s) ≤ n) : card s ≤ n * card (image f s) :=
  card_le_mul_card_image_of_maps_to (fun (x : α) => mem_image_of_mem f) n hn

theorem mul_card_image_le_card_of_maps_to {α : Type u} {γ : Type w} [DecidableEq γ] {f : α → γ} {s : finset α} {t : finset γ} (Hf : ∀ (a : α), a ∈ s → f a ∈ t) (n : ℕ) (hn : ∀ (a : γ), a ∈ t → n ≤ card (filter (fun (x : α) => f x = a) s)) : n * card t ≤ card s := sorry

theorem mul_card_image_le_card {α : Type u} {γ : Type w} [DecidableEq γ] {f : α → γ} (s : finset α) (n : ℕ) (hn : ∀ (a : γ), a ∈ image f s → n ≤ card (filter (fun (x : α) => f x = a) s)) : n * card (image f s) ≤ card s :=
  mul_card_image_le_card_of_maps_to (fun (x : α) => mem_image_of_mem f) n hn

theorem sum_nonneg {α : Type u} {β : Type v} {s : finset α} {f : α → β} [ordered_add_comm_monoid β] (h : ∀ (x : α), x ∈ s → 0 ≤ f x) : 0 ≤ finset.sum s fun (x : α) => f x :=
  le_trans (eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ finset.sum s fun (x : α) => 0)) sum_const_zero)) (le_refl 0))
    (sum_le_sum h)

theorem sum_nonpos {α : Type u} {β : Type v} {s : finset α} {f : α → β} [ordered_add_comm_monoid β] (h : ∀ (x : α), x ∈ s → f x ≤ 0) : (finset.sum s fun (x : α) => f x) ≤ 0 :=
  le_trans (sum_le_sum h)
    (eq.mpr (id (Eq._oldrec (Eq.refl ((finset.sum s fun (x : α) => 0) ≤ 0)) sum_const_zero)) (le_refl 0))

theorem sum_le_sum_of_subset_of_nonneg {α : Type u} {β : Type v} {s₁ : finset α} {s₂ : finset α} {f : α → β} [ordered_add_comm_monoid β] (h : s₁ ⊆ s₂) (hf : ∀ (x : α), x ∈ s₂ → ¬x ∈ s₁ → 0 ≤ f x) : (finset.sum s₁ fun (x : α) => f x) ≤ finset.sum s₂ fun (x : α) => f x := sorry

theorem sum_mono_set_of_nonneg {α : Type u} {β : Type v} {f : α → β} [ordered_add_comm_monoid β] (hf : ∀ (x : α), 0 ≤ f x) : monotone fun (s : finset α) => finset.sum s fun (x : α) => f x :=
  fun (s₁ s₂ : finset α) (hs : s₁ ≤ s₂) =>
    sum_le_sum_of_subset_of_nonneg hs fun (x : α) (_x : x ∈ s₂) (_x : ¬x ∈ s₁) => hf x

theorem sum_fiberwise_le_sum_of_sum_fiber_nonneg {α : Type u} {β : Type v} {γ : Type w} [ordered_add_comm_monoid β] [DecidableEq γ] {s : finset α} {t : finset γ} {g : α → γ} {f : α → β} (h : ∀ (y : γ), ¬y ∈ t → 0 ≤ finset.sum (filter (fun (x : α) => g x = y) s) fun (x : α) => f x) : (finset.sum t fun (y : γ) => finset.sum (filter (fun (x : α) => g x = y) s) fun (x : α) => f x) ≤
  finset.sum s fun (x : α) => f x := sorry

theorem sum_le_sum_fiberwise_of_sum_fiber_nonpos {α : Type u} {β : Type v} {γ : Type w} [ordered_add_comm_monoid β] [DecidableEq γ] {s : finset α} {t : finset γ} {g : α → γ} {f : α → β} (h : ∀ (y : γ), ¬y ∈ t → (finset.sum (filter (fun (x : α) => g x = y) s) fun (x : α) => f x) ≤ 0) : (finset.sum s fun (x : α) => f x) ≤
  finset.sum t fun (y : γ) => finset.sum (filter (fun (x : α) => g x = y) s) fun (x : α) => f x :=
  sum_fiberwise_le_sum_of_sum_fiber_nonneg h

theorem sum_eq_zero_iff_of_nonneg {α : Type u} {β : Type v} {s : finset α} {f : α → β} [ordered_add_comm_monoid β] : (∀ (x : α), x ∈ s → 0 ≤ f x) → ((finset.sum s fun (x : α) => f x) = 0 ↔ ∀ (x : α), x ∈ s → f x = 0) := sorry

theorem sum_eq_zero_iff_of_nonpos {α : Type u} {β : Type v} {s : finset α} {f : α → β} [ordered_add_comm_monoid β] : (∀ (x : α), x ∈ s → f x ≤ 0) → ((finset.sum s fun (x : α) => f x) = 0 ↔ ∀ (x : α), x ∈ s → f x = 0) :=
  sum_eq_zero_iff_of_nonneg

theorem single_le_sum {α : Type u} {β : Type v} {s : finset α} {f : α → β} [ordered_add_comm_monoid β] (hf : ∀ (x : α), x ∈ s → 0 ≤ f x) {a : α} (h : a ∈ s) : f a ≤ finset.sum s fun (x : α) => f x := sorry

@[simp] theorem sum_eq_zero_iff {α : Type u} {β : Type v} {s : finset α} {f : α → β} [canonically_ordered_add_monoid β] : (finset.sum s fun (x : α) => f x) = 0 ↔ ∀ (x : α), x ∈ s → f x = 0 :=
  sum_eq_zero_iff_of_nonneg fun (x : α) (hx : x ∈ s) => zero_le (f x)

theorem sum_le_sum_of_subset {α : Type u} {β : Type v} {s₁ : finset α} {s₂ : finset α} {f : α → β} [canonically_ordered_add_monoid β] (h : s₁ ⊆ s₂) : (finset.sum s₁ fun (x : α) => f x) ≤ finset.sum s₂ fun (x : α) => f x :=
  sum_le_sum_of_subset_of_nonneg h fun (x : α) (h₁ : x ∈ s₂) (h₂ : ¬x ∈ s₁) => zero_le (f x)

theorem sum_mono_set {α : Type u} {β : Type v} [canonically_ordered_add_monoid β] (f : α → β) : monotone fun (s : finset α) => finset.sum s fun (x : α) => f x :=
  fun (s₁ s₂ : finset α) (hs : s₁ ≤ s₂) => sum_le_sum_of_subset hs

theorem sum_le_sum_of_ne_zero {α : Type u} {β : Type v} {s₁ : finset α} {s₂ : finset α} {f : α → β} [canonically_ordered_add_monoid β] (h : ∀ (x : α), x ∈ s₁ → f x ≠ 0 → x ∈ s₂) : (finset.sum s₁ fun (x : α) => f x) ≤ finset.sum s₂ fun (x : α) => f x := sorry

theorem sum_lt_sum {α : Type u} {β : Type v} {s : finset α} {f : α → β} {g : α → β} [ordered_cancel_add_comm_monoid β] (Hle : ∀ (i : α), i ∈ s → f i ≤ g i) (Hlt : ∃ (i : α), ∃ (H : i ∈ s), f i < g i) : (finset.sum s fun (x : α) => f x) < finset.sum s fun (x : α) => g x := sorry

theorem sum_lt_sum_of_nonempty {α : Type u} {β : Type v} {s : finset α} {f : α → β} {g : α → β} [ordered_cancel_add_comm_monoid β] (hs : finset.nonempty s) (Hlt : ∀ (x : α), x ∈ s → f x < g x) : (finset.sum s fun (x : α) => f x) < finset.sum s fun (x : α) => g x :=
  sum_lt_sum (fun (i : α) (hi : i ∈ s) => le_of_lt (Hlt i hi))
    (Exists.dcases_on hs fun (i : α) (hi : i ∈ s) => Exists.intro i (Exists.intro hi (Hlt i hi)))

theorem sum_lt_sum_of_subset {α : Type u} {β : Type v} {s₁ : finset α} {s₂ : finset α} {f : α → β} [ordered_cancel_add_comm_monoid β] [DecidableEq α] (h : s₁ ⊆ s₂) {i : α} (hi : i ∈ s₂ \ s₁) (hpos : 0 < f i) (hnonneg : ∀ (j : α), j ∈ s₂ \ s₁ → 0 ≤ f j) : (finset.sum s₁ fun (x : α) => f x) < finset.sum s₂ fun (x : α) => f x := sorry

theorem exists_lt_of_sum_lt {α : Type u} {β : Type v} {s : finset α} {f : α → β} {g : α → β} [linear_ordered_cancel_add_comm_monoid β] (Hlt : (finset.sum s fun (x : α) => f x) < finset.sum s fun (x : α) => g x) : ∃ (i : α), ∃ (H : i ∈ s), f i < g i := sorry

theorem exists_le_of_sum_le {α : Type u} {β : Type v} {s : finset α} {f : α → β} {g : α → β} [linear_ordered_cancel_add_comm_monoid β] (hs : finset.nonempty s) (Hle : (finset.sum s fun (x : α) => f x) ≤ finset.sum s fun (x : α) => g x) : ∃ (i : α), ∃ (H : i ∈ s), f i ≤ g i := sorry

theorem exists_pos_of_sum_zero_of_exists_nonzero {α : Type u} {β : Type v} {s : finset α} [linear_ordered_cancel_add_comm_monoid β] (f : α → β) (h₁ : (finset.sum s fun (e : α) => f e) = 0) (h₂ : ∃ (x : α), ∃ (H : x ∈ s), f x ≠ 0) : ∃ (x : α), ∃ (H : x ∈ s), 0 < f x := sorry

/- this is also true for a ordered commutative multiplicative monoid -/

theorem prod_nonneg {α : Type u} {β : Type v} [linear_ordered_comm_ring β] {s : finset α} {f : α → β} (h0 : ∀ (x : α), x ∈ s → 0 ≤ f x) : 0 ≤ finset.prod s fun (x : α) => f x :=
  prod_induction f (fun (x : β) => 0 ≤ x) (fun (_x _x_1 : β) (ha : 0 ≤ _x) (hb : 0 ≤ _x_1) => mul_nonneg ha hb)
    zero_le_one h0

/- this is also true for a ordered commutative multiplicative monoid -/

theorem prod_pos {α : Type u} {β : Type v} [linear_ordered_comm_ring β] {s : finset α} {f : α → β} (h0 : ∀ (x : α), x ∈ s → 0 < f x) : 0 < finset.prod s fun (x : α) => f x :=
  prod_induction f (fun (x : β) => 0 < x) (fun (_x _x_1 : β) (ha : 0 < _x) (hb : 0 < _x_1) => mul_pos ha hb) zero_lt_one
    h0

/- this is also true for a ordered commutative multiplicative monoid -/

theorem prod_le_prod {α : Type u} {β : Type v} [linear_ordered_comm_ring β] {s : finset α} {f : α → β} {g : α → β} (h0 : ∀ (x : α), x ∈ s → 0 ≤ f x) (h1 : ∀ (x : α), x ∈ s → f x ≤ g x) : (finset.prod s fun (x : α) => f x) ≤ finset.prod s fun (x : α) => g x := sorry

theorem prod_le_one {α : Type u} {β : Type v} [linear_ordered_comm_ring β] {s : finset α} {f : α → β} (h0 : ∀ (x : α), x ∈ s → 0 ≤ f x) (h1 : ∀ (x : α), x ∈ s → f x ≤ 1) : (finset.prod s fun (x : α) => f x) ≤ 1 := sorry

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `linear_ordered_comm_ring`. -/
theorem prod_add_prod_le {α : Type u} {β : Type v} [linear_ordered_comm_ring β] {s : finset α} {i : α} {f : α → β} {g : α → β} {h : α → β} (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ (j : α), j ∈ s → j ≠ i → g j ≤ f j) (hhf : ∀ (j : α), j ∈ s → j ≠ i → h j ≤ f j) (hg : ∀ (i : α), i ∈ s → 0 ≤ g i) (hh : ∀ (i : α), i ∈ s → 0 ≤ h i) : ((finset.prod s fun (i : α) => g i) + finset.prod s fun (i : α) => h i) ≤ finset.prod s fun (i : α) => f i := sorry

theorem prod_le_prod' {α : Type u} {β : Type v} [canonically_ordered_comm_semiring β] {s : finset α} {f : α → β} {g : α → β} (h : ∀ (i : α), i ∈ s → f i ≤ g i) : (finset.prod s fun (x : α) => f x) ≤ finset.prod s fun (x : α) => g x := sorry

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `canonically_ordered_comm_semiring`.
-/
theorem prod_add_prod_le' {α : Type u} {β : Type v} [canonically_ordered_comm_semiring β] {s : finset α} {i : α} {f : α → β} {g : α → β} {h : α → β} (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ (j : α), j ∈ s → j ≠ i → g j ≤ f j) (hhf : ∀ (j : α), j ∈ s → j ≠ i → h j ≤ f j) : ((finset.prod s fun (i : α) => g i) + finset.prod s fun (i : α) => h i) ≤ finset.prod s fun (i : α) => f i := sorry

end finset


namespace with_top


/-- A product of finite numbers is still finite -/
theorem prod_lt_top {α : Type u} {β : Type v} [canonically_ordered_comm_semiring β] [nontrivial β] [DecidableEq β] {s : finset α} {f : α → with_top β} (h : ∀ (a : α), a ∈ s → f a < ⊤) : (finset.prod s fun (x : α) => f x) < ⊤ :=
  finset.prod_induction f (fun (a : with_top β) => a < ⊤) (fun (a b : with_top β) => mul_lt_top) (coe_lt_top 1) h

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top {α : Type u} {β : Type v} [ordered_add_comm_monoid β] {s : finset α} {f : α → with_top β} : (∀ (a : α), a ∈ s → f a < ⊤) → (finset.sum s fun (x : α) => f x) < ⊤ := sorry

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top_iff {α : Type u} {β : Type v} [canonically_ordered_add_monoid β] {s : finset α} {f : α → with_top β} : (finset.sum s fun (x : α) => f x) < ⊤ ↔ ∀ (a : α), a ∈ s → f a < ⊤ := sorry

/-- A sum of numbers is infinite iff one of them is infinite -/
theorem sum_eq_top_iff {α : Type u} {β : Type v} [canonically_ordered_add_monoid β] {s : finset α} {f : α → with_top β} : (finset.sum s fun (x : α) => f x) = ⊤ ↔ ∃ (a : α), ∃ (H : a ∈ s), f a = ⊤ := sorry

