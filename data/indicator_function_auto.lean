/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group.pi
import Mathlib.group_theory.group_action.default
import Mathlib.data.support
import Mathlib.data.finset.lattice
import PostPort

universes u_1 u_3 u_2 u_4 u_5 

namespace Mathlib

/-!
# Indicator function

`indicator (s : set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.

## Implementation note

In mathematics, an indicator function or a characteristic function is a function used to indicate
membership of an element in a set `s`, having the value `1` for all elements of `s` and the value `0`
otherwise. But since it is usually used to restrict a function to a certain set `s`, we let the
indicator function take the value `f x` for some function `f`, instead of `1`. If the usual indicator
function is needed, just set `f` to be the constant function `λx, 1`.

## Tags
indicator, characteristic
-/

namespace set


/-- `indicator s f a` is `f a` if `a ∈ s`, `0` otherwise.  -/
def indicator {α : Type u_1} {β : Type u_3} [HasZero β] (s : set α) (f : α → β) : α → β :=
  fun (x : α) => ite (x ∈ s) (f x) 0

@[simp] theorem piecewise_eq_indicator {α : Type u_1} {β : Type u_3} [HasZero β] {f : α → β} {s : set α} : piecewise s f 0 = indicator s f :=
  rfl

theorem indicator_apply {α : Type u_1} {β : Type u_3} [HasZero β] (s : set α) (f : α → β) (a : α) : indicator s f a = ite (a ∈ s) (f a) 0 :=
  rfl

@[simp] theorem indicator_of_mem {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {a : α} (h : a ∈ s) (f : α → β) : indicator s f a = f a :=
  if_pos h

@[simp] theorem indicator_of_not_mem {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {a : α} (h : ¬a ∈ s) (f : α → β) : indicator s f a = 0 :=
  if_neg h

theorem indicator_eq_zero_or_self {α : Type u_1} {β : Type u_3} [HasZero β] (s : set α) (f : α → β) (a : α) : indicator s f a = 0 ∨ indicator s f a = f a :=
  dite (a ∈ s) (fun (h : a ∈ s) => Or.inr (indicator_of_mem h f)) fun (h : ¬a ∈ s) => Or.inl (indicator_of_not_mem h f)

/-- If an indicator function is nonzero at a point, that
point is in the set. -/
theorem mem_of_indicator_ne_zero {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {f : α → β} {a : α} (h : indicator s f a ≠ 0) : a ∈ s :=
  iff.mp not_imp_comm (fun (hn : ¬a ∈ s) => indicator_of_not_mem hn f) h

theorem eq_on_indicator {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {f : α → β} : eq_on (indicator s f) f s :=
  fun (x : α) (hx : x ∈ s) => indicator_of_mem hx f

theorem support_indicator {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {f : α → β} : function.support (indicator s f) ⊆ s :=
  fun (x : α) (hx : x ∈ function.support (indicator s f)) =>
    not.imp_symm (fun (h : ¬x ∈ s) => indicator_of_not_mem h f) hx

@[simp] theorem indicator_apply_eq_self {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {f : α → β} {a : α} : indicator s f a = f a ↔ ¬a ∈ s → f a = 0 :=
  iff.trans ite_eq_left_iff
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬a ∈ s → 0 = f a ↔ ¬a ∈ s → f a = 0)) (propext eq_comm)))
      (iff.refl (¬a ∈ s → 0 = f a)))

@[simp] theorem indicator_eq_self {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {f : α → β} : indicator s f = f ↔ function.support f ⊆ s := sorry

@[simp] theorem indicator_support {α : Type u_1} {β : Type u_3} [HasZero β] {f : α → β} : indicator (function.support f) f = f :=
  iff.mpr indicator_eq_self (subset.refl (function.support f))

@[simp] theorem indicator_apply_eq_zero {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {f : α → β} {a : α} : indicator s f a = 0 ↔ a ∈ s → f a = 0 :=
  ite_eq_right_iff

@[simp] theorem indicator_eq_zero {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {f : α → β} : (indicator s f = fun (x : α) => 0) ↔ disjoint (function.support f) s := sorry

@[simp] theorem indicator_eq_zero' {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {f : α → β} : indicator s f = 0 ↔ disjoint (function.support f) s :=
  indicator_eq_zero

@[simp] theorem indicator_range_comp {α : Type u_1} {β : Type u_3} [HasZero β] {ι : Sort u_2} (f : ι → α) (g : α → β) : indicator (range f) g ∘ f = g ∘ f :=
  piecewise_range_comp f (fun (x : α) => g x) fun (x : α) => 0

theorem indicator_congr {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {f : α → β} {g : α → β} (h : ∀ (a : α), a ∈ s → f a = g a) : indicator s f = indicator s g := sorry

@[simp] theorem indicator_univ {α : Type u_1} {β : Type u_3} [HasZero β] (f : α → β) : indicator univ f = f :=
  iff.mpr indicator_eq_self (subset_univ (function.support f))

@[simp] theorem indicator_empty {α : Type u_1} {β : Type u_3} [HasZero β] (f : α → β) : indicator ∅ f = fun (a : α) => 0 :=
  iff.mpr indicator_eq_zero (disjoint_empty (function.support f))

@[simp] theorem indicator_zero {α : Type u_1} (β : Type u_3) [HasZero β] (s : set α) : (indicator s fun (x : α) => 0) = fun (x : α) => 0 := sorry

@[simp] theorem indicator_zero' {α : Type u_1} (β : Type u_3) [HasZero β] {s : set α} : indicator s 0 = 0 :=
  indicator_zero β s

theorem indicator_indicator {α : Type u_1} {β : Type u_3} [HasZero β] (s : set α) (t : set α) (f : α → β) : indicator s (indicator t f) = indicator (s ∩ t) f := sorry

theorem comp_indicator {α : Type u_1} {β : Type u_3} {γ : Type u_4} [HasZero β] (h : β → γ) (f : α → β) {s : set α} {x : α} : h (indicator s f x) = piecewise s (h ∘ f) (function.const α (h 0)) x :=
  comp_piecewise s h

theorem indicator_comp_right {α : Type u_1} {β : Type u_3} {γ : Type u_4} [HasZero β] {s : set α} (f : γ → α) {g : α → β} {x : γ} : indicator (f ⁻¹' s) (g ∘ f) x = indicator s g (f x) := sorry

theorem indicator_comp_of_zero {α : Type u_1} {β : Type u_3} {γ : Type u_4} [HasZero β] {s : set α} {f : α → β} [HasZero γ] {g : β → γ} (hg : g 0 = 0) : indicator s (g ∘ f) = g ∘ indicator s f := sorry

theorem indicator_preimage {α : Type u_1} {β : Type u_3} [HasZero β] (s : set α) (f : α → β) (B : set β) : indicator s f ⁻¹' B = s ∩ f ⁻¹' B ∪ sᶜ ∩ (fun (a : α) => 0) ⁻¹' B :=
  piecewise_preimage s f 0 B

theorem indicator_preimage_of_not_mem {α : Type u_1} {β : Type u_3} [HasZero β] (s : set α) (f : α → β) {t : set β} (ht : ¬0 ∈ t) : indicator s f ⁻¹' t = s ∩ f ⁻¹' t := sorry

theorem mem_range_indicator {α : Type u_1} {β : Type u_3} [HasZero β] {r : β} {s : set α} {f : α → β} : r ∈ range (indicator s f) ↔ r = 0 ∧ s ≠ univ ∨ r ∈ f '' s := sorry

theorem indicator_rel_indicator {α : Type u_1} {β : Type u_3} [HasZero β] {s : set α} {f : α → β} {g : α → β} {a : α} {r : β → β → Prop} (h0 : r 0 0) (ha : a ∈ s → r (f a) (g a)) : r (indicator s f a) (indicator s g a) := sorry

/-- Consider a sum of `g i (f i)` over a `finset`.  Suppose `g` is a
function such as multiplication, which maps a second argument of 0 to
0.  (A typical use case would be a weighted sum of `f i * h i` or `f i
• h i`, where `f` gives the weights that are multiplied by some other
function `h`.)  Then if `f` is replaced by the corresponding indicator
function, the `finset` may be replaced by a possibly larger `finset`
without changing the value of the sum. -/
theorem sum_indicator_subset_of_eq_zero {α : Type u_1} {β : Type u_3} [HasZero β] {γ : Type u_2} [add_comm_monoid γ] (f : α → β) (g : α → β → γ) {s₁ : finset α} {s₂ : finset α} (h : s₁ ⊆ s₂) (hg : ∀ (a : α), g a 0 = 0) : (finset.sum s₁ fun (i : α) => g i (f i)) = finset.sum s₂ fun (i : α) => g i (indicator (↑s₁) f i) := sorry

/-- Summing an indicator function over a possibly larger `finset` is
the same as summing the original function over the original
`finset`. -/
theorem sum_indicator_subset {α : Type u_1} {γ : Type u_2} [add_comm_monoid γ] (f : α → γ) {s₁ : finset α} {s₂ : finset α} (h : s₁ ⊆ s₂) : (finset.sum s₁ fun (i : α) => f i) = finset.sum s₂ fun (i : α) => indicator (↑s₁) f i :=
  sum_indicator_subset_of_eq_zero (fun (i : α) => f i) (fun (a : α) (b : γ) => b) h fun (_x : α) => rfl

theorem indicator_union_of_not_mem_inter {α : Type u_1} {β : Type u_3} [add_monoid β] {s : set α} {t : set α} {a : α} (h : ¬a ∈ s ∩ t) (f : α → β) : indicator (s ∪ t) f a = indicator s f a + indicator t f a := sorry

theorem indicator_union_of_disjoint {α : Type u_1} {β : Type u_3} [add_monoid β] {s : set α} {t : set α} (h : disjoint s t) (f : α → β) : indicator (s ∪ t) f = fun (a : α) => indicator s f a + indicator t f a := sorry

theorem indicator_add {α : Type u_1} {β : Type u_3} [add_monoid β] (s : set α) (f : α → β) (g : α → β) : (indicator s fun (a : α) => f a + g a) = fun (a : α) => indicator s f a + indicator s g a := sorry

@[simp] theorem indicator_compl_add_self_apply {α : Type u_1} {β : Type u_3} [add_monoid β] (s : set α) (f : α → β) (a : α) : indicator (sᶜ) f a + indicator s f a = f a := sorry

@[simp] theorem indicator_compl_add_self {α : Type u_1} {β : Type u_3} [add_monoid β] (s : set α) (f : α → β) : indicator (sᶜ) f + indicator s f = f :=
  funext (indicator_compl_add_self_apply s f)

@[simp] theorem indicator_self_add_compl_apply {α : Type u_1} {β : Type u_3} [add_monoid β] (s : set α) (f : α → β) (a : α) : indicator s f a + indicator (sᶜ) f a = f a := sorry

@[simp] theorem indicator_self_add_compl {α : Type u_1} {β : Type u_3} [add_monoid β] (s : set α) (f : α → β) : indicator s f + indicator (sᶜ) f = f :=
  funext (indicator_self_add_compl_apply s f)

protected instance is_add_monoid_hom.indicator {α : Type u_1} (β : Type u_3) [add_monoid β] (s : set α) : is_add_monoid_hom fun (f : α → β) => indicator s f :=
  is_add_monoid_hom.mk (indicator_zero β s)

theorem indicator_smul {α : Type u_1} {β : Type u_3} [add_monoid β] {𝕜 : Type u_5} [monoid 𝕜] [distrib_mul_action 𝕜 β] (s : set α) (r : 𝕜) (f : α → β) : (indicator s fun (x : α) => r • f x) = fun (x : α) => r • indicator s f x := sorry

theorem indicator_add_eq_left {α : Type u_1} {β : Type u_3} [add_monoid β] {f : α → β} {g : α → β} (h : univ ⊆ f ⁻¹' singleton 0 ∪ g ⁻¹' singleton 0) : indicator (f ⁻¹' singleton 0ᶜ) (f + g) = f := sorry

theorem indicator_add_eq_right {α : Type u_1} {β : Type u_3} [add_monoid β] {f : α → β} {g : α → β} (h : univ ⊆ f ⁻¹' singleton 0 ∪ g ⁻¹' singleton 0) : indicator (g ⁻¹' singleton 0ᶜ) (f + g) = g := sorry

protected instance is_add_group_hom.indicator {α : Type u_1} (β : Type u_3) [add_group β] (s : set α) : is_add_group_hom fun (f : α → β) => indicator s f :=
  is_add_group_hom.mk

theorem indicator_neg {α : Type u_1} {β : Type u_3} [add_group β] (s : set α) (f : α → β) : (indicator s fun (a : α) => -f a) = fun (a : α) => -indicator s f a :=
  (fun (this : indicator s (-f) = -indicator s f) => this) (is_add_group_hom.map_neg (indicator s) f)

theorem indicator_sub {α : Type u_1} {β : Type u_3} [add_group β] (s : set α) (f : α → β) (g : α → β) : (indicator s fun (a : α) => f a - g a) = fun (a : α) => indicator s f a - indicator s g a :=
  (fun (this : indicator s (f - g) = indicator s f - indicator s g) => this) (is_add_group_hom.map_sub (indicator s) f g)

theorem indicator_compl {α : Type u_1} {β : Type u_3} [add_group β] (s : set α) (f : α → β) : indicator (sᶜ) f = f - indicator s f :=
  eq_sub_of_add_eq (indicator_compl_add_self s f)

theorem indicator_finset_sum {α : Type u_1} {β : Type u_2} [add_comm_monoid β] {ι : Type u_3} (I : finset ι) (s : set α) (f : ι → α → β) : indicator s (finset.sum I fun (i : ι) => f i) = finset.sum I fun (i : ι) => indicator s (f i) := sorry

theorem indicator_finset_bUnion {α : Type u_1} {β : Type u_2} [add_comm_monoid β] {ι : Type u_3} (I : finset ι) (s : ι → set α) {f : α → β} : (∀ (i : ι), i ∈ I → ∀ (j : ι), j ∈ I → i ≠ j → s i ∩ s j = ∅) →
  indicator (Union fun (i : ι) => Union fun (H : i ∈ I) => s i) f =
    fun (a : α) => finset.sum I fun (i : ι) => indicator (s i) f a := sorry

theorem indicator_mul {α : Type u_1} {β : Type u_3} [mul_zero_class β] (s : set α) (f : α → β) (g : α → β) : (indicator s fun (a : α) => f a * g a) = fun (a : α) => indicator s f a * indicator s g a := sorry

theorem indicator_mul_left {α : Type u_1} {β : Type u_3} [mul_zero_class β] {a : α} (s : set α) (f : α → β) (g : α → β) : indicator s (fun (a : α) => f a * g a) a = indicator s f a * g a := sorry

theorem indicator_mul_right {α : Type u_1} {β : Type u_3} [mul_zero_class β] {a : α} (s : set α) (f : α → β) (g : α → β) : indicator s (fun (a : α) => f a * g a) a = f a * indicator s g a := sorry

theorem indicator_prod_one {α : Type u_1} {α' : Type u_2} {β : Type u_3} [monoid_with_zero β] {s : set α} {t : set α'} {x : α} {y : α'} : indicator (set.prod s t) 1 (x, y) = indicator s 1 x * indicator t 1 y := sorry

theorem indicator_nonneg' {α : Type u_1} {β : Type u_3} [HasZero β] [preorder β] {s : set α} {f : α → β} {a : α} (h : a ∈ s → 0 ≤ f a) : 0 ≤ indicator s f a := sorry

theorem indicator_nonneg {α : Type u_1} {β : Type u_3} [HasZero β] [preorder β] {s : set α} {f : α → β} (h : ∀ (a : α), a ∈ s → 0 ≤ f a) (a : α) : 0 ≤ indicator s f a :=
  indicator_nonneg' (h a)

theorem indicator_nonpos' {α : Type u_1} {β : Type u_3} [HasZero β] [preorder β] {s : set α} {f : α → β} {a : α} (h : a ∈ s → f a ≤ 0) : indicator s f a ≤ 0 := sorry

theorem indicator_nonpos {α : Type u_1} {β : Type u_3} [HasZero β] [preorder β] {s : set α} {f : α → β} (h : ∀ (a : α), a ∈ s → f a ≤ 0) (a : α) : indicator s f a ≤ 0 :=
  indicator_nonpos' (h a)

theorem indicator_le' {α : Type u_1} {β : Type u_3} [HasZero β] [preorder β] {s : set α} {f : α → β} {g : α → β} (hfg : ∀ (a : α), a ∈ s → f a ≤ g a) (hg : ∀ (a : α), ¬a ∈ s → 0 ≤ g a) : indicator s f ≤ g := sorry

theorem indicator_le_indicator {α : Type u_1} {β : Type u_3} [HasZero β] [preorder β] {s : set α} {f : α → β} {g : α → β} {a : α} (h : f a ≤ g a) : indicator s f a ≤ indicator s g a :=
  indicator_rel_indicator (le_refl 0) fun (_x : a ∈ s) => h

theorem indicator_le_indicator_of_subset {α : Type u_1} {β : Type u_3} [HasZero β] [preorder β] {s : set α} {t : set α} {f : α → β} (h : s ⊆ t) (hf : ∀ (a : α), 0 ≤ f a) (a : α) : indicator s f a ≤ indicator t f a := sorry

theorem indicator_le_self' {α : Type u_1} {β : Type u_3} [HasZero β] [preorder β] {s : set α} {f : α → β} (hf : ∀ (x : α), ¬x ∈ s → 0 ≤ f x) : indicator s f ≤ f :=
  indicator_le' (fun (_x : α) (_x_1 : _x ∈ s) => le_refl (f _x)) hf

theorem indicator_le_self {α : Type u_1} {β : Type u_2} [canonically_ordered_add_monoid β] (s : set α) (f : α → β) : indicator s f ≤ f :=
  indicator_le_self' fun (_x : α) (_x_1 : ¬_x ∈ s) => zero_le (f _x)

theorem indicator_le {α : Type u_1} {β : Type u_2} [canonically_ordered_add_monoid β] {s : set α} {f : α → β} {g : α → β} (hfg : ∀ (a : α), a ∈ s → f a ≤ g a) : indicator s f ≤ g :=
  indicator_le' hfg fun (_x : α) (_x_1 : ¬_x ∈ s) => zero_le (g _x)

theorem indicator_Union_apply {α : Type u_1} {ι : Sort u_2} {β : Type u_3} [complete_lattice β] [HasZero β] (h0 : ⊥ = 0) (s : ι → set α) (f : α → β) (x : α) : indicator (Union fun (i : ι) => s i) f x = supr fun (i : ι) => indicator (s i) f x := sorry

end set


theorem add_monoid_hom.map_indicator {α : Type u_1} {M : Type u_2} {N : Type u_3} [add_monoid M] [add_monoid N] (f : M →+ N) (s : set α) (g : α → M) (x : α) : coe_fn f (set.indicator s g x) = set.indicator s (⇑f ∘ g) x :=
  congr_fun (Eq.symm (set.indicator_comp_of_zero (add_monoid_hom.map_zero f))) x

