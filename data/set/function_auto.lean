/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.set.basic
import Mathlib.logic.function.conjugate
import PostPort

universes u v u_1 w y u_2 u_3 

namespace Mathlib

/-!
# Functions over sets

## Main definitions

### Predicate

* `eq_on f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `maps_to f s t` : `f` sends every point of `s` to a point of `t`;
* `inj_on f s` : restriction of `f` to `s` is injective;
* `surj_on f s t` : every point in `s` has a preimage in `s`;
* `bij_on f s t` : `f` is a bijection between `s` and `t`;
* `left_inv_on f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `right_inv_on f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `inv_on f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `left_inv_on f' f s` and `right_inv_on f' f t`.

### Functions

* `restrict f s` : restrict the domain of `f` to the set `s`;
* `cod_restrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
* `maps_to.restrict f s t h`: given `h : maps_to f s t`, restrict the domain of `f` to `s`
  and the codomain to `t`.
-/

namespace set


/-! ### Restrict -/

/-- Restrict domain of a function `f` to a set `s`. Same as `subtype.restrict` but this version
takes an argument `↥s` instead of `subtype s`. -/
def restrict {α : Type u} {β : Type v} (f : α → β) (s : set α) : ↥s → β :=
  fun (x : ↥s) => f ↑x

theorem restrict_eq {α : Type u} {β : Type v} (f : α → β) (s : set α) : restrict f s = f ∘ coe :=
  rfl

@[simp] theorem restrict_apply {α : Type u} {β : Type v} (f : α → β) (s : set α) (x : ↥s) : restrict f s x = f ↑x :=
  rfl

@[simp] theorem range_restrict {α : Type u} {β : Type v} (f : α → β) (s : set α) : range (restrict f s) = f '' s :=
  Eq.trans (range_comp f fun (x : ↥s) => ↑x) (congr_arg (image f) subtype.range_coe)

/-- Restrict codomain of a function `f` to a set `s`. Same as `subtype.coind` but this version
has codomain `↥s` instead of `subtype s`. -/
def cod_restrict {α : Type u} {β : Type v} (f : α → β) (s : set β) (h : ∀ (x : α), f x ∈ s) : α → ↥s :=
  fun (x : α) => { val := f x, property := h x }

@[simp] theorem coe_cod_restrict_apply {α : Type u} {β : Type v} (f : α → β) (s : set β) (h : ∀ (x : α), f x ∈ s) (x : α) : ↑(cod_restrict f s h x) = f x :=
  rfl

/-! ### Equality on a set -/

/-- Two functions `f₁ f₂ : α → β` are equal on `s`
  if `f₁ x = f₂ x` for all `x ∈ a`. -/
def eq_on {α : Type u} {β : Type v} (f₁ : α → β) (f₂ : α → β) (s : set α)  :=
  ∀ {x : α}, x ∈ s → f₁ x = f₂ x

theorem eq_on.symm {α : Type u} {β : Type v} {s : set α} {f₁ : α → β} {f₂ : α → β} (h : eq_on f₁ f₂ s) : eq_on f₂ f₁ s :=
  fun (x : α) (hx : x ∈ s) => Eq.symm (h hx)

theorem eq_on_comm {α : Type u} {β : Type v} {s : set α} {f₁ : α → β} {f₂ : α → β} : eq_on f₁ f₂ s ↔ eq_on f₂ f₁ s :=
  { mp := eq_on.symm, mpr := eq_on.symm }

theorem eq_on_refl {α : Type u} {β : Type v} (f : α → β) (s : set α) : eq_on f f s :=
  fun (_x : α) (_x_1 : _x ∈ s) => rfl

theorem eq_on.trans {α : Type u} {β : Type v} {s : set α} {f₁ : α → β} {f₂ : α → β} {f₃ : α → β} (h₁ : eq_on f₁ f₂ s) (h₂ : eq_on f₂ f₃ s) : eq_on f₁ f₃ s :=
  fun (x : α) (hx : x ∈ s) => Eq.trans (h₁ hx) (h₂ hx)

theorem eq_on.image_eq {α : Type u} {β : Type v} {s : set α} {f₁ : α → β} {f₂ : α → β} (heq : eq_on f₁ f₂ s) : f₁ '' s = f₂ '' s :=
  image_congr heq

theorem eq_on.mono {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {f₁ : α → β} {f₂ : α → β} (hs : s₁ ⊆ s₂) (hf : eq_on f₁ f₂ s₂) : eq_on f₁ f₂ s₁ :=
  fun (x : α) (hx : x ∈ s₁) => hf (hs hx)

theorem comp_eq_of_eq_on_range {α : Type u} {β : Type v} {ι : Sort u_1} {f : ι → α} {g₁ : α → β} {g₂ : α → β} (h : eq_on g₁ g₂ (range f)) : g₁ ∘ f = g₂ ∘ f :=
  funext fun (x : ι) => h (mem_range_self x)

/-! ### maps to -/

/-- `maps_to f a b` means that the image of `a` is contained in `b`. -/
def maps_to {α : Type u} {β : Type v} (f : α → β) (s : set α) (t : set β)  :=
  ∀ {x : α}, x ∈ s → f x ∈ t

/-- Given a map `f` sending `s : set α` into `t : set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `subtype.map`. -/
def maps_to.restrict {α : Type u} {β : Type v} (f : α → β) (s : set α) (t : set β) (h : maps_to f s t) : ↥s → ↥t :=
  subtype.map f h

@[simp] theorem maps_to.coe_restrict_apply {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : maps_to f s t) (x : ↥s) : ↑(maps_to.restrict f s t h x) = f ↑x :=
  rfl

theorem maps_to_iff_exists_map_subtype {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} : maps_to f s t ↔ ∃ (g : ↥s → ↥t), ∀ (x : ↥s), f ↑x = ↑(g x) := sorry

theorem maps_to' {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} : maps_to f s t ↔ f '' s ⊆ t :=
  iff.symm image_subset_iff

theorem maps_to_empty {α : Type u} {β : Type v} (f : α → β) (t : set β) : maps_to f ∅ t :=
  empty_subset fun (x : α) => t (f x)

theorem maps_to.image_subset {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : maps_to f s t) : f '' s ⊆ t :=
  iff.mp maps_to' h

theorem maps_to.congr {α : Type u} {β : Type v} {s : set α} {t : set β} {f₁ : α → β} {f₂ : α → β} (h₁ : maps_to f₁ s t) (h : eq_on f₁ f₂ s) : maps_to f₂ s t :=
  fun (x : α) (hx : x ∈ s) => h hx ▸ h₁ hx

theorem eq_on.maps_to_iff {α : Type u} {β : Type v} {s : set α} {t : set β} {f₁ : α → β} {f₂ : α → β} (H : eq_on f₁ f₂ s) : maps_to f₁ s t ↔ maps_to f₂ s t :=
  { mp := fun (h : maps_to f₁ s t) => maps_to.congr h H,
    mpr := fun (h : maps_to f₂ s t) => maps_to.congr h (eq_on.symm H) }

theorem maps_to.comp {α : Type u} {β : Type v} {γ : Type w} {s : set α} {t : set β} {p : set γ} {f : α → β} {g : β → γ} (h₁ : maps_to g t p) (h₂ : maps_to f s t) : maps_to (g ∘ f) s p :=
  fun (x : α) (h : x ∈ s) => h₁ (h₂ h)

theorem maps_to_id {α : Type u} (s : set α) : maps_to id s s :=
  fun (x : α) => id

theorem maps_to.iterate {α : Type u} {f : α → α} {s : set α} (h : maps_to f s s) (n : ℕ) : maps_to (nat.iterate f n) s s := sorry

theorem maps_to.iterate_restrict {α : Type u} {f : α → α} {s : set α} (h : maps_to f s s) (n : ℕ) : nat.iterate (maps_to.restrict f s s h) n = maps_to.restrict (nat.iterate f n) s s (maps_to.iterate h n) := sorry

theorem maps_to.mono {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t₁ : set β} {t₂ : set β} {f : α → β} (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) (hf : maps_to f s₁ t₁) : maps_to f s₂ t₂ :=
  fun (x : α) (hx : x ∈ s₂) => ht (hf (hs hx))

theorem maps_to.union_union {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t₁ : set β} {t₂ : set β} {f : α → β} (h₁ : maps_to f s₁ t₁) (h₂ : maps_to f s₂ t₂) : maps_to f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  fun (x : α) (hx : x ∈ s₁ ∪ s₂) => or.elim hx (fun (hx : x ∈ s₁) => Or.inl (h₁ hx)) fun (hx : x ∈ s₂) => Or.inr (h₂ hx)

theorem maps_to.union {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t : set β} {f : α → β} (h₁ : maps_to f s₁ t) (h₂ : maps_to f s₂ t) : maps_to f (s₁ ∪ s₂) t :=
  union_self t ▸ maps_to.union_union h₁ h₂

@[simp] theorem maps_to_union {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t : set β} {f : α → β} : maps_to f (s₁ ∪ s₂) t ↔ maps_to f s₁ t ∧ maps_to f s₂ t := sorry

theorem maps_to.inter {α : Type u} {β : Type v} {s : set α} {t₁ : set β} {t₂ : set β} {f : α → β} (h₁ : maps_to f s t₁) (h₂ : maps_to f s t₂) : maps_to f s (t₁ ∩ t₂) :=
  fun (x : α) (hx : x ∈ s) => { left := h₁ hx, right := h₂ hx }

theorem maps_to.inter_inter {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t₁ : set β} {t₂ : set β} {f : α → β} (h₁ : maps_to f s₁ t₁) (h₂ : maps_to f s₂ t₂) : maps_to f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  fun (x : α) (hx : x ∈ s₁ ∩ s₂) => { left := h₁ (and.left hx), right := h₂ (and.right hx) }

@[simp] theorem maps_to_inter {α : Type u} {β : Type v} {s : set α} {t₁ : set β} {t₂ : set β} {f : α → β} : maps_to f s (t₁ ∩ t₂) ↔ maps_to f s t₁ ∧ maps_to f s t₂ := sorry

theorem maps_to_univ {α : Type u} {β : Type v} (f : α → β) (s : set α) : maps_to f s univ :=
  fun (x : α) (h : x ∈ s) => trivial

theorem maps_to_image {α : Type u} {β : Type v} (f : α → β) (s : set α) : maps_to f s (f '' s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (maps_to f s (f '' s))) (propext maps_to'))) (subset.refl (f '' s))

theorem maps_to_preimage {α : Type u} {β : Type v} (f : α → β) (t : set β) : maps_to f (f ⁻¹' t) t :=
  subset.refl (f ⁻¹' t)

theorem maps_to_range {α : Type u} {β : Type v} (f : α → β) (s : set α) : maps_to f s (range f) :=
  maps_to.mono (subset.refl s) (image_subset_range f s) (maps_to_image f s)

theorem surjective_maps_to_image_restrict {α : Type u} {β : Type v} (f : α → β) (s : set α) : function.surjective (maps_to.restrict f s (f '' s) (maps_to_image f s)) := sorry

theorem maps_to.mem_iff {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : maps_to f s t) (hc : maps_to f (sᶜ) (tᶜ)) {x : α} : f x ∈ t ↔ x ∈ s :=
  { mp := fun (ht : f x ∈ t) => by_contra fun (hs : ¬x ∈ s) => hc hs ht, mpr := fun (hx : x ∈ s) => h hx }

/-! ### Injectivity on a set -/

/-- `f` is injective on `a` if the restriction of `f` to `a` is injective. -/
def inj_on {α : Type u} {β : Type v} (f : α → β) (s : set α)  :=
  ∀ {x₁ : α}, x₁ ∈ s → ∀ {x₂ : α}, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂

theorem inj_on_empty {α : Type u} {β : Type v} (f : α → β) : inj_on f ∅ :=
  fun (_x : α) (h₁ : _x ∈ ∅) => false.elim h₁

theorem inj_on.eq_iff {α : Type u} {β : Type v} {s : set α} {f : α → β} {x : α} {y : α} (h : inj_on f s) (hx : x ∈ s) (hy : y ∈ s) : f x = f y ↔ x = y :=
  { mp := h hx hy, mpr := fun (h : x = y) => h ▸ rfl }

theorem inj_on.congr {α : Type u} {β : Type v} {s : set α} {f₁ : α → β} {f₂ : α → β} (h₁ : inj_on f₁ s) (h : eq_on f₁ f₂ s) : inj_on f₂ s :=
  fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) => h hx ▸ h hy ▸ h₁ hx hy

theorem eq_on.inj_on_iff {α : Type u} {β : Type v} {s : set α} {f₁ : α → β} {f₂ : α → β} (H : eq_on f₁ f₂ s) : inj_on f₁ s ↔ inj_on f₂ s :=
  { mp := fun (h : inj_on f₁ s) => inj_on.congr h H, mpr := fun (h : inj_on f₂ s) => inj_on.congr h (eq_on.symm H) }

theorem inj_on.mono {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {f : α → β} (h : s₁ ⊆ s₂) (ht : inj_on f s₂) : inj_on f s₁ :=
  fun (x : α) (hx : x ∈ s₁) (y : α) (hy : y ∈ s₁) (H : f x = f y) => ht (h hx) (h hy) H

theorem inj_on_insert {α : Type u} {β : Type v} {f : α → β} {s : set α} {a : α} (has : ¬a ∈ s) : inj_on f (insert a s) ↔ inj_on f s ∧ ¬f a ∈ f '' s := sorry

theorem injective_iff_inj_on_univ {α : Type u} {β : Type v} {f : α → β} : function.injective f ↔ inj_on f univ :=
  { mp := fun (h : function.injective f) (x : α) (hx : x ∈ univ) (y : α) (hy : y ∈ univ) (hxy : f x = f y) => h hxy,
    mpr := fun (h : inj_on f univ) (_x _x_1 : α) (heq : f _x = f _x_1) => h trivial trivial heq }

theorem inj_on_of_injective {α : Type u} {β : Type v} {f : α → β} (h : function.injective f) (s : set α) : inj_on f s :=
  fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) (hxy : f x = f y) => h hxy

theorem Mathlib.function.injective.inj_on {α : Type u} {β : Type v} {f : α → β} (h : function.injective f) (s : set α) : inj_on f s :=
  inj_on_of_injective

theorem inj_on.comp {α : Type u} {β : Type v} {γ : Type w} {s : set α} {t : set β} {f : α → β} {g : β → γ} (hg : inj_on g t) (hf : inj_on f s) (h : maps_to f s t) : inj_on (g ∘ f) s :=
  fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) (heq : function.comp g f x = function.comp g f y) =>
    hf hx hy (hg (h hx) (h hy) heq)

theorem inj_on_iff_injective {α : Type u} {β : Type v} {s : set α} {f : α → β} : inj_on f s ↔ function.injective (restrict f s) := sorry

theorem inj_on.inv_fun_on_image {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {f : α → β} [Nonempty α] (h : inj_on f s₂) (ht : s₁ ⊆ s₂) : function.inv_fun_on f s₂ '' (f '' s₁) = s₁ := sorry

theorem inj_on_preimage {α : Type u} {β : Type v} {f : α → β} {B : set (set β)} (hB : B ⊆ 𝒫 range f) : inj_on (preimage f) B :=
  fun (s : set β) (hs : s ∈ B) (t : set β) (ht : t ∈ B) (hst : f ⁻¹' s = f ⁻¹' t) =>
    iff.mp (preimage_eq_preimage' (hB hs) (hB ht)) hst

/-! ### Surjectivity on a set -/

/-- `f` is surjective from `a` to `b` if `b` is contained in the image of `a`. -/
def surj_on {α : Type u} {β : Type v} (f : α → β) (s : set α) (t : set β)  :=
  t ⊆ f '' s

theorem surj_on.subset_range {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : surj_on f s t) : t ⊆ range f :=
  subset.trans h (image_subset_range f s)

theorem surj_on_iff_exists_map_subtype {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} : surj_on f s t ↔ ∃ (t' : set β), ∃ (g : ↥s → ↥t'), t ⊆ t' ∧ function.surjective g ∧ ∀ (x : ↥s), f ↑x = ↑(g x) := sorry

theorem surj_on_empty {α : Type u} {β : Type v} (f : α → β) (s : set α) : surj_on f s ∅ :=
  empty_subset (f '' s)

theorem surj_on.comap_nonempty {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : surj_on f s t) (ht : set.nonempty t) : set.nonempty s :=
  nonempty.of_image (nonempty.mono h ht)

theorem surj_on.congr {α : Type u} {β : Type v} {s : set α} {t : set β} {f₁ : α → β} {f₂ : α → β} (h : surj_on f₁ s t) (H : eq_on f₁ f₂ s) : surj_on f₂ s t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (surj_on f₂ s t)) (surj_on.equations._eqn_1 f₂ s t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (t ⊆ f₂ '' s)) (Eq.symm (eq_on.image_eq H)))) h)

theorem eq_on.surj_on_iff {α : Type u} {β : Type v} {s : set α} {t : set β} {f₁ : α → β} {f₂ : α → β} (h : eq_on f₁ f₂ s) : surj_on f₁ s t ↔ surj_on f₂ s t :=
  { mp := fun (H : surj_on f₁ s t) => surj_on.congr H h,
    mpr := fun (H : surj_on f₂ s t) => surj_on.congr H (eq_on.symm h) }

theorem surj_on.mono {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t₁ : set β} {t₂ : set β} {f : α → β} (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : surj_on f s₁ t₂) : surj_on f s₂ t₁ :=
  subset.trans ht (subset.trans hf (image_subset f hs))

theorem surj_on.union {α : Type u} {β : Type v} {s : set α} {t₁ : set β} {t₂ : set β} {f : α → β} (h₁ : surj_on f s t₁) (h₂ : surj_on f s t₂) : surj_on f s (t₁ ∪ t₂) :=
  fun (x : β) (hx : x ∈ t₁ ∪ t₂) => or.elim hx (fun (hx : x ∈ t₁) => h₁ hx) fun (hx : x ∈ t₂) => h₂ hx

theorem surj_on.union_union {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t₁ : set β} {t₂ : set β} {f : α → β} (h₁ : surj_on f s₁ t₁) (h₂ : surj_on f s₂ t₂) : surj_on f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  surj_on.union (surj_on.mono (subset_union_left s₁ s₂) (subset.refl t₁) h₁)
    (surj_on.mono (subset_union_right s₁ s₂) (subset.refl t₂) h₂)

theorem surj_on.inter_inter {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t₁ : set β} {t₂ : set β} {f : α → β} (h₁ : surj_on f s₁ t₁) (h₂ : surj_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) : surj_on f (s₁ ∩ s₂) (t₁ ∩ t₂) := sorry

theorem surj_on.inter {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t : set β} {f : α → β} (h₁ : surj_on f s₁ t) (h₂ : surj_on f s₂ t) (h : inj_on f (s₁ ∪ s₂)) : surj_on f (s₁ ∩ s₂) t :=
  inter_self t ▸ surj_on.inter_inter h₁ h₂ h

theorem surj_on.comp {α : Type u} {β : Type v} {γ : Type w} {s : set α} {t : set β} {p : set γ} {f : α → β} {g : β → γ} (hg : surj_on g t p) (hf : surj_on f s t) : surj_on (g ∘ f) s p :=
  subset.trans hg (subset.trans (image_subset g hf) (image_comp g f s ▸ subset.refl (g ∘ f '' s)))

theorem surjective_iff_surj_on_univ {α : Type u} {β : Type v} {f : α → β} : function.surjective f ↔ surj_on f univ univ := sorry

theorem surj_on_iff_surjective {α : Type u} {β : Type v} {s : set α} {f : α → β} : surj_on f s univ ↔ function.surjective (restrict f s) := sorry

theorem surj_on.image_eq_of_maps_to {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h₁ : surj_on f s t) (h₂ : maps_to f s t) : f '' s = t :=
  eq_of_subset_of_subset (maps_to.image_subset h₂) h₁

theorem surj_on.maps_to_compl {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : surj_on f s t) (h' : function.injective f) : maps_to f (sᶜ) (tᶜ) := sorry

theorem maps_to.surj_on_compl {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : maps_to f s t) (h' : function.surjective f) : surj_on f (sᶜ) (tᶜ) :=
  iff.mpr (function.surjective.forall h')
    fun (x : α) (ht : f x ∈ (tᶜ)) => mem_image_of_mem f fun (hs : x ∈ s) => ht (h hs)

/-! ### Bijectivity -/

/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
def bij_on {α : Type u} {β : Type v} (f : α → β) (s : set α) (t : set β)  :=
  maps_to f s t ∧ inj_on f s ∧ surj_on f s t

theorem bij_on.maps_to {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : bij_on f s t) : maps_to f s t :=
  and.left h

theorem bij_on.inj_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : bij_on f s t) : inj_on f s :=
  and.left (and.right h)

theorem bij_on.surj_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : bij_on f s t) : surj_on f s t :=
  and.right (and.right h)

theorem bij_on.mk {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h₁ : maps_to f s t) (h₂ : inj_on f s) (h₃ : surj_on f s t) : bij_on f s t :=
  { left := h₁, right := { left := h₂, right := h₃ } }

theorem bij_on_empty {α : Type u} {β : Type v} (f : α → β) : bij_on f ∅ ∅ :=
  { left := maps_to_empty f ∅, right := { left := inj_on_empty f, right := surj_on_empty f ∅ } }

theorem bij_on.inter {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t₁ : set β} {t₂ : set β} {f : α → β} (h₁ : bij_on f s₁ t₁) (h₂ : bij_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) : bij_on f (s₁ ∩ s₂) (t₁ ∩ t₂) := sorry

theorem bij_on.union {α : Type u} {β : Type v} {s₁ : set α} {s₂ : set α} {t₁ : set β} {t₂ : set β} {f : α → β} (h₁ : bij_on f s₁ t₁) (h₂ : bij_on f s₂ t₂) (h : inj_on f (s₁ ∪ s₂)) : bij_on f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  { left := maps_to.union_union (bij_on.maps_to h₁) (bij_on.maps_to h₂),
    right := { left := h, right := surj_on.union_union (bij_on.surj_on h₁) (bij_on.surj_on h₂) } }

theorem bij_on.subset_range {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : bij_on f s t) : t ⊆ range f :=
  surj_on.subset_range (bij_on.surj_on h)

theorem inj_on.bij_on_image {α : Type u} {β : Type v} {s : set α} {f : α → β} (h : inj_on f s) : bij_on f s (f '' s) :=
  bij_on.mk (maps_to_image f s) h (subset.refl (f '' s))

theorem bij_on.congr {α : Type u} {β : Type v} {s : set α} {t : set β} {f₁ : α → β} {f₂ : α → β} (h₁ : bij_on f₁ s t) (h : eq_on f₁ f₂ s) : bij_on f₂ s t :=
  bij_on.mk (maps_to.congr (bij_on.maps_to h₁) h) (inj_on.congr (bij_on.inj_on h₁) h)
    (surj_on.congr (bij_on.surj_on h₁) h)

theorem eq_on.bij_on_iff {α : Type u} {β : Type v} {s : set α} {t : set β} {f₁ : α → β} {f₂ : α → β} (H : eq_on f₁ f₂ s) : bij_on f₁ s t ↔ bij_on f₂ s t :=
  { mp := fun (h : bij_on f₁ s t) => bij_on.congr h H, mpr := fun (h : bij_on f₂ s t) => bij_on.congr h (eq_on.symm H) }

theorem bij_on.image_eq {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : bij_on f s t) : f '' s = t :=
  surj_on.image_eq_of_maps_to (bij_on.surj_on h) (bij_on.maps_to h)

theorem bij_on.comp {α : Type u} {β : Type v} {γ : Type w} {s : set α} {t : set β} {p : set γ} {f : α → β} {g : β → γ} (hg : bij_on g t p) (hf : bij_on f s t) : bij_on (g ∘ f) s p :=
  bij_on.mk (maps_to.comp (bij_on.maps_to hg) (bij_on.maps_to hf))
    (inj_on.comp (bij_on.inj_on hg) (bij_on.inj_on hf) (bij_on.maps_to hf))
    (surj_on.comp (bij_on.surj_on hg) (bij_on.surj_on hf))

theorem bij_on.bijective {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (h : bij_on f s t) : function.bijective (cod_restrict (restrict f s) t fun (x : ↥s) => bij_on.maps_to h (subtype.val_prop x)) := sorry

theorem bijective_iff_bij_on_univ {α : Type u} {β : Type v} {f : α → β} : function.bijective f ↔ bij_on f univ univ := sorry

theorem bij_on.compl {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} (hst : bij_on f s t) (hf : function.bijective f) : bij_on f (sᶜ) (tᶜ) := sorry

/-! ### left inverse -/

/-- `g` is a left inverse to `f` on `a` means that `g (f x) = x` for all `x ∈ a`. -/
def left_inv_on {α : Type u} {β : Type v} (f' : β → α) (f : α → β) (s : set α)  :=
  ∀ {x : α}, x ∈ s → f' (f x) = x

theorem left_inv_on.eq_on {α : Type u} {β : Type v} {s : set α} {f : α → β} {f' : β → α} (h : left_inv_on f' f s) : eq_on (f' ∘ f) id s :=
  h

theorem left_inv_on.eq {α : Type u} {β : Type v} {s : set α} {f : α → β} {f' : β → α} (h : left_inv_on f' f s) {x : α} (hx : x ∈ s) : f' (f x) = x :=
  h hx

theorem left_inv_on.congr_left {α : Type u} {β : Type v} {s : set α} {f : α → β} {f₁' : β → α} {f₂' : β → α} (h₁ : left_inv_on f₁' f s) {t : set β} (h₁' : maps_to f s t) (heq : eq_on f₁' f₂' t) : left_inv_on f₂' f s :=
  fun (x : α) (hx : x ∈ s) => heq (h₁' hx) ▸ h₁ hx

theorem left_inv_on.congr_right {α : Type u} {β : Type v} {s : set α} {f₁ : α → β} {f₂ : α → β} {f₁' : β → α} (h₁ : left_inv_on f₁' f₁ s) (heq : eq_on f₁ f₂ s) : left_inv_on f₁' f₂ s :=
  fun (x : α) (hx : x ∈ s) => heq hx ▸ h₁ hx

theorem left_inv_on.inj_on {α : Type u} {β : Type v} {s : set α} {f : α → β} {f₁' : β → α} (h : left_inv_on f₁' f s) : inj_on f s :=
  fun (x₁ : α) (h₁ : x₁ ∈ s) (x₂ : α) (h₂ : x₂ ∈ s) (heq : f x₁ = f x₂) =>
    Eq.trans (Eq.trans (Eq.symm (h h₁)) (congr_arg f₁' heq)) (h h₂)

theorem left_inv_on.surj_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} {f' : β → α} (h : left_inv_on f' f s) (hf : maps_to f s t) : surj_on f' t s :=
  fun (x : α) (hx : x ∈ s) => Exists.intro (f x) { left := hf hx, right := h hx }

theorem left_inv_on.maps_to {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} {f' : β → α} (h : left_inv_on f' f s) (hf : surj_on f s t) : maps_to f' t s := sorry

theorem left_inv_on.comp {α : Type u} {β : Type v} {γ : Type w} {s : set α} {t : set β} {f : α → β} {g : β → γ} {f' : β → α} {g' : γ → β} (hf' : left_inv_on f' f s) (hg' : left_inv_on g' g t) (hf : maps_to f s t) : left_inv_on (f' ∘ g') (g ∘ f) s :=
  fun (x : α) (h : x ∈ s) => Eq.trans (congr_arg f' (hg' (hf h))) (hf' h)

theorem left_inv_on.mono {α : Type u} {β : Type v} {s : set α} {s₁ : set α} {f : α → β} {f' : β → α} (hf : left_inv_on f' f s) (ht : s₁ ⊆ s) : left_inv_on f' f s₁ :=
  fun (x : α) (hx : x ∈ s₁) => hf (ht hx)

/-! ### Right inverse -/

/-- `g` is a right inverse to `f` on `b` if `f (g x) = x` for all `x ∈ b`. -/
def right_inv_on {α : Type u} {β : Type v} (f' : β → α) (f : α → β) (t : set β)  :=
  left_inv_on f f' t

theorem right_inv_on.eq_on {α : Type u} {β : Type v} {t : set β} {f : α → β} {f' : β → α} (h : right_inv_on f' f t) : eq_on (f ∘ f') id t :=
  h

theorem right_inv_on.eq {α : Type u} {β : Type v} {t : set β} {f : α → β} {f' : β → α} (h : right_inv_on f' f t) {y : β} (hy : y ∈ t) : f (f' y) = y :=
  h hy

theorem right_inv_on.congr_left {α : Type u} {β : Type v} {t : set β} {f : α → β} {f₁' : β → α} {f₂' : β → α} (h₁ : right_inv_on f₁' f t) (heq : eq_on f₁' f₂' t) : right_inv_on f₂' f t :=
  left_inv_on.congr_right h₁ heq

theorem right_inv_on.congr_right {α : Type u} {β : Type v} {s : set α} {t : set β} {f₁ : α → β} {f₂ : α → β} {f' : β → α} (h₁ : right_inv_on f' f₁ t) (hg : maps_to f' t s) (heq : eq_on f₁ f₂ s) : right_inv_on f' f₂ t :=
  left_inv_on.congr_left h₁ hg heq

theorem right_inv_on.surj_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} {f' : β → α} (hf : right_inv_on f' f t) (hf' : maps_to f' t s) : surj_on f s t :=
  left_inv_on.surj_on hf hf'

theorem right_inv_on.maps_to {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} {f' : β → α} (h : right_inv_on f' f t) (hf : surj_on f' t s) : maps_to f s t :=
  left_inv_on.maps_to h hf

theorem right_inv_on.comp {α : Type u} {β : Type v} {γ : Type w} {t : set β} {p : set γ} {f : α → β} {g : β → γ} {f' : β → α} {g' : γ → β} (hf : right_inv_on f' f t) (hg : right_inv_on g' g p) (g'pt : maps_to g' p t) : right_inv_on (f' ∘ g') (g ∘ f) p :=
  left_inv_on.comp hg hf g'pt

theorem right_inv_on.mono {α : Type u} {β : Type v} {t : set β} {t₁ : set β} {f : α → β} {f' : β → α} (hf : right_inv_on f' f t) (ht : t₁ ⊆ t) : right_inv_on f' f t₁ :=
  left_inv_on.mono hf ht

theorem inj_on.right_inv_on_of_left_inv_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} {f' : β → α} (hf : inj_on f s) (hf' : left_inv_on f f' t) (h₁ : maps_to f s t) (h₂ : maps_to f' t s) : right_inv_on f f' s :=
  fun (x : α) (h : x ∈ s) => hf (h₂ (h₁ h)) h (hf' (h₁ h))

theorem eq_on_of_left_inv_on_of_right_inv_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} {f₁' : β → α} {f₂' : β → α} (h₁ : left_inv_on f₁' f s) (h₂ : right_inv_on f₂' f t) (h : maps_to f₂' t s) : eq_on f₁' f₂' t :=
  fun (y : β) (hy : y ∈ t) => Eq.trans (congr_arg f₁' (Eq.symm (h₂ hy))) (h₁ (h hy))

theorem surj_on.left_inv_on_of_right_inv_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} {f' : β → α} (hf : surj_on f s t) (hf' : right_inv_on f f' s) : left_inv_on f f' t := sorry

/-! ### Two-side inverses -/

/-- `g` is an inverse to `f` viewed as a map from `a` to `b` -/
def inv_on {α : Type u} {β : Type v} (g : β → α) (f : α → β) (s : set α) (t : set β)  :=
  left_inv_on g f s ∧ right_inv_on g f t

theorem inv_on.symm {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} {f' : β → α} (h : inv_on f' f s t) : inv_on f f' t s :=
  { left := and.right h, right := and.left h }

theorem inv_on.mono {α : Type u} {β : Type v} {s : set α} {s₁ : set α} {t : set β} {t₁ : set β} {f : α → β} {f' : β → α} (h : inv_on f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : inv_on f' f s₁ t₁ :=
  { left := left_inv_on.mono (and.left h) hs, right := right_inv_on.mono (and.right h) ht }

/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `maps_to` arguments can be deduced from
`surj_on` statements using `left_inv_on.maps_to` and `right_inv_on.maps_to`. -/
theorem inv_on.bij_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} {f' : β → α} (h : inv_on f' f s t) (hf : maps_to f s t) (hf' : maps_to f' t s) : bij_on f s t :=
  { left := hf, right := { left := left_inv_on.inj_on (and.left h), right := right_inv_on.surj_on (and.right h) hf' } }

/-! ### `inv_fun_on` is a left/right inverse -/

theorem inj_on.left_inv_on_inv_fun_on {α : Type u} {β : Type v} {s : set α} {f : α → β} [Nonempty α] (h : inj_on f s) : left_inv_on (function.inv_fun_on f s) f s :=
  fun (x : α) (hx : x ∈ s) => function.inv_fun_on_eq' h hx

theorem surj_on.right_inv_on_inv_fun_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} [Nonempty α] (h : surj_on f s t) : right_inv_on (function.inv_fun_on f s) f t :=
  fun (y : β) (hy : y ∈ t) => function.inv_fun_on_eq (iff.mp mem_image_iff_bex (h hy))

theorem bij_on.inv_on_inv_fun_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} [Nonempty α] (h : bij_on f s t) : inv_on (function.inv_fun_on f s) f s t :=
  { left := inj_on.left_inv_on_inv_fun_on (bij_on.inj_on h), right := surj_on.right_inv_on_inv_fun_on (bij_on.surj_on h) }

theorem surj_on.inv_on_inv_fun_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} [Nonempty α] (h : surj_on f s t) : inv_on (function.inv_fun_on f s) f (function.inv_fun_on f s '' t) t := sorry

theorem surj_on.maps_to_inv_fun_on {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} [Nonempty α] (h : surj_on f s t) : maps_to (function.inv_fun_on f s) t s :=
  fun (y : β) (hy : y ∈ t) => iff.mpr mem_preimage (function.inv_fun_on_mem (iff.mp mem_image_iff_bex (h hy)))

theorem surj_on.bij_on_subset {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} [Nonempty α] (h : surj_on f s t) : bij_on f (function.inv_fun_on f s '' t) t := sorry

theorem surj_on_iff_exists_bij_on_subset {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} : surj_on f s t ↔ ∃ (s' : set α), ∃ (H : s' ⊆ s), bij_on f s' t := sorry

theorem preimage_inv_fun_of_mem {α : Type u} {β : Type v} [n : Nonempty α] {f : α → β} (hf : function.injective f) {s : set α} (h : Classical.choice n ∈ s) : function.inv_fun f ⁻¹' s = f '' s ∪ (range fᶜ) := sorry

theorem preimage_inv_fun_of_not_mem {α : Type u} {β : Type v} [n : Nonempty α] {f : α → β} (hf : function.injective f) {s : set α} (h : ¬Classical.choice n ∈ s) : function.inv_fun f ⁻¹' s = f '' s := sorry

end set


/-! ### Piecewise defined function -/

namespace set


@[simp] theorem piecewise_empty {α : Type u} {δ : α → Sort y} (f : (i : α) → δ i) (g : (i : α) → δ i) [(i : α) → Decidable (i ∈ ∅)] : piecewise ∅ f g = g := sorry

@[simp] theorem piecewise_univ {α : Type u} {δ : α → Sort y} (f : (i : α) → δ i) (g : (i : α) → δ i) [(i : α) → Decidable (i ∈ univ)] : piecewise univ f g = f := sorry

@[simp] theorem piecewise_insert_self {α : Type u} {δ : α → Sort y} (s : set α) (f : (i : α) → δ i) (g : (i : α) → δ i) {j : α} [(i : α) → Decidable (i ∈ insert j s)] : piecewise (insert j s) f g j = f j := sorry

protected instance compl.decidable_mem {α : Type u} (s : set α) [(j : α) → Decidable (j ∈ s)] (j : α) : Decidable (j ∈ (sᶜ)) :=
  not.decidable

theorem piecewise_insert {α : Type u} {δ : α → Sort y} (s : set α) (f : (i : α) → δ i) (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] [DecidableEq α] (j : α) [(i : α) → Decidable (i ∈ insert j s)] : piecewise (insert j s) f g = function.update (piecewise s f g) j (f j) := sorry

@[simp] theorem piecewise_eq_of_mem {α : Type u} {δ : α → Sort y} (s : set α) (f : (i : α) → δ i) (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] {i : α} (hi : i ∈ s) : piecewise s f g i = f i := sorry

@[simp] theorem piecewise_eq_of_not_mem {α : Type u} {δ : α → Sort y} (s : set α) (f : (i : α) → δ i) (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] {i : α} (hi : ¬i ∈ s) : piecewise s f g i = g i := sorry

theorem piecewise_singleton {α : Type u} {β : Type v} (x : α) [(y : α) → Decidable (y ∈ singleton x)] [DecidableEq α] (f : α → β) (g : α → β) : piecewise (singleton x) f g = function.update g x (f x) := sorry

theorem piecewise_eq_on {α : Type u} {β : Type v} (s : set α) [(j : α) → Decidable (j ∈ s)] (f : α → β) (g : α → β) : eq_on (piecewise s f g) f s :=
  fun (_x : α) => piecewise_eq_of_mem s f g

theorem piecewise_eq_on_compl {α : Type u} {β : Type v} (s : set α) [(j : α) → Decidable (j ∈ s)] (f : α → β) (g : α → β) : eq_on (piecewise s f g) g (sᶜ) :=
  fun (_x : α) => piecewise_eq_of_not_mem s f g

@[simp] theorem piecewise_insert_of_ne {α : Type u} {δ : α → Sort y} (s : set α) (f : (i : α) → δ i) (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] {i : α} {j : α} (h : i ≠ j) [(i : α) → Decidable (i ∈ insert j s)] : piecewise (insert j s) f g i = piecewise s f g i := sorry

@[simp] theorem piecewise_compl {α : Type u} {δ : α → Sort y} (s : set α) (f : (i : α) → δ i) (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] [(i : α) → Decidable (i ∈ (sᶜ))] : piecewise (sᶜ) f g = piecewise s g f := sorry

@[simp] theorem piecewise_range_comp {α : Type u} {β : Type v} {ι : Sort u_1} (f : ι → α) [(j : α) → Decidable (j ∈ range f)] (g₁ : α → β) (g₂ : α → β) : piecewise (range f) g₁ g₂ ∘ f = g₁ ∘ f :=
  comp_eq_of_eq_on_range (piecewise_eq_on (range f) g₁ g₂)

theorem piecewise_preimage {α : Type u} {β : Type v} (s : set α) [(j : α) → Decidable (j ∈ s)] (f : α → β) (g : α → β) (t : set β) : piecewise s f g ⁻¹' t = s ∩ f ⁻¹' t ∪ sᶜ ∩ g ⁻¹' t := sorry

theorem comp_piecewise {α : Type u} {β : Type v} {γ : Type w} (s : set α) [(j : α) → Decidable (j ∈ s)] (h : β → γ) {f : α → β} {g : α → β} {x : α} : h (piecewise s f g x) = piecewise s (h ∘ f) (h ∘ g) x := sorry

@[simp] theorem piecewise_same {α : Type u} {δ : α → Sort y} (s : set α) (f : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] : piecewise s f f = f := sorry

theorem range_piecewise {α : Type u} {β : Type v} (s : set α) [(j : α) → Decidable (j ∈ s)] (f : α → β) (g : α → β) : range (piecewise s f g) = f '' s ∪ g '' (sᶜ) := sorry

theorem piecewise_mem_pi {α : Type u} (s : set α) [(j : α) → Decidable (j ∈ s)] {δ : α → Type u_1} {t : set α} {t' : (i : α) → set (δ i)} {f : (i : α) → δ i} {g : (i : α) → δ i} (hf : f ∈ pi t t') (hg : g ∈ pi t t') : piecewise s f g ∈ pi t t' := sorry

end set


theorem strict_mono_incr_on.inj_on {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} {s : set α} (H : strict_mono_incr_on f s) : set.inj_on f s :=
  fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) (hxy : f x = f y) =>
    (fun (this : ordering.compares ordering.eq x y) => this) (iff.mp (strict_mono_incr_on.compares H hx hy) hxy)

theorem strict_mono_decr_on.inj_on {α : Type u} {β : Type v} [linear_order α] [preorder β] {f : α → β} {s : set α} (H : strict_mono_decr_on f s) : set.inj_on f s :=
  strict_mono_incr_on.inj_on H

theorem strict_mono_incr_on.comp {α : Type u} {β : Type v} {γ : Type w} [preorder α] [preorder β] [preorder γ] {g : β → γ} {f : α → β} {s : set α} {t : set β} (hg : strict_mono_incr_on g t) (hf : strict_mono_incr_on f s) (hs : set.maps_to f s t) : strict_mono_incr_on (g ∘ f) s :=
  fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) (hxy : x < y) => hg (hs hx) (hs hy) (hf hx hy hxy)

theorem strict_mono.comp_strict_mono_incr_on {α : Type u} {β : Type v} {γ : Type w} [preorder α] [preorder β] [preorder γ] {g : β → γ} {f : α → β} {s : set α} (hg : strict_mono g) (hf : strict_mono_incr_on f s) : strict_mono_incr_on (g ∘ f) s :=
  fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) (hxy : x < y) => hg (hf hx hy hxy)

theorem strict_mono.cod_restrict {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} (hf : strict_mono f) {s : set β} (hs : ∀ (x : α), f x ∈ s) : strict_mono (set.cod_restrict f s hs) :=
  hf

namespace function


theorem injective.comp_inj_on {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ} {s : set α} (hg : injective g) (hf : set.inj_on f s) : set.inj_on (g ∘ f) s :=
  set.inj_on.comp (injective.inj_on hg set.univ) hf (set.maps_to_univ f s)

theorem surjective.surj_on {α : Type u} {β : Type v} {f : α → β} (hf : surjective f) (s : set β) : set.surj_on f set.univ s :=
  set.surj_on.mono (set.subset.refl set.univ) (set.subset_univ s) (iff.mp set.surjective_iff_surj_on_univ hf)

namespace semiconj


theorem maps_to_image {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {f : α → β} {s : set α} {t : set α} (h : semiconj f fa fb) (ha : set.maps_to fa s t) : set.maps_to fb (f '' s) (f '' t) := sorry

theorem maps_to_range {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {f : α → β} (h : semiconj f fa fb) : set.maps_to fb (set.range f) (set.range f) := sorry

theorem surj_on_image {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {f : α → β} {s : set α} {t : set α} (h : semiconj f fa fb) (ha : set.surj_on fa s t) : set.surj_on fb (f '' s) (f '' t) := sorry

theorem surj_on_range {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {f : α → β} (h : semiconj f fa fb) (ha : surjective fa) : set.surj_on fb (set.range f) (set.range f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (set.surj_on fb (set.range f) (set.range f))) (Eq.symm set.image_univ)))
    (surj_on_image h (surjective.surj_on ha set.univ))

theorem inj_on_image {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {f : α → β} {s : set α} (h : semiconj f fa fb) (ha : set.inj_on fa s) (hf : set.inj_on f (fa '' s)) : set.inj_on fb (f '' s) := sorry

theorem inj_on_range {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {f : α → β} (h : semiconj f fa fb) (ha : injective fa) (hf : set.inj_on f (set.range fa)) : set.inj_on fb (set.range f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (set.inj_on fb (set.range f))) (Eq.symm set.image_univ)))
    (inj_on_image h (injective.inj_on ha set.univ)
      (eq.mp (Eq._oldrec (Eq.refl (set.inj_on f (set.range fa))) (Eq.symm set.image_univ)) hf))

theorem bij_on_image {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {f : α → β} {s : set α} {t : set α} (h : semiconj f fa fb) (ha : set.bij_on fa s t) (hf : set.inj_on f t) : set.bij_on fb (f '' s) (f '' t) := sorry

theorem bij_on_range {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {f : α → β} (h : semiconj f fa fb) (ha : bijective fa) (hf : injective f) : set.bij_on fb (set.range f) (set.range f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (set.bij_on fb (set.range f) (set.range f))) (Eq.symm set.image_univ)))
    (bij_on_image h (iff.mp set.bijective_iff_bij_on_univ ha) (injective.inj_on hf set.univ))

theorem maps_to_preimage {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {f : α → β} (h : semiconj f fa fb) {s : set β} {t : set β} (hb : set.maps_to fb s t) : set.maps_to fa (f ⁻¹' s) (f ⁻¹' t) := sorry

theorem inj_on_preimage {α : Type u} {β : Type v} {fa : α → α} {fb : β → β} {f : α → β} (h : semiconj f fa fb) {s : set β} (hb : set.inj_on fb s) (hf : set.inj_on f (f ⁻¹' s)) : set.inj_on fa (f ⁻¹' s) := sorry

end semiconj


theorem update_comp_eq_of_not_mem_range' {α : Sort u_1} {β : Type u_2} {γ : β → Sort u_3} [DecidableEq β] (g : (b : β) → γ b) {f : α → β} {i : β} (a : γ i) (h : ¬i ∈ set.range f) : (fun (j : α) => update g i a (f j)) = fun (j : α) => g (f j) :=
  update_comp_eq_of_forall_ne' g a fun (x : α) (hx : f x = i) => h (Exists.intro x hx)

/-- Non-dependent version of `function.update_comp_eq_of_not_mem_range'` -/
theorem update_comp_eq_of_not_mem_range {α : Sort u_1} {β : Type u_2} {γ : Sort u_3} [DecidableEq β] (g : β → γ) {f : α → β} {i : β} (a : γ) (h : ¬i ∈ set.range f) : update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_not_mem_range' g a h

