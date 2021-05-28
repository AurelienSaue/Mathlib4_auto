/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.pointwise
import Mathlib.order.filter.basic
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Pointwise operations on filters.

The pointwise operations on filters have nice properties, such as
  • `map m (f₁ * f₂) = map m f₁ * map m f₂`
  • `𝓝 x * 𝓝 y = 𝓝 (x * y)`

-/

namespace filter


protected instance has_one {α : Type u} [HasOne α] : HasOne (filter α) :=
  { one := principal 1 }

@[simp] theorem mem_zero {α : Type u} [HasZero α] (s : set α) : s ∈ 0 ↔ 0 ∈ s := sorry

protected instance has_mul {α : Type u} [monoid α] : Mul (filter α) :=
  { mul :=
      fun (f g : filter α) =>
        mk (set_of fun (s : set α) => ∃ (t₁ : set α), ∃ (t₂ : set α), t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ * t₂ ⊆ s) sorry sorry sorry }

theorem mem_add {α : Type u} [add_monoid α] {f : filter α} {g : filter α} {s : set α} : s ∈ f + g ↔ ∃ (t₁ : set α), ∃ (t₂ : set α), t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ + t₂ ⊆ s :=
  iff.rfl

theorem mul_mem_mul {α : Type u} [monoid α] {f : filter α} {g : filter α} {s : set α} {t : set α} (hs : s ∈ f) (ht : t ∈ g) : s * t ∈ f * g :=
  Exists.intro s (Exists.intro t { left := hs, right := { left := ht, right := set.subset.refl (s * t) } })

protected theorem mul_le_mul {α : Type u} [monoid α] {f₁ : filter α} {f₂ : filter α} {g₁ : filter α} {g₂ : filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁ * g₁ ≤ f₂ * g₂ := sorry

theorem ne_bot.add {α : Type u} [add_monoid α] {f : filter α} {g : filter α} : ne_bot f → ne_bot g → ne_bot (f + g) := sorry

protected theorem add_assoc {α : Type u} [add_monoid α] (f : filter α) (g : filter α) (h : filter α) : f + g + h = f + (g + h) := sorry

protected theorem one_mul {α : Type u} [monoid α] (f : filter α) : 1 * f = f := sorry

protected theorem add_zero {α : Type u} [add_monoid α] (f : filter α) : f + 0 = f := sorry

protected instance monoid {α : Type u} [monoid α] : monoid (filter α) :=
  monoid.mk Mul.mul filter.mul_assoc 1 filter.one_mul filter.mul_one

protected theorem map_add {α : Type u} {β : Type v} [add_monoid α] [add_monoid β] (m : α → β) [is_add_hom m] {f₁ : filter α} {f₂ : filter α} : map m (f₁ + f₂) = map m f₁ + map m f₂ := sorry

protected theorem map_one {α : Type u} {β : Type v} [monoid α] [monoid β] (m : α → β) [is_monoid_hom m] : map m 1 = 1 := sorry

-- TODO: prove similar statements when `m` is group homomorphism etc.

theorem Mathlib.map.is_add_monoid_hom {α : Type u} {β : Type v} [add_monoid α] [add_monoid β] (m : α → β) [is_add_monoid_hom m] : is_add_monoid_hom (map m) :=
  is_add_monoid_hom.mk (filter.map_zero m)

-- The other direction does not hold in general.

theorem comap_mul_comap_le {α : Type u} {β : Type v} [monoid α] [monoid β] (m : α → β) [is_mul_hom m] {f₁ : filter β} {f₂ : filter β} : comap m f₁ * comap m f₂ ≤ comap m (f₁ * f₂) := sorry

theorem tendsto.mul_mul {α : Type u} {β : Type v} [monoid α] [monoid β] {m : α → β} [is_mul_hom m] {f₁ : filter α} {g₁ : filter α} {f₂ : filter β} {g₂ : filter β} : tendsto m f₁ f₂ → tendsto m g₁ g₂ → tendsto m (f₁ * g₁) (f₂ * g₂) :=
  fun (hf : tendsto m f₁ f₂) (hg : tendsto m g₁ g₂) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (tendsto m (f₁ * g₁) (f₂ * g₂))) (tendsto.equations._eqn_1 m (f₁ * g₁) (f₂ * g₂))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (map m (f₁ * g₁) ≤ f₂ * g₂)) (filter.map_mul m))) (filter.mul_le_mul hf hg))

