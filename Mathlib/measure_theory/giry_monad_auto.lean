/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.measure_theory.integration
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# The Giry monad

Let X be a measurable space. The collection of all measures on X again
forms a measurable space. This construction forms a monad on
measurable spaces and measurable functions, called the Giry monad.

Note that most sources use the term "Giry monad" for the restriction
to *probability* measures. Here we include all measures on X.

See also `measure_theory/category/Meas.lean`, containing an upgrade of the type-level
monad to an honest monad of the functor `Measure : Meas ⥤ Meas`.

## References

* <https://ncatlab.org/nlab/show/Giry+monad>

## Tags

giry monad
-/

namespace measure_theory


namespace measure


/-- Measurability structure on `measure`: Measures are measurable w.r.t. all projections -/
protected instance measurable_space {α : Type u_1} [measurable_space α] : measurable_space (measure α) :=
  supr
    fun (s : set α) =>
      supr fun (hs : is_measurable s) => measurable_space.comap (fun (μ : measure α) => coe_fn μ s) (borel ennreal)

theorem measurable_coe {α : Type u_1} [measurable_space α] {s : set α} (hs : is_measurable s) : measurable fun (μ : measure α) => coe_fn μ s :=
  measurable.of_comap_le
    (le_supr_of_le s
      (le_supr_of_le hs (le_refl (measurable_space.comap (fun (μ : measure α) => coe_fn μ s) ennreal.measurable_space))))

theorem measurable_of_measurable_coe {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] (f : β → measure α) (h : ∀ (s : set α), is_measurable s → measurable fun (b : β) => coe_fn (f b) s) : measurable f := sorry

theorem measurable_measure {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {μ : α → measure β} : measurable μ ↔ ∀ (s : set β), is_measurable s → measurable fun (b : α) => coe_fn (μ b) s :=
  { mp := fun (hμ : measurable μ) (s : set β) (hs : is_measurable s) => measurable.comp (measurable_coe hs) hμ,
    mpr := measurable_of_measurable_coe μ }

theorem measurable_map {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] (f : α → β) (hf : measurable f) : measurable fun (μ : measure α) => coe_fn (map f) μ := sorry

theorem measurable_dirac {α : Type u_1} [measurable_space α] : measurable dirac := sorry

theorem measurable_lintegral {α : Type u_1} [measurable_space α] {f : α → ennreal} (hf : measurable f) : measurable fun (μ : measure α) => lintegral μ fun (x : α) => f x := sorry

/-- Monadic join on `measure` in the category of measurable spaces and measurable
functions. -/
def join {α : Type u_1} [measurable_space α] (m : measure (measure α)) : measure α :=
  of_measurable (fun (s : set α) (hs : is_measurable s) => lintegral m fun (μ : measure α) => coe_fn μ s) sorry sorry

@[simp] theorem join_apply {α : Type u_1} [measurable_space α] {m : measure (measure α)} {s : set α} : is_measurable s → coe_fn (join m) s = lintegral m fun (μ : measure α) => coe_fn μ s :=
  of_measurable_apply

theorem measurable_join {α : Type u_1} [measurable_space α] : measurable join := sorry

theorem lintegral_join {α : Type u_1} [measurable_space α] {m : measure (measure α)} {f : α → ennreal} (hf : measurable f) : (lintegral (join m) fun (x : α) => f x) = lintegral m fun (μ : measure α) => lintegral μ fun (x : α) => f x := sorry

/-- Monadic bind on `measure`, only works in the category of measurable spaces and measurable
functions. When the function `f` is not measurable the result is not well defined. -/
def bind {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] (m : measure α) (f : α → measure β) : measure β :=
  join (coe_fn (map f) m)

@[simp] theorem bind_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {m : measure α} {f : α → measure β} {s : set β} (hs : is_measurable s) (hf : measurable f) : coe_fn (bind m f) s = lintegral m fun (a : α) => coe_fn (f a) s := sorry

theorem measurable_bind' {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {g : α → measure β} (hg : measurable g) : measurable fun (m : measure α) => bind m g :=
  measurable.comp measurable_join (measurable_map g hg)

theorem lintegral_bind {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {m : measure α} {μ : α → measure β} {f : β → ennreal} (hμ : measurable μ) (hf : measurable f) : (lintegral (bind m μ) fun (x : β) => f x) = lintegral m fun (a : α) => lintegral (μ a) fun (x : β) => f x :=
  Eq.trans (lintegral_join hf) (lintegral_map (measurable_lintegral hf) hμ)

theorem bind_bind {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {γ : Type u_3} [measurable_space γ] {m : measure α} {f : α → measure β} {g : β → measure γ} (hf : measurable f) (hg : measurable g) : bind (bind m f) g = bind m fun (a : α) => bind (f a) g := sorry

theorem bind_dirac {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {f : α → measure β} (hf : measurable f) (a : α) : bind (dirac a) f = f a := sorry

theorem dirac_bind {α : Type u_1} [measurable_space α] {m : measure α} : bind m dirac = m := sorry

theorem join_eq_bind {α : Type u_1} [measurable_space α] (μ : measure (measure α)) : join μ = bind μ id :=
  eq.mpr (id (Eq._oldrec (Eq.refl (join μ = bind μ id)) (bind.equations._eqn_1 μ id)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (join μ = join (coe_fn (map id) μ))) map_id)) (Eq.refl (join μ)))

theorem join_map_map {α : Type u_1} {β : Type u_2} [measurable_space α] [measurable_space β] {f : α → β} (hf : measurable f) (μ : measure (measure α)) : join (coe_fn (map ⇑(map f)) μ) = coe_fn (map f) (join μ) := sorry

theorem join_map_join {α : Type u_1} [measurable_space α] (μ : measure (measure (measure α))) : join (coe_fn (map join) μ) = join (join μ) := sorry

theorem join_map_dirac {α : Type u_1} [measurable_space α] (μ : measure α) : join (coe_fn (map dirac) μ) = μ :=
  dirac_bind

theorem join_dirac {α : Type u_1} [measurable_space α] (μ : measure α) : join (dirac μ) = μ :=
  Eq.trans (join_eq_bind (dirac μ)) (bind_dirac measurable_id μ)

