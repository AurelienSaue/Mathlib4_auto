/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.monoidal.functorial
import Mathlib.category_theory.monoidal.functor_category
import Mathlib.category_theory.limits.limits
import PostPort

universes u v 

namespace Mathlib

/-!
# `lim : (J ⥤ C) ⥤ C` is lax monoidal when `C` is a monoidal category.

When `C` is a monoidal category, the functorial association `F ↦ limit F` is lax monoidal,
i.e. there are morphisms
* `lim_lax.ε : (𝟙_ C) → limit (𝟙_ (J ⥤ C))`
* `lim_lax.μ : limit F ⊗ limit G ⟶ limit (F ⊗ G)`
satisfying the laws of a lax monoidal functor.
-/

namespace category_theory.limits


protected instance limit_functorial {J : Type v} [small_category J] {C : Type u} [category C] [has_limits C] : functorial fun (F : J ⥤ C) => limit F :=
  functorial.mk (functor.map lim)

@[simp] theorem limit_functorial_map {J : Type v} [small_category J] {C : Type u} [category C] [has_limits C] {F : J ⥤ C} {G : J ⥤ C} (α : F ⟶ G) : map (fun (F : J ⥤ C) => limit F) α = functor.map lim α :=
  rfl

protected instance limit_lax_monoidal {J : Type v} [small_category J] {C : Type u} [category C] [has_limits C] [monoidal_category C] : lax_monoidal fun (F : J ⥤ C) => limit F :=
  lax_monoidal.mk (limit.lift (functor.obj (functor.const J) 𝟙_) (cone.mk 𝟙_ (nat_trans.mk fun (j : J) => 𝟙)))
    fun (F G : J ⥤ C) =>
      limit.lift (F ⊗ G) (cone.mk (limit F ⊗ limit G) (nat_trans.mk fun (j : J) => limit.π F j ⊗ limit.π G j))

/-- The limit functor `F ↦ limit F` bundled as a lax monoidal functor. -/
def lim_lax {J : Type v} [small_category J] {C : Type u} [category C] [has_limits C] [monoidal_category C] : lax_monoidal_functor (J ⥤ C) C :=
  lax_monoidal_functor.of fun (F : J ⥤ C) => limit F

@[simp] theorem lim_lax_obj {J : Type v} [small_category J] {C : Type u} [category C] [has_limits C] [monoidal_category C] (F : J ⥤ C) : functor.obj (lax_monoidal_functor.to_functor lim_lax) F = limit F :=
  rfl

theorem lim_lax_obj' {J : Type v} [small_category J] {C : Type u} [category C] [has_limits C] [monoidal_category C] (F : J ⥤ C) : functor.obj (lax_monoidal_functor.to_functor lim_lax) F = functor.obj lim F :=
  rfl

@[simp] theorem lim_lax_map {J : Type v} [small_category J] {C : Type u} [category C] [has_limits C] [monoidal_category C] {F : J ⥤ C} {G : J ⥤ C} (α : F ⟶ G) : functor.map (lax_monoidal_functor.to_functor lim_lax) α = functor.map lim α :=
  rfl

@[simp] theorem lim_lax_ε {J : Type v} [small_category J] {C : Type u} [category C] [has_limits C] [monoidal_category C] : lax_monoidal_functor.ε lim_lax =
  limit.lift (functor.obj (functor.const J) 𝟙_) (cone.mk 𝟙_ (nat_trans.mk fun (j : J) => 𝟙)) :=
  rfl

@[simp] theorem lim_lax_μ {J : Type v} [small_category J] {C : Type u} [category C] [has_limits C] [monoidal_category C] (F : J ⥤ C) (G : J ⥤ C) : lax_monoidal_functor.μ lim_lax F G =
  limit.lift (F ⊗ G) (cone.mk (limit F ⊗ limit G) (nat_trans.mk fun (j : J) => limit.π F j ⊗ limit.π G j)) :=
  rfl

